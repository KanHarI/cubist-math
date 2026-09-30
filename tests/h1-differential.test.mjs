import "./fresh-build.mjs";
import createLegacyCubical, {legacyKernelRoot} from "../tools/legacy-kernel.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { canonicalHasher } from "../tools/proof-migration.mjs";
import { execFileSync } from "node:child_process";
import { readFile, mkdtemp, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { replayInstructions } from "../tools/h1-instruction-replay.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";
import { H1Translation } from "../web/h1-translation.mjs";
import { T } from "../web/dist/cubical-runtime/core.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";

const legacyModule = await createLegacyCubical();
const module = await createCubical(), hash = canonicalHasher();
async function check(t,source,representation="declared") {
  const program = new CubicalProgram(module,sourceReader(),{experimental:["h1"],representation,collectReferences:false});
  t.after(() => program.dispose());
  const result = await program.check(source,"differential");
  return {program,result,get:name=>result.outputs.find(output=>output.name===name)};
}
const ok = (result,name) => assert.ok(result.outputs.find(output=>output.name===name)?.verified,
  `${name}: ${result.outputs.find(output=>output.name===name)?.reason}`);

test("X1 and X3: native instruction judgements, equalities and refusals replay through τ",async t=>{
  const directory = await mkdtemp(join(tmpdir(),"h1-instructions-")), file=join(directory,"fixtures.jsonl");
  t.after(()=>rm(directory,{recursive:true,force:true}));
  execFileSync(legacyKernelRoot+"build/test-instructions",["--fixtures",file],{stdio:"pipe"});
  const fixtures=(await readFile(file,"utf8")).trim().split("\n").map(line=>JSON.parse(line));
  const report=replayInstructions(module,fixtures,{sourceModule:legacyModule});
  assert.deepEqual(report.failures,[]);
  // Pinned evidence counts: update the record when native fixtures change.
  assert.equal(report.replayed,202); assert.equal(report.equalities,70);
  assert.equal(report.refused,42); assert.equal(report.unequal,1);
  assert.deepEqual(report.refusals,{replace:2,lookup:1,lambda:1,extend:3,step:4,comp:1,systemTube:2,
    systemOverlap:3,system:1,pushout:1,pushRight:1,pushLeft:1,iota:1,hcomp:1,trans:1,
    glueBase:1,gluePiece:1,glue:1,glueTermBase:1,glueTerm:1,unglue:1,sup:2,wElim:1,
    apply:2,define:1,lift:1,universeEntry:2,universeTerm:1,level:1,levelApplyTerm:1});
  for(const kind of ["NatRec","WRec","PushPath","Comp","HComp","Trans"]) assert.ok(report.kinds[kind],kind);
  for(const reason of report.refusalReasons) assert.equal(reason.declared.kind,reason.native.kind);
  const refusal=fixtures.find(fixture=>fixture.operation === "glueBase");
  const wrongKind=replayInstructions(module,[{...refusal,nativeError:{...refusal.nativeError,kind:1}}],{sourceModule:legacyModule});
  assert.match(wrongKind.failures[0]?.reason,/no longer matches its recorded reason/);
  const wrongReason=replayInstructions(module,[{...refusal,nativeError:{...refusal.nativeError,expected:"unrelated refusal"}}],{sourceModule:legacyModule});
  assert.match(wrongReason.failures[0]?.reason,/Refusal diagnostic changed/);
});

// X1/X2: point formation and elimination. Translation introduces applications
// of first-class eliminators, so the image needs administrative Beta/Eta.
test("X1 and X2: natural and sum formation, constructors and eliminators replay through τ",async t=>{
  const {program,result} = await check(t,`import primes;
def plus(U < UU0, A, B : U) : U := A or B;
def left_value : Nat or Unit := left(2);
def right_value : Nat or Unit := right(tt);
def select(x : Nat or Unit) : Nat := match x return Nat { left n => n; right u => 0; };
def result : select(left_value) = 2 { rfl; }
def sum(n : Nat) := induction n as k return Nat { zero => 0; succ r => succ(r); };
def computation : sum(3) = 3 { rfl; }
`);
  for(const name of ["plus","left_value","right_value","select","result","sum","computation"])ok(result,name);
  const target=program.translation;
  for(const name of ["left_value","right_value","select","sum","computation"]) {
    const binding=`differential__${name}`, native=program.kernel.definition(program.kernel.definitions.get(binding));
    const declared=target.kernel.definition(target.kernel.definitions.get(binding));
    const nativeNormal=program.checker.verify(program.checker.syntax.decode(native.value)).normal;
    const imageNormal=target.checker.verify(target.checker.syntax.decode(declared.value)).normal;
    const mapped=target.map(nativeNormal);
    assert.equal(hash(target.checker.verify(mapped).normal),hash(imageNormal),name);
    if(name === "select") assert.notEqual(hash(mapped),hash(imageNormal),"X2's literal alpha criterion misses a new Eta redex");
  }
});

// X6: one declared instance used at several finite universes.
test("X6: generic calls preserve a native term used at two finite universes",async t=>{
  const {result} = await check(t,`
def sum_id(U < UU0, A : U, x : A or A) : A or A := x;
def small : Nat or Nat := left(0);
def higher : Nat or Nat := sum_id(U1, Nat, small);
def nat_id(U < UU0, n : Nat) : Nat := n;
def at_two : Nat := nat_id(U2, 1);
`);
  for(const name of ["sum_id","small","higher","nat_id","at_two"])ok(result,name);
});

// X7/X8: keep tier-1 formers, but reject their mixed calls at finite instances.
test("X7 and X8: a tier-1 sum remains native and its mixed-tier call is rejected",async t=>{
  const source=`def big_sum(A, B : UU0) : UU0 := A or B;
def big_id(A : UU0, x : A or A) : A or A := x;
def small : Nat or Nat := left(0);
def call : Nat or Nat := big_id(Nat, small);
`;
  const native=await check(t,source,"native");
  assert.ok(native.result.complete);
  const {program,result,get}=await check(t,source);
  for(const name of ["big_sum","big_id","small"])ok(result,name);
  assert.equal(get("call").verified,false);
  assert.match(get("call").reason,/τ has no checked image for differential__call/);
  assert.ok(program.translation.keptNative.has("Sum"));
  assert.equal(program.translation.kernel.definitions.has("differential__call"),false);
});

test("X6, X7 and X8: W and pushout finite instantiations and mixed-tier calls",t=>{
  const kernel=new CubicalKernel(legacyModule), source=new NativeCubicalElaborator(kernel), target=new H1Translation(legacyModule,source);
  t.after(()=>{target.dispose();kernel.dispose();});
  const A=T.variable("carrier"), UU0=T.universe({tag:"LConst",tier:1,value:0});
  const tree=a=>T.w("label",a,T.void);
  const push=a=>T.pushout(a,a,a,T.pair(T.sigma("f",T.pi("x",a,a),T.pi("x",a,a)),
    T.lam("x",a,T.variable("x")),T.lam("x",a,T.variable("x"))));
  for(const [kind,former] of [["W",tree],["Pushout",push]]) {
    const finite=former(T.nat), image=target.map(finite);
    assert.equal(image.tag,"Sort");
    for(const U of [T.universe(1),T.universe(2)]) {
      const generic=T.lam("carrier",U,T.lam("element",former(A),T.variable("element")));
      const call=T.app(T.app(generic,T.nat),T.variable(`small_${kind}`));
      const context=new Map([[`small_${kind}`,finite]]), imageContext=new Map([[`small_${kind}`,image]]);
      source.check(call,finite,context);
      target.checker.check(target.map(call,context),image,imageContext);
    }
    const large=T.lam("carrier",UU0,T.lam("element",former(A),T.variable("element")));
    const imageLarge=target.map(large);
    assert.equal(imageLarge.body.domain.tag,kind);
    target.checker.infer(imageLarge);
    const call=T.app(T.app(large,T.nat),T.variable(`mixed_${kind}`));
    const context=new Map([[`mixed_${kind}`,finite]]);
    source.check(call,finite,context);
    assert.throws(()=>target.checker.check(target.map(call,context),image,new Map([[`mixed_${kind}`,image]])),/mismatch|convert/i);
  }
});

test("X8: the migration verifier rejects the mixed-tier declaration by name",async()=>{
  const tree=a=>`W(${a}, fun (label : ${a}) => Void)`;
  const push=a=>`Pushout(${a}, ${a}, ${a}, fun (x : ${a}) => x, fun (x : ${a}) => x)`;
  for(const [former,value] of [[a=>`${a} or ${a}`,"left(0)"],
    [push,`push_left(${push("Nat")}, 0)`]]) {
    const source=`def big_id(A : UU0, x : ${former("A")}) : ${former("A")} := x;
def small : ${former("Nat")} := ${value};
def call : ${former("Nat")} := big_id(Nat, small);`;
    const [native]=await verifyMigration({modules:["tier_fixture"],readOriginal:async name=>name==="tier_fixture"?source:sourceReader()(name),readEdited:async()=>source});
    assert.deepEqual(native.failures,[]);
    const [report]=await verifyMigration({modules:["tier_fixture"],readOriginal:async name=>name==="tier_fixture"?source:sourceReader()(name),readEdited:async()=>source,
      experimental:["h1"],representation:"declared"});
    assert.ok(report.failures.some(failure=>failure.name==="call" && /τ has no checked image/.test(failure.reason)),JSON.stringify(report));
    assert.equal(report.changes.length,2,"the callable definition and small value both have images");
  }
});

test("X4: canonicity and evaluate results are checked in the declared kernel",async t=>{
  const source=await readFile(new URL("../docs/examples/h1/winding.cubist",import.meta.url),"utf8");
  const native=await check(t,source,"native"), declared=await check(t,source);
  assert.ok(declared.result.complete,JSON.stringify(declared.result.gaps));
  assert.deepEqual(declared.result.evaluations,native.result.evaluations);
  assert.equal(declared.program.translation.evaluations.length,3);
  for(const output of declared.result.outputs) assert.deepEqual(output.axioms,[]);
});

test("X2 and X5: coverage records both phases and distinguishes literal alpha from normalized comparisons",async t=>{
  const directory=await mkdtemp(join(tmpdir(),"h1-cost-"));
  t.after(()=>rm(directory,{recursive:true,force:true}));
  const reports=[];
  for(const representation of ["native","declared"]) {
    const file=join(directory,`${representation}.json`);
    execFileSync(process.execPath,["tools/instruction-coverage.mjs","--modules=primes","--select=^primes__add$",
      `--representation=${representation}`,`--report=${file}`,...(representation === "declared" ? ["--normal-forms"] : [])],{stdio:"pipe"});
    reports.push(JSON.parse(await readFile(file,"utf8")));
  }
  for(const report of reports) {
    assert.ok(report.success); assert.equal(report.derived,1);
    assert.equal(typeof report.environment.revision,"string");
    assert.ok(report.environment.cpu); assert.equal(report.budgets.limitMs,5000);
    assert.ok(report.work.instructionSteps>0); assert.ok(report.memory.arenaNodes>0);
  }
  assert.ok(reports[1].checked.sourceWork.instructionSteps>0);
  assert.equal(reports[0].checked.verified,reports[1].checked.verified);
  assert.equal(reports[1].differential.strictAlphaSatisfied,true);
  assert.equal(reports[1].differential.exactAlpha,1);
  assert.equal(reports[1].differential.renormalizedImages,0);
});
