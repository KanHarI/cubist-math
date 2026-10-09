import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import {DependencyAnalysis} from "../web/cubist/dependencies.mjs";
import {equationalSupport} from "../web/translator/initial-models.mjs";

const module = await createCubical();
const check = (t,source,fixtures={}) => {
  const library = sourceReader();
  return checkProgram(t,source,{module,reader:(name,importer)=>fixtures[name]??library(name,importer)});
};
const theory = (program,name) => {
  const record=[...program.checker.theories.values()].find(record=>record.name===name);
  assert.ok(record,`missing checked theory ${name}`);
  return record;
};

test("FG2: hidden law dependencies refuse transport across imported and renamed interfaces", async t => {
  const fixture=`import hlevels;
def ProofEq(U < UU0, A : U, p : A) : U := p = p;
theory P(U < UU0) { M : set U; c : M; law l : c = c;
  def proof_alias : c = c := l;
  op(p : ProofEq(U,c = c,proof_alias)) : M;
}`;
  const {program,result,get}=await check(t,`import fixture;
theory Child(U < UU0) extends P(l := law_again, op := act) {}
def usable(S : Child(U0)) : S.M := S.act(refl(S.law_again));
def missing(S : Child(U0)) := Child.Hom.id(S);
initial N : Child(U0);`,{fixture});
  assert.equal(get("usable").verified,true,JSON.stringify(result.gaps));
  assert.deepEqual(get("usable").axioms,[]);
  assert.deepEqual(result.gaps.map(g=>g.name),["missing","N"]);
  assert.equal(get("missing").code,"E817");
  for(const name of ["P","Child"]) {
    const record=theory(program,name),support=record.support.hom;
    assert.equal(support.status,"unsupported");
    assert.equal(support.dependency.category,"law");
    assert.equal(support.dependency.identity,record.fields.find(field=>field.kind==="law").identity);
    assert.ok(support.at.end>support.at.start);
    assert.equal(record.support.iso.status,"unsupported");
    assert.equal(equationalSupport(record).status,"unsupported");
    assert.ok(![...program.checker.theories.values()].some(r=>r.name===`${name}.Hom`));
  }
  const parent=theory(program,"P"),child=theory(program,"Child");
  assert.equal(child.dependencies.fields.find(field=>field.name==="law_again").originIdentity,
    parent.fields.find(field=>field.name==="l").identity);
  assert.ok(!result.outputs.some(o=>o.name.startsWith("Child.Hom")||o.name.startsWith("Child.Iso")||o.name.startsWith("N.")));
});

test("FG2: evidence and operation values cannot masquerade as fixed argument types", async t => {
  for(const [domain,category] of [["M_is_set = M_is_set","evidence"],["c = c","operation"]]) {
    const {program,result,get}=await check(t,`import hlevels;
theory T(U < UU0) { M : set U; c : M; op(p : ${domain}) : M; }
def usable(S : T(U0)) : S.M := S.c;`);
    assert.deepEqual(result.gaps,[]);
    assert.equal(get("usable").verified,true);
    const record=theory(program,"T");
    assert.equal(record.support.hom.dependency.category,category);
    assert.equal(record.support.hom.status,"unsupported");
    assert.equal(equationalSupport(record).status,"unsupported");
    assert.ok(!result.outputs.some(o=>o.name.startsWith("T.Hom")||o.name.startsWith("T.Iso")));
  }
});

test("FG2: fixed external identities and the open header remain independent of field spelling", async t => {
  const {program,result,get}=await check(t,`import fixture;
def Fixed : U0 := Nat;
theory Child(U < UU0) extends P {}
initial N : Child(U0);
def point : N := N.op(tt);
def identity(S : Child(U0)) : Child.Hom(S,S) := Child.Hom.id(S);`,{
    fixture:`import hlevels; import nat;
def Fixed : U0 := Unit;
theory P(U < UU0) { M : set U; op(x : Fixed) : M; }
theory Header(U < UU0, A : U0, a : A) { M : set U; point(x : A) : M; }`});
  assert.deepEqual(result.gaps,[]);
  for(const name of ["point","identity"])assert.deepEqual(get(name).axioms,[]);
  const record=theory(program,"Child"),support=record.support.hom;
  assert.equal(support.status,"conditional");
  const operation=support.mapping.operations.find(op=>op.name==="op");
  assert.equal(operation.inputs[0].way,"fixed");
  const external=record.dependencies.fields.find(field=>field.name==="op").typeUses.find(use=>use.name==="Fixed");
  assert.equal(external.category,"external");
  const analysis=new DependencyAnalysis(record.dependencies);
  // A resolved dependency's written label cannot redirect its identity.
  assert.equal(analysis.references({kind:"reference",binding:external.identity,spelling:"M",start:0,end:1})[0].category,"external");
  const header=theory(program,"Header").dependencies;
  const a=header.interface.find(item=>item.name==="a"),A=header.interface.find(item=>item.name==="A");
  assert.equal(a.typeUses[0].identity,A.identity);
  assert.equal(equationalSupport(record).status,"conditional");
});

test("FG2: morphism and equational strategies share facts while retaining different admissibility", async t => {
  const {program,result}=await check(t,`import hlevels;
theory T(U < UU0) { M : set U; op(f : Unit -> M) : M; }
def identity(S : T(U0)) : T.Hom(S,S) := T.Hom.id(S);
initial N : T(U0);`);
  assert.deepEqual(result.gaps.map(g=>g.name),["N"]);
  const record=theory(program,"T"),support=record.support.hom;
  assert.equal(support.status,"conditional");
  assert.equal(support.mapping.operations[0].inputs[0].way,"push");
  assert.equal(equationalSupport(record).status,"unsupported");
});

test("FG2: inherited notation is an explicit fixed dependency of retained law syntax", async t => {
  const {program,result,get}=await check(t,`import fixture;
notation shifted { numeral(n : Nat) := succ(n); }
use shifted;
theory Child(U < UU0) extends P {}
initial N : Child(U0);
def intended : N.number(zero) = N.number(zero) := N.base;`,{
    fixture:`import hlevels; import nat; use nat;
theory P(U < UU0) { M : set U; number(n : Nat) : M; law base : number(0) = number(zero); }`});
  assert.deepEqual(result.gaps,[]);
  assert.deepEqual(get("intended").axioms,[]);
  const notation=record=>record.dependencies.fields.find(field=>field.name==="base").typeUses.find(use=>use.role==="notation");
  const parent=notation(theory(program,"P")),child=notation(theory(program,"Child"));
  assert.equal(parent.category,"external");
  assert.equal(child.identity,parent.identity);
});

test("FG2: helper capture preserves named calls through a grouped dependent telescope", async t => {
  const {result,get} = await check(t,`import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x,c);
  def kk(c, d : M, p : c = c) : M := k(c);
}
def intended(S : T(U0), x : S.M) : T.kk(S, c := x, d := x, p := refl(x)) = S.op(x,S.c) { rfl; }
def captured(S : T(U0), x : S.M) : T.kk(S, c := x, d := x, p := refl(x)) = S.op(x,x) { rfl; }`);
  assert.equal(get("intended").verified,true,get("intended").reason);
  assert.deepEqual(get("intended").axioms,[]);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["captured","E606"]]);
});

test("FG2: imported and renamed inheritance transforms helper telescopes without capturing a parameter", async t => {
  const {result,get} = await check(t,`import fixture;
theory Child(U < UU0) extends P(c := d) {}
def intended(S : Child(U0), x : S.M) : Child.k(S, d := x) = S.op(x,S.d) { rfl; }
def captured(S : Child(U0), x : S.M) : Child.k(S, d := x) = S.op(x,x) { rfl; }
initial N : Child(U0);
def computation(x : N) : Child.k(N.model, d := x) = N.op(x,N.d) { rfl; }`,{
    fixture:`import hlevels;
theory P(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(d : M) : M := op(d,c);
}`});
  for(const name of ["intended","computation"]) {
    assert.equal(get(name).verified,true,get(name).reason);
    assert.deepEqual(get(name).axioms,[]);
  }
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["captured","E606"]]);
});

test("FG2: earlier recursive value calls compute through import, inheritance and a generated model", async t => {
  const {program,result,get} = await check(t,`import fixture;
theory Child(U < UU0) extends P {}
initial N : Child(U0);
def inherited(S : Child(U0)) : S.twice(zero) = S.op(S.c) { rfl; }
def generated : N.model.twice(succ(zero)) = N.op(N.op(N.c)) { rfl; }`,{
    fixture:`import hlevels; import nat;
theory P(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  def twice(n : Nat) : M := op(iter(n));
}`});
  assert.deepEqual(result.gaps,[]);
  for(const name of ["inherited","generated"])assert.deepEqual(get(name).axioms,[]);
  const record=theory(program,"Child"),analysis=new DependencyAnalysis(record.dependencies);
  const uses=analysis.dependencies({kind:"name",name:"twice",start:0,end:5});
  const iter=record.derived.find(field=>field.name==="iter");
  assert.equal(uses.find(use=>use.identity===iter.identity).category,"helper");
  const constant=uses.find(use=>use.name==="c");
  assert.equal(constant.category,"operation");
  assert.ok(constant.via.includes(iter.identity));
  assert.ok(!uses.some(use=>use.category==="unresolved"));
});

test("FG2: earlier value-call support does not permit a nonstructural self-call", async t => {
  const {result,get}=await check(t,`import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M;
  def bad(n : Nat) : M := match n { zero => c; succ(k) => bad(n); };
}
def usable(S : T(U0)) : S.M := S.c;`);
  assert.equal(get("usable").verified,true,get("usable").reason);
  assert.equal(result.gaps.length,1);
  assert.match(result.gaps[0].reason,/recurs|smaller|structur/i);
});

test("FG2: a recursive call in a later derived parameter type still receives the type-unfolding refusal", async t => {
  const source = `import hlevels; import nat;
theory P(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };
  def with_proof(n : Nat, p : iter(n) = c) : M := c;
}`;
  const {result} = await check(t,source);
  assert.equal(result.gaps.length,1);
  assert.equal(result.gaps[0].code,"E845");
  assert.equal(source.slice(result.gaps[0].start,result.gaps[0].end),"iter(n)");
});
