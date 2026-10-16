import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkProgram, checkTestModule } from "./check-program.mjs";
import { generatedCubist } from "../web/generated-cubist.mjs";
import { gaps } from "./frontend-generation-cases.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

const module = await createCubical();
const source = `import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M; }
initial N : T(U0);
free F(A : U0) : T(U0) on A;`;
const options = { collectGeneration: true };

test("generated Cubist shows the actual theory, initial and free declarations without changing checking", async t => {
  const {program, result} = await checkProgram(t, source, {module, options});
  const baseline = await checkProgram(t, source, {module});
  assert.deepEqual(result.gaps, []);
  assert.deepEqual(result.publications, baseline.result.publications);
  assert.equal(result.instructionCount, baseline.result.instructionCount);
  assert.deepEqual(result.outputs, baseline.result.outputs);
  assert.equal(baseline.program.generation.size, 0, "retention is opt-in");
  const before = program.kernel.work();
  const view = generatedCubist(program);
  assert.deepEqual(program.kernel.work(), before, "viewing must not run kernel instructions");
  assert.doesNotMatch(view.source, /display unavailable|\u0000|undefined|generated_display_/);
  assert.match(view.source, /def T :=\s+fun \(U < UU0\) => exists M : U\./);
  assert.match(view.source, /def T\.Hom\.compose/);
  assert.match(view.source, /def T\.Iso\.inverse/);
  assert.match(view.source, /inductive N : set U0/);
  assert.match(view.source, /N\.op\(x, y : N\)/);
  assert.match(view.source, /def N\.fold_map/);
  assert.match(view.source, /inductive F\(A : U0\) : set U0/);
  assert.match(view.source, /F\.gen\(a : A\)/);
  assert.match(view.source, /\/\/ N:initial · checked/);
  for (const link of view.links) {
    assert.equal(view.source.slice(link.start, link.end), link.name);
    assert.ok(program.symbols[link.binding] ?? program.localSymbols[link.binding], link.binding);
  }
  assert.ok(view.links.some(link => link.name === "T.Hom.id" && link.binding === "main__T.Hom.id"));
  assert.ok(view.links.some(link => link.name === "IsSet" && link.binding === "hlevels__IsSet"));
  assert.ok(view.links.some(link => link.name === "N" && link.binding === "main__N"));
  assert.deepEqual(generatedCubist(program), view, "display is deterministic");
});

test("generated inspection links distinguish a captured theory from local binders with its name", async t => {
  const {program} = await checkProgram(t, "import hlevels; theory A(U < UU0) { M : set U; c : M; }", {module, options});
  const view = generatedCubist(program);
  const start = view.source.indexOf("def A.Hom.id"), end = view.source.indexOf("def A.Hom.compose");
  const links = view.links.filter(link => link.start >= start && link.end <= end);
  const theory = links.filter(link => link.binding === "main__A");
  assert.equal(theory.length, 1, "only the captured type in (A : A(U)) links to the theory");
  assert.match(view.source.slice(theory[0].end), /^\(U\)/);
  assert.ok(links.some(link => link.binding === "main__A.Hom"));
});

test("the generated view preserves comments and unchanged code, commenting out replaced declarations in order", async t => {
  const source = `// Module documentation
import hlevels;
// Before the theory
def before : Unit := tt;
// Theory documentation
theory T(U < UU0) {
  // Carrier documentation
  M : set U; // Inline field comment
  c : M;
} // End of theory
// An unchanged function
def unchanged(x : Unit) : Unit := x;
initial N : T(U0);
free F(A : U0) : T(U0) on A;
// After the expansions
print(typeof(unchanged));
`;
  const {program} = await checkProgram(t, source, {module, options});
  const view = generatedCubist(program);
  for (const text of ["// Module documentation\nimport hlevels;", "// Before the theory\ndef before : Unit := tt;",
    "// An unchanged function\ndef unchanged(x : Unit) : Unit := x;", "// After the expansions\nprint(typeof(unchanged));"])
    assert.ok(view.source.includes(text), text);
  assert.match(view.source, /\/\/ theory T\(U < UU0\) \{\n  \/\/ Carrier documentation\n\/\/   M : set U; \/\/ Inline field comment/);
  assert.match(view.source, /\/\/ \} \/\/ End of theory\n\n\/\/ T:base · checked/);
  assert.match(view.source, /\/\/ initial N : T\(U0\);\n\n\/\/ N:initial · checked/);
  assert.match(view.source, /\/\/ free F\(A : U0\) : T\(U0\) on A;/);
  assert.doesNotMatch(view.source, /^(theory|initial|free) /m);
  for (const text of ["Carrier documentation", "Inline field comment", "End of theory"])
    assert.equal(view.source.split(text).length, 2, `${text} is kept once`);
  const order = ["def before", "// theory T", "def T :=", "def unchanged", "// initial N", "inductive N", "// free F", "inductive F", "print(typeof"]
    .map(text => view.source.indexOf(text));
  assert.ok(order.every((at, index) => at >= 0 && (!index || at > order[index - 1])));
  const unchanged = view.links.find(link => link.name === "unchanged");
  assert.equal(view.source.slice(unchanged.start, unchanged.end), "unchanged");
  assert.equal(unchanged.binding, "main__unchanged");
  const local = view.links.filter(link => link.name === "x").at(-1);
  assert.equal(view.source.slice(local.start, local.end), "x");
  assert.ok(program.views.has(local.binding), "the unchanged local keeps its checked inspector context");
});

test("failed and blocked generated families keep their syntax and their real publication state", async t => {
  const {program} = await checkProgram(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; law bad : c = tt; }`, {module, options});
  const view = generatedCubist(program);
  assert.match(view.source, /T:base · failed/);
  assert.match(view.source, /T:hom · blocked/);
  assert.match(view.source, /T:iso · blocked/);
  assert.match(view.source, /tt/);
  assert.match(view.source, /def T\.Hom\.id/);
  assert.doesNotMatch(view.source, /display unavailable|· checked/);
  assert.equal(program.kernel.definitions.has("main__T"), false);
  for (const name of ["T", "T.Hom.id"]) {
    const link = view.links.find(link => link.name === name);
    assert.ok(link, `a failed or blocked declaration ${name} remains inspectable`);
    assert.equal((program.symbols[link.binding] ?? link).verified, false);
  }
});

test("generated views distinguish imported modules and discard expansions on recheck", async t => {
  const {program} = await checkProgram(t, "import models; def kept : Unit := tt;", {module, options,
    reader: name => name === "models" ? "// Imported documentation\ntheory Imported(U < UU0) { M : U; }\ndef unchanged(x : Unit) : Unit := x;" : Promise.reject(Error(name))});
  assert.equal(generatedCubist(program).count, 0);
  assert.match(generatedCubist(program, "models").source, /def Imported\.make/);
  assert.ok(generatedCubist(program, "models").links.some(link => link.binding === "models__Imported.make"));
  const imported = generatedCubist(program, "models");
  assert.match(imported.source, /\/\/ Imported documentation\n\/\/ theory Imported/);
  assert.match(imported.source, /def unchanged\(x : Unit\) : Unit := x;/);
  assert.ok(imported.links.some(link => link.binding === "models__unchanged"));
  const local = imported.links.filter(link => link.name === "x").at(-1);
  assert.equal(imported.source.slice(local.start, local.end), "x");
  assert.ok(program.views.has(local.binding));
  await program.check("def replacement : Unit := tt;", "main");
  assert.equal(generatedCubist(program).count, 0);
  assert.match(generatedCubist(program).source, /def replacement : Unit := tt;/);
  assert.equal(program.generation.has("models"), false);
});

for (const name of ["theory_headers", "theory_families", "theory_variance", "theory_use", "initial_models"])
  test(`generated Cubist renders every retained declaration in ${name}`, async t => {
    const {program} = await checkTestModule(t, name, {module, options});
    const view = generatedCubist(program);
    assert.ok(view.count > 0);
    assert.doesNotMatch(view.source, /display unavailable|\u0000|undefined|generated_display_/);
    for (const link of view.links.filter(link => link.generated)) assert.equal(view.source.slice(link.start, link.end), link.name);
    for (const group of program.generation.get(name)) for (const d of group.declarations)
      assert.ok(view.source.includes(`${d.kind} ${d.name.text}`), d.name.text);
  });

test("generated recursive helpers retain their calls and patterns in Cubist", async t => {
  const {program} = await checkProgram(t, gaps.G12.source, {module, options});
  const view = generatedCubist(program);
  assert.match(view.source, /def T\.iter/);
  assert.match(view.source, /def T\.twice/);
  assert.match(view.source, /T\.iter\(/);
  assert.doesNotMatch(view.source, /display unavailable|recursiveCall|\u0000/);
});

test("generated proof helpers preserve blocks, local identities and imported navigation",async t=>{
  const fixture=`import nat;
inductive Edge { lo; hi; edge : lo = hi; }
theory Parent(U < UU0) { M : U;
  def step(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { rw [nat_add_zero(n)]; };
  def chain(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { calc { add(n, zero) = n by nat_add_zero(n); } };
  def local(n : Nat, x : Edge) : Nat := match x { lo => add(n, zero); hi => n; }
    obligations by { let y : add(n, zero) = n := nat_add_zero(n); exact y; };
}`;
  const read=sourceReader();
  const {program,result}=await checkProgram(t,"import fixture; theory Child(U < UU0) extends Parent {}",{module,options,
    reader:(name,...args)=>name==="fixture"?fixture:read(name,...args)});
  assert.deepEqual(result.gaps,[]);
  const before=program.kernel.work(),view=generatedCubist(program);
  assert.deepEqual(program.kernel.work(),before);
  assert.doesNotMatch(view.source,/display unavailable|undefined|\u0000/);
  assert.match(view.source,/rw \[nat_add_zero\(n\)\]/);
  assert.match(view.source,/calc \{/);
  assert.match(view.source,/let y : \(add\(n, zero\) = n\) := nat_add_zero\(n\);/);
  const links=view.links.filter(link=>link.generated&&link.name==="x"&&link.sourceModule==="fixture"&&link.definitionStart===fixture.indexOf("local(n : Nat, x")+"local(n : Nat, ".length);
  assert.ok(links.length);
  for(const link of links) {
    assert.equal(link.sourceName,"Parent");
    assert.ok(program.inspect(link.binding));
  }
  const expected=generatedCubist(program);
  for(const env of program.modules.values())env.get=()=>{throw new Error("display cannot resolve names");};
  assert.deepEqual(generatedCubist(program),expected);
});



test("generated member spellings and nested deferred slots preserve their identities",async t=>{
  const source=`import nat; import hlevels;
theory P(U < UU0) { M : set U; z0 : M; z1 : M; }
theory Q(U < UU0) { M : set U; c : M;
  def pick(S : P(U0)) : S.M := S.z1;
  def again(S : P(U0)) : S.M := S.z0;
  def nested(n, p : Nat) : Nat := match n {
    zero => p; succ(k) => match p { zero => k; succ(k) => k; };
  };
}`;
  const {program,result}=await checkProgram(t,source,{module,options});
  assert.deepEqual(result.gaps,[]);
  const view=generatedCubist(program);
  assert.doesNotMatch(view.source,/display unavailable/);
  for(const field of ["z0","z1"]) {
    const at=view.source.indexOf(`S.${field}`,view.source.indexOf("def Q.pick"));
    assert.ok(at>=0);
    assert.ok(view.links.every(link=>link.start!==at+2),"the field must not link to a parameter");
  }
  const start=view.source.indexOf("def Q.nested"),end=view.source.indexOf("// Q:hom",start);
  const uses=view.links.filter(link=>link.start>=start&&link.end<end&&/^k⟦/.test(link.name));
  assert.equal(uses.length,4,"both binders and their uses are inspectable");
  assert.equal(new Set(uses.map(link=>link.bindingId)).size,2,"the nested slots remain distinct");
  for(const id of new Set(uses.map(link=>link.bindingId))) {
    const same=uses.filter(link=>link.bindingId===id);
    assert.equal(same.length,2);assert.equal(new Set(same.map(link=>link.name)).size,1);
    assert.equal(new Set(same.map(link=>link.binding)).size,1);
  }
});

test("derived families stay with their publication owner in local and imported inheritance",async t=>{
  const fixture=`import hlevels; theory Parent(U < UU0) { M : set U; c : M; def twice(x : M) : M := x; }`;
  for(const imported of [false,true]) {
    const source=(imported?"import fixture;":fixture)+
      "\ntheory Child(U < UU0) extends Parent {}\ndef tail : Unit := tt;";
    const read=sourceReader();
    const {program,result}=await checkProgram(t,source,{module,options,reader:(name,...args)=>name==="fixture"?fixture:read(name,...args)});
    assert.deepEqual(result.gaps,[]);
    for(const name of imported?["main","fixture"]:["main"]) {
      const view=generatedCubist(program,name);
      for(const owner of name==="fixture"?["Parent"]:imported?["Child"]:["Parent","Child"])
        assert.ok(view.source.indexOf(`def ${owner}.twice`)<view.source.indexOf(`// ${owner}:hom`));
      if(name==="main")assert.ok(view.source.indexOf("def Child.twice")<view.source.indexOf("def tail"));
    }
  }
});

test("inherited checked and blocked symbols navigate to authored source without changing module ownership",async t=>{
  const fixture=`import hlevels;
theory Parent(U < UU0) {
  M : set U; c : M; op(x, y : M) : M;
  def twice(x : M) : M := op(x, op(x, c));
}`;
  const start=fixture.indexOf("twice(x"),prefix="import fixture;\n",doc="// Unrelated client documentation.\n";
  const read=sourceReader();
  for(const blocked of [false,true])for(const padding of ["", "\n".repeat(start-prefix.length-doc.length)+doc+"def client_only : Unit := tt;\n"]) {
    const source=prefix+padding+`theory Child(U < UU0) extends Parent { ${blocked?"law bad : c = tt;":""} }`;
    const {program,result}=await checkProgram(t,source,{module,options,
      reader:(name,...args)=>name==="fixture"?fixture:read(name,...args)});
    const view=generatedCubist(program),link=view.links.find(link=>link.name==="Child.twice");
    assert.ok(link);assert.equal(link.verified,!blocked);
    assert.equal(link.definitionSite.module,"fixture");assert.equal(link.definitionSite.start,start);
    assert.equal(link.definitionSite.name,"Parent");
    assert.doesNotMatch(link.description,/Unrelated client/);
    if(!blocked) {
      assert.deepEqual(result.gaps,[]);
      assert.ok(result.outputs.some(output=>output.name==="Child.twice"));
      assert.ok(result.imports.every(output=>output.name!=="Child.twice"));
    } else assert.equal(program.kernel.definitions.has("main__Child.twice"),false);
  }
});
