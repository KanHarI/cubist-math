import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkProgram, checkTestModule } from "./check-program.mjs";
import { generatedCubist, generatedDeclaration } from "../web/generated-cubist.mjs";
import { gaps } from "./fixtures/frontend-generation.mjs";

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
  assert.deepEqual(generatedCubist(program), view, "display is deterministic");
});

test("failed and blocked generated families keep their syntax and their real publication state", async t => {
  const {program} = await checkProgram(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; law bad : c = Missing; }`, {module, options});
  const view = generatedCubist(program);
  assert.match(view.source, /T:base · failed/);
  assert.match(view.source, /T:hom · blocked/);
  assert.match(view.source, /T:iso · blocked/);
  assert.match(view.source, /Missing/);
  assert.match(view.source, /def T\.Hom\.id/);
  assert.doesNotMatch(view.source, /display unavailable|· checked/);
  assert.equal(program.kernel.definitions.has("main__T"), false);
});

test("generated views distinguish imported modules and discard expansions on recheck", async t => {
  const {program} = await checkProgram(t, "import models; def kept : Unit := tt;", {module, options,
    reader: name => name === "models" ? "theory Imported(U < UU0) { M : U; }" : Promise.reject(Error(name))});
  assert.equal(generatedCubist(program).count, 0);
  assert.match(generatedCubist(program, "models").source, /def Imported\.make/);
  await program.check("def replacement : Unit := tt;", "main");
  assert.equal(generatedCubist(program).count, 0);
  assert.equal(program.generation.has("models"), false);
});

for (const name of ["theory_headers", "theory_families", "theory_variance", "theory_use", "initial_models"])
  test(`generated Cubist renders every retained declaration in ${name}`, async t => {
    const {program} = await checkTestModule(t, name, {module, options});
    const view = generatedCubist(program);
    assert.ok(view.count > 0);
    assert.doesNotMatch(view.source, /display unavailable|\u0000|undefined|generated_display_/);
    for (const group of program.generation.get(name)) for (const d of group.declarations)
      assert.ok(view.source.includes(`${d.kind} ${d.name.text}`), d.name.text);
  });

test("unsupported display syntax is explicit and leaves other declarations visible", () => {
  const declaration = {kind:"def",name:{text:"ok"},params:[],value:{kind:"name",name:"tt"}};
  const program = {main:"main",sourceAsts:new Map(),publications:new Map([["main",[{id:"T:base",state:"checked"}]]]),
    generation:new Map([["main",[{id:"T:base",declarations:[
      {...declaration,name:{text:"unknown"},value:{kind:"futureSyntax"}},declaration]}]]])};
  assert.match(generatedCubist(program).source, /unknown: display unavailable \(unsupported futureSyntax syntax\)/);
  assert.match(generatedCubist(program).source, /def ok := tt;/);
  assert.equal(generatedDeclaration(declaration), "def ok := tt;\n");
});

test("generated recursive helpers retain their calls and patterns in Cubist", async t => {
  const {program} = await checkProgram(t, gaps.G12.source, {module, options});
  const view = generatedCubist(program);
  assert.match(view.source, /def T\.iter/);
  assert.match(view.source, /def T\.twice/);
  assert.match(view.source, /T\.iter\(/);
  assert.doesNotMatch(view.source, /display unavailable|recursiveCall|\u0000/);
});

test("a large generated inductive keeps each qualified constructor name", () => {
  const constructors = Array.from({length:12}, (_, i) => ({name:{text:`N.c${i}`},params:[]}));
  const source = generatedDeclaration({kind:"inductive",name:{text:"N"},params:[],
    result:{universe:{kind:"name",name:"U0"}},constructors});
  for (const constructor of constructors) assert.ok(source.includes(`  ${constructor.name.text};`));
  assert.doesNotMatch(source, /generated_display_/);
});
