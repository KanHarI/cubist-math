import "./fresh-build.mjs";
import {naturalSort, numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { cubicalMathTree } from "../web/cubical-notation.mjs";
import naturalSource from "../web/translator/nat-source.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { testModulePath } from "../tools/inline-errors.mjs";
import { checkTestModule } from "./check-program.mjs";
const module = await createCubical();
// The Cubist cases are cubist-tests/program_*.cubist, whose comments state
// each refusal and what each print shows (tests/cubist-tests.test.mjs); here,
// what the program's inspection, export and switches do with them, and the
// programs that need a reader of their own.
const cases = (t, name, options = {}) => checkTestModule(t, `program_${name}`, { module, options });

// A reader with no library, such as the first test's, still loads `nat`.
test("nat's bundled source is the library's nat module", async () => {
  assert.equal(naturalSource, await readFile(new URL("../library/nat.cubist", import.meta.url), "utf8"),
    "Regenerate web/translator/nat-source.mjs from library/nat.cubist.");
});

test("a universe-generic definition is one kernel definition", async t => {
  const { program } = await cases(t, "generic_once");
  assert.deepEqual([...program.kernel.definitions.keys()].filter(name => name.startsWith("program_generic_once__identity")),
    ["program_generic_once__identity"]);
});

test("the browser program checks Euclid from source and exports a replayable native inspection", async t => {
  const readSource = sourceReader();
  const program = new CubicalProgram(module, readSource); t.after(() => program.dispose());
  const result = await program.check(await readSource("euclid"), "euclid");
  assert.equal(result.complete, true);
  assert.equal(result.backend, "cubical");
  assert.ok(result.instructionCount > 0);
  assert.ok(result.links.some(x => x.name === "prime_divisor_exists"));
  assert.equal(program.inspect("euclid__euclid").type.name, "euclid__InfinitelyManyPrimes");
  const local = result.links.find(x => x.role === "local" && program.inspect(x.binding).context.length);
  assert.ok(local);
  assert.ok(program.inspect(local.binding).context.length);
  const payload = program.export("euclid__euclid", "type");
  const replay = new CubicalProgram(module, async name => payload.sources[name]); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  assert.deepEqual(replay.inspect(payload.binding).type, program.inspect(payload.binding).type);
});

test("module shadowing cannot retarget earlier checked native definitions", async t => {
  const { program } = await cases(t, "shadowing");
  assert.equal(program.inspect("program_shadow_first__remembered").expression.name, "program_shadow_first__value");
  assert.equal(program.inspect("program_shadow_first__value", { normalize: true }).expression.tag, "Con");
  assert.equal(program.inspect("program_shadow_second__value", { normalize: true }).expression.tag, "App");
});

test("unsupported foundations and invalid proofs remain explicitly unverified", async t => {
  const program = new CubicalProgram(module, async () => { throw new Error("Source unavailable"); }); t.after(() => program.dispose());
  const result = await program.check("import nat; import missing; use nat; def wrong : 0 = 1 { exact refl(0); } def dependent := wrong; def fine := 0;", "example");
  assert.equal(result.complete, false);
  assert.deepEqual(result.outputs.map(d => d.verified), [false, false, true]);
  assert.ok(result.gaps.some(g => g.module === "missing"));
  assert.throws(() => program.inspect("example__wrong"));
  assert.equal(program.kernel.definitions.has("example__wrong"), false);
});

test("native notation preserves named references and dependent path families", () => {
  assert.deepEqual(cubicalMathTree({ tag: "DefRef", name: "m__F" }, { m__F: { name: "F" } }),
    { kind: "Name", name: "F", binding: "m__F" });
  const family = { tag: "PApp", path: { tag: "Var", name: "p" }, arg: [["i:1"]] };
  const tree = cubicalMathTree({ tag: "Path", dim: "i", family, left: { tag: "Var", name: "a" }, right: { tag: "Var", name: "b" } });
  assert.equal(tree.fn.name, "PathP");
});

test("native path interiors retain their interval context in the inspector and replay", async t => {
  const readSource = sourceReader();
  const program = new CubicalProgram(module, readSource); t.after(() => program.dispose());
  const source = await readSource("cubical_paths");
  const result = await program.check(source, "cubical_paths");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const local = result.links.find(link => program.views.get(link.binding)?.dimensions.size);
  assert.ok(local);
  const view = program.inspect(local.binding);
  assert.equal(view.dimensions.length, 1);
  const payload = program.export(local.binding);
  const replay = new CubicalProgram(module, async name => payload.sources[name]); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  assert.deepEqual(replay.inspect(payload.binding).dimensions, view.dimensions);
});

test("logical assumptions remain explicit, minimal, and inspectable after native closure", async t => {
  const { result, program } = await cases(t, "assumptions");
  assert.equal(result.outputs.find(d => d.name === "introduction").axioms.length, 2);
  const view = program.inspect("program_assumptions__introduction");
  assert.equal(view.context.length, 2);
  assert.ok(view.context.some(entry => entry.label === "Truncate"));
  const assumption = program.inspect(view.axioms[0]);
  assert.equal(assumption.expression.tag, "Var");
  const payload = program.export("program_assumptions__introduction");
  const replay = new CubicalProgram(module, async name => payload.sources[name]); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  assert.deepEqual(replay.inspect(payload.binding).context, view.context);
});

test("`with unfolding` checks its body as a definition of its own, which replays", async t => {
  const { program } = await cases(t, "unfolding_hints");
  assert.ok(program.checker.definitionViews.has("program_unfolding_hints__unfolding_1"));
  const view = program.inspect("program_unfolding_hints__hinted");
  const payload = program.export("program_unfolding_hints__hinted");
  const replay = new CubicalProgram(module, async name => payload.sources[name]); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  assert.deepEqual(replay.inspect(payload.binding).type, view.type);
});

test("native progress identifies the active declaration before it is checked", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  const progress = [];
  await program.check("def first := tt; def second := tt;", "progress", event => progress.push(event));
  const checking = progress.filter(p => p.phase !== "loading");
  assert.ok(checking.every(p => p.total === 2));
  assert.deepEqual(checking.map(p => [p.current, p.phase, p.completed]), [
    ["progress.first", "checking", 0], ["progress.first", "checked", 1],
    ["progress.second", "checking", 1], ["progress.second", "checked", 2],
  ]);
});


test("progress totals count a shared import once, including universe-generic definitions", async t => {
  const sources = {
    common: "def generic(U < UU0, A : U, a : A) := a; def shared := tt;",
    first: "import common; def fromFirst := shared;",
    second: "import common; def fromSecond := shared;",
  };
  const reads = [];
  const program = new CubicalProgram(module, async name => { reads.push(name); return sources[name]; });
  t.after(() => program.dispose());
  const progress = [];
  const result = await program.check("import first; import second; def final := fromFirst;", "root", p => progress.push(p));
  assert.equal(result.declarationCount, 5);
  assert.equal(reads.filter(name => name === "common").length, 1);
  assert.ok(progress.filter(p => p.phase !== "loading").every(p => p.total === 5));
  assert.equal(progress.at(-1).completed, 5);
});

test("progress totals count the declarations a theory expands to, so that none exceeds its total", async t => {
  const sources = { hlevels: await readFile(new URL("../library/hlevels.cubist", import.meta.url), "utf8") };
  const program = new CubicalProgram(module, async name => sources[name] ?? sourceReader()(name));
  t.after(() => program.dispose());
  const progress = [];
  const result = await program.check("import hlevels; theory Pointed(U < UU0) { M : set U; point : M; } def after := tt;", "root", p => progress.push(p));
  const counted = progress.filter(p => p.phase !== "loading");
  // The page shows "N of total" only while the total is at least N.
  assert.ok(counted.every(p => p.completed <= p.total), JSON.stringify(counted.find(p => p.completed > p.total)));
  assert.equal(progress.at(-1).completed, result.declarationCount);
  assert.equal(progress.at(-1).total, result.declarationCount);
  assert.ok(result.outputs.filter(output => output.name.startsWith("Pointed")).length > 2);
});
test("progress totals count the declarations an initial or free model expands to", async t => {
  const program = new CubicalProgram(module, sourceReader());
  t.after(() => program.dispose());
  const progress = [];
  const result = await program.check("import hlevels; import algebra; initial N : Monoid(U0); free W(A : U0) : Monoid(U0) on A; def after := tt;",
    "root", p => progress.push(p));
  const counted = progress.filter(p => p.phase !== "loading");
  assert.ok(counted.every(p => p.completed <= p.total), JSON.stringify(counted.find(p => p.completed > p.total)));
  assert.deepEqual([progress.at(-1).completed, progress.at(-1).total], [result.declarationCount, result.declarationCount]);
  assert.ok(result.outputs.filter(output => output.name.startsWith("W")).length > 2);
  assert.ok(result.outputs.every(output => output.verified), JSON.stringify(result.outputs.find(output => !output.verified)));
});
test("progress totals take off the rest of a theory whose type of models fails, and end at what was checked", async t => {
  // Without hlevels, Pointed's sorts have no evidence: its type of models
  // fails, once, and the rest of its expansion is not checked. Its
  // failure is the last declaration of the source, or one is after it.
  const pointed = "theory Pointed(U < UU0) { M : set U; point : M; }";
  for (const [source, outputs] of [[pointed, [["Pointed", false]]], [`${pointed} def after := tt;`, [["Pointed", false], ["after", true]]]]) {
    const program = new CubicalProgram(module, sourceReader());
    t.after(() => program.dispose());
    const progress = [];
    const result = await program.check(source, "root", p => progress.push(p));
    assert.deepEqual(result.outputs.map(output => [output.name, output.verified]), outputs);
    const counted = progress.filter(p => p.phase !== "loading");
    assert.ok(counted.every(p => p.completed <= p.total), JSON.stringify(counted.find(p => p.completed > p.total)));
    assert.equal(result.declarationCount, outputs.length);
    assert.deepEqual([progress.at(-1).completed, progress.at(-1).total], [outputs.length, outputs.length], source);
  }
});

test("native optimization switches preserve path proofs and rejection independently", async () => {
  const name = "program_optimizations", path = testModulePath(name), source = await readFile(path, "utf8");
  for (let flags = 0; flags < 8; flags++) {
    const optimizations = { shareSyntax: !!(flags & 1), reuseChecks: !!(flags & 2), compactPaths: !!(flags & 4) };
    const program = new CubicalProgram(module, sourceReader({ path }), { optimizations });
    try {
      const result = await program.check(source, name);
      assert.deepEqual(result.outputs.map(d => d.verified), [true, true, false, false], JSON.stringify(optimizations));
      assert.deepEqual(program.kernel.optimizations, optimizations);
    } finally { program.dispose(); }
  }
});

test("calls of an imported generic definition link to the definition itself", async t => {
  for (const reuseChecks of [true, false]) {
    const { source, result, program } = await cases(t, "generic_caller", { optimizations: { reuseChecks } });
    const binding = "program_generic_identity__identity";
    const references = result.links.filter(link => link.binding === binding);
    assert.equal(references.length, 2);
    for (const link of references) {
      assert.equal(source.slice(link.start, link.end), "identity");
      const view = program.inspect(link.binding);
      assert.equal(view.type.tag, "LPi");
      assert.equal(view.symbols[link.binding].sourceModule, "program_generic_identity");
      assert.deepEqual(view.axioms, []);
    }
    for (const link of result.links)
      assert.equal(source.slice(link.start, link.end), link.name, "imported offsets must not leak into the caller");
    assert.deepEqual(program.inspect("program_generic_caller__identity1").type.domain, { tag: "U", level: 1 });
  }
});

test("an unused generic definition's locals inspect and replay under the universe binder", async t => {
  const { source, result, program } = await cases(t, "unused_generic");
  const local = result.links.find(link => link.name === "x" && source.slice(link.end, link.end + 1) === ";");
  const view = program.inspect(local.binding);
  assert.equal(view.expression.tag, "Var");
  assert.deepEqual(view.context.map(entry => entry.label), ["U", "A", "x"]);
  assert.deepEqual(view.context[0].type, { tag: "LBound", tier: 1 });
  assert.deepEqual(view.context[1].type, { tag: "U", level: { tag: "Var", name: view.context[0].name } });
  const payload = program.export(view.name);
  const replay = new CubicalProgram(module, async () => ""); t.after(() => replay.dispose());
  await replay.check(payload.source, payload.main);
  const restored = replay.inspect(payload.binding);
  assert.deepEqual(restored.expression, view.expression);
  assert.deepEqual(restored.type, view.type);
  assert.deepEqual(restored.context, view.context);
});

test("a refused generic definition cannot be inspected",async t=>{
  const {program}=await cases(t,"untyped_generic");
  assert.throws(()=>program.inspect("program_untyped_generic__generic"),
    /Untyped lambda requires an expected function type/);
});

test("every named reference in the generic group definitions is inspectable with source labels", async t => {
  const readSource = sourceReader();
  const program = new CubicalProgram(module, readSource); t.after(() => program.dispose());
  const result = await program.check(await readSource("group_universes"), "group_universes");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const references = result.links.filter(link => link.role === "local");
  assert.ok(references.length > 300);
  for (const reference of references) {
    const view = program.inspect(reference.binding);
    assert.equal(view.symbols[view.name].name, reference.name);
  }
  const view = program.inspect("group_universes__GroupAssociativeAt");
  assert.equal(view.type.tag, "LPi");
  const notation = JSON.stringify(cubicalMathTree(view.expression, view.symbols));
  for (const name of ["U", "A", "multiply", "x", "y", "z"]) assert.ok(notation.includes(`"name":"${name}"`), name);
  assert.doesNotMatch(notation, /"name":"(?:U|A|multiply|x|y|z)_?[0-9]+"/);
});

test("a declaration that fails after a failed import names the import", async t => {
  const program = new CubicalProgram(await createCubical(), async name => {
    throw new Error(`Native source is not available for ${name}.`);
  }, { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check("import nat;\nimport lists; use nat;\ndef four := append;\ndef five := 5;\ndef six : Nat {\n  exact length;\n}\n", "imports_missing");
  const reason = name => result.outputs.find(output => output.name === name).reason;
  assert.equal(reason("four"),
    "Untranslated name: append (import lists failed: Native source is not available for lists.)");
  assert.match(reason("six"), /^Untranslated name: length \(import lists failed: .*\)( at \d+:\d+)?$/);
  assert.equal(result.outputs.find(output => output.name === "five").verified, true);
});
