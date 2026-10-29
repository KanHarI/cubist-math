import "./fresh-build.mjs";
import {naturalSort, numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { fileURLToPath } from "node:url";
import { archiveReader, sourceReader } from "../tools/module-sources.mjs";
import { foldedInspection } from "../web/cubical-inspection.mjs";
import { cubicalMathTree } from "../web/cubical-notation.mjs";
import { boundedSyntaxJson } from "../web/cubical-json.mjs";
import { simplifyTypeApplications } from "../web/cubical-reduction.mjs";
import { checkTestModule } from "./check-program.mjs";

const module = await createCubical();
const archiveSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const variable = name => ({ tag: "Var", name });
// Programs whose links and views are the test are
// cubist-tests/inspection_*.cubist (tests/cubist-tests.test.mjs checks them).
const cases = (t, name) => checkTestModule(t, `inspection_${name}`, { module });
const unat = naturalSort;

test("declared type occurrences link to their imported and local source declarations", async t => {
  const { program, result } = await cases(t, "declared_types");
  for (const [name, binding] of [["UNat", "unat__UNat"], ["W", "w__W"], ["N", "inspection_declared_types__N"]]) {
    const links = result.links.filter(link => link.name === name);
    assert.equal(links.length, name === "N" ? 3 : 2, name);
    for (const link of links) {
      assert.equal(link.binding, binding);
      assert.equal(link.role, "inductive");
    }
  }
  const imported = result.imports.find(info => info.binding === "unat__UNat");
  assert.equal(imported.sourceModule, "unat");
  assert.equal(imported.sourceName, "UNat");
  assert.match(result.sources.unat.slice(imported.definitionStart), /^inductive UNat/);
  assert.deepEqual(program.signatureView("unat__UNat").constructors.map(c => c.name), ["zero", "succ"]);
});

test("shadowed UNat names retain their own local source targets", async t => {
  const { result } = await cases(t, "shadowed_nat");
  const links = result.links.filter(link => link.name === "UNat");
  assert.equal(links.length, 5);
  for (const link of links.slice(0, 3)) {
    assert.notEqual(link.binding, "unat__UNat");
    assert.notEqual(link.role, "inductive");
  }
  assert.equal(links.at(-1).binding, "inspection_shadowed_nat__UNat");
  assert.equal(links.at(-1).role, "def");
});

test("inferred induction statements simplify the motive and retain source binder names", async t => {
  const program = new CubicalProgram(module, archiveReader("finite_combinations")); t.after(() => program.dispose());
  assert.equal((await program.check(await archiveSource("finite_combinations"), "finite_combinations")).complete, true);
  const view = program.inspect("finite_combinations__linear_combination_scale");
  assert.equal(view.statement.inferred, true);
  assert.deepEqual(view.statement.parameters.map(p => p.name[0].text), ["K", "V", "a", "n", "v", "b"]);
  assert.doesNotMatch(view.typeText, /b\d+|λ k/);
  assert.match(view.typeText, /λ \(i : Fin\(n\)\)/);
  assert.equal(view.type.body.body.body.body.tag, "App"); // raw motive application remains available
  assert.equal(view.folded.type.body.body.body.body.tag, "Pi");
  const k = Object.values(view.symbols).find(symbol => symbol.local && symbol.name === "k");
  assert.ok(k);
  let conclusion = view.folded.type;
  while (conclusion.tag === "Pi") conclusion = conclusion.body;
  const tree = cubicalMathTree(conclusion, view.symbols, undefined, { dimensions: (view.dimensions ?? []).map(([name]) => name) });
  assert.equal(tree.left.args.at(-1).kind, "Lambda");
  assert.equal(tree.left.args.at(-1).name, "i");
  assert.equal(tree.left.args.at(-1).domain.fn.name, "Fin");
});

test("type simplification avoids capture, preserves definitions, and has a budget", () => {
  const term = { tag: "App", fn: { tag: "Lam", name: "x", domain: unat,
    body: { tag: "Lam", name: "y", domain: unat, body: variable("x") } }, arg: variable("y") };
  const result = simplifyTypeApplications(term);
  assert.equal(result.tag, "Lam");
  assert.notEqual(result.name, "y");
  assert.equal(result.body.name, "y");
  assert.deepEqual(simplifyTypeApplications({ tag: "DefRef", name: "Named" }), { tag: "DefRef", name: "Named" });
  assert.equal(simplifyTypeApplications(term, 0), term);
});

test("Euclid locals retain checked syntax, source aliases, and navigable assumptions", async t => {
  const path = fileURLToPath(new URL("../library/euclid.cubist", import.meta.url));
  const program = new CubicalProgram(module, sourceReader({ path })); t.after(() => program.dispose());
  const source = await readFile(path, "utf8"), result = await program.check(source, "euclid");
  assert.equal(result.complete, true);
  const link = result.links.find(link => link.name === "least");
  const view = program.inspect(link.binding);
  assert.match(view.typeText, /IsLeastDivisor\(succ\(factorial\(n\)\), p\)/);
  assert.equal(view.folded.reference.name, "least");
  assert.equal(view.context[0].label, "n");
  const natural = { tag: "DefRef", name: "nat__Nat" };
  assert.deepEqual(program.inspect(view.context[0].binding).type, natural);
  const p = view.locals.find(local => local.name === "p");
  assert.deepEqual(program.inspect(p.binding).type, natural);
  assert.equal(source.slice(view.symbols[p.binding].definitionStart).startsWith("p,"), true);
  assert.ok(JSON.stringify(view.type).includes('"Fst"'));
  assert.ok(!JSON.stringify(view.type).includes("DisplayRef"));
  assert.equal(view.locals.some(local => local.name === "least"), false);
  // Export reconstructs terms from source, never trusts the display projection.
  const payload = program.export(link.binding);
  assert.equal(JSON.stringify(payload).includes("DisplayRef"), false);
  assert.equal(program.inspect("euclid__euclid").folded.reference.name, "euclid__euclid");
});

test("aliases abbreviate exact syntax and never cross a binder or rewrite stored terms", () => {
  const term = { tag: "Fst", pair: variable("pair") };
  const typed = { tag: "App", fn: { tag: "Lam", name: "id", domain: unat, body: variable("id") }, arg: term };
  const view = { name: "other", expression: typed, type: unat, context: [{ name: "hyp", type: term }] };
  const before = structuredClone(view);
  const aliases = [{ name: "local", binding: "source_local", term }];
  const folded = foldedInspection(view, aliases);
  assert.equal(folded.expression.tag, "DisplayRef");
  assert.equal(folded.context[0].type.name, "local");
  assert.deepEqual(view, before);
  for (const expression of [
    { tag: "Lam", name: "pair", domain: unat, body: term },
    { tag: "PLam", dim: "i", family: unat, body: term },
  ]) {
    assert.equal(foldedInspection({ ...view, expression }, aliases).expression.body.tag, "Fst");
  }
  const different = { tag: "Snd", pair: variable("pair") };
  assert.equal(foldedInspection({ ...view, expression: different }, aliases).expression.tag, "Snd");
  assert.equal(foldedInspection({ ...view, name: "source_local" }, aliases).expression.tag, "Fst");
});

test("notation preserves dependency and distinguishes renamed shadowing variables", () => {
  const symbols = { outer: { name: "x", local: true }, inner: { name: "x", local: true } };
  const body = { tag: "Pair", first: variable("inner"), second: variable("outer") };
  const lambda = cubicalMathTree({ tag: "Lam", name: "inner", domain: unat, body }, symbols, undefined, { dimensions: [] });
  assert.equal(lambda.name, "x′");
  assert.equal(lambda.body.left.name, "x′");
  assert.equal(lambda.body.right.name, "x");
  assert.equal(cubicalMathTree({ tag: "Pi", name: "x", domain: unat, body: unat }, {}, undefined, { dimensions: [] }).kind, "Arrow");
  assert.equal(cubicalMathTree({ tag: "Sigma", name: "x", domain: unat, body: variable("x") }, {}, undefined, { dimensions: [] }).kind, "Sigma");
});

test("path notation and raw syntax display stay bounded on shared terms", () => {
  let shared = unat;
  for (let i = 0; i < 28; i++) shared = { tag: "App", fn: shared, arg: shared };
  const constant = { tag: "PLam", dim: "i", family: shared, body: variable("x") };
  assert.equal(cubicalMathTree(constant, {}, 1, { dimensions: [] }).fn.name, "refl");
  assert.equal(cubicalMathTree({ tag: "Path", dim: "i", family: shared,
    left: variable("x"), right: variable("x") }, {}, 1, { dimensions: [] }).kind, "Identity");
  const varying = { tag: "PApp", path: variable("p"), arg: [["i:0"]] };
  assert.equal(cubicalMathTree({ tag: "Path", dim: "i", family: varying,
    left: variable("x"), right: variable("x") }, {}, undefined, { dimensions: [] }).fn.name, "PathP");
  assert.equal(boundedSyntaxJson(shared), null);
  assert.equal(boundedSyntaxJson(unat), JSON.stringify(unat, null, 2));
  let deep = unat;
  for (let i = 0; i < 600; i++) deep = { tag: "Inl", as: { tag: "Unit" }, value: deep };
  assert.equal(boundedSyntaxJson(deep), null);
});

test("axiom labels and derived cubical helpers remain inspectable", async t => {
  const { program } = await cases(t, "axiom_labels");
  const tree = view => cubicalMathTree(view.folded.expression, view.symbols, undefined, { dimensions: (view.dimensions ?? []).map(([name]) => name) });
  // The library's excluded middle shows by its label, with no notation of
  // its own, and inspects as the assumption it is.
  const lem = tree(program.inspect("inspection_axiom_labels__excluded")).body.body.fn;
  assert.deepEqual([lem.name, lem.binding, lem.axiomNotation], ["LEM", program.checker.axioms.get("classical_axioms__LEM"), undefined]);
  assert.equal(program.inspect(lem.binding).expression.tag, "Var");
  // The archive's legacy Truncate(U, A) is written ‖A‖ until it retires
  // with the archive: its own truncation module shows it so.
  const archive = new CubicalProgram(module, archiveReader("truncation")); t.after(() => archive.dispose());
  assert.equal((await archive.check(await archiveSource("truncation"), "truncation")).complete, true);
  const truncate = tree(archive.inspect("truncation__Mere")).body.fn;
  assert.equal(truncate.axiomNotation, "truncation");
  assert.equal(truncate.truncationArgument, 1);
  assert.equal(archive.inspect(truncate.binding).expression.tag, "Var");
  const ordinary = cubicalMathTree(variable("Truncate"), { Truncate: { name: "Truncate" } }, undefined, { dimensions: [] });
  assert.equal(ordinary.axiomNotation, undefined);
});

test("a let alias preserves the original local's name and does not leak to later declarations", async t => {
  const { source, program, result } = await cases(t, "let_alias");
  const n = result.links.filter(link => link.name === "n").at(-1);
  const view = program.inspect(n.binding);
  assert.equal(view.expressionText, "n");
  assert.equal(view.context[0].label, "n");
  assert.equal(result.links.find(link => link.start === source.lastIndexOf("zero")).binding, "inspection_let_alias__zero");
});

// The first review of #184: a square's boundary showed x1 as x1_, the stem
// of its kernel name, and squares.transpose's a00 and a_0 as a00_ and a_0_.
test("a square's boundary shows its parameters by their source names", async t => {
  const { program } = await cases(t, "square_boundary");
  const boundary = binding => program.inspect(binding).boundary;
  assert.deepEqual(boundary("inspection_square_boundary__numbered"), {
    corners: { a00: "x1", a01: "x2", a10: "x1", a11: "x2" },
    edges: { left: "p", right: "p", bottom: "refl(x1)", top: "refl(x2)" } });
  assert.deepEqual(boundary("squares__transpose"), {
    corners: { a00: "a00", a01: "a10", a10: "a01", a11: "a11" },
    edges: { left: "a_0", right: "a_1", bottom: "a0_", top: "a1_" } });
  // The lambda's x is shown apart from the parameter x.
  assert.equal(boundary("inspection_square_boundary__apart").corners.a00, "f(x, fun (x1 : A) => x1)");
  assert.equal(boundary("squares__double_comp"), null);
});
