import "./fresh-build.mjs";
import {naturalSort, numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { archiveReader } from "../tools/module-sources.mjs";
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
const nat = naturalSort;

test("declared type occurrences link to their imported and local source declarations", async t => {
  const { program, result } = await cases(t, "declared_types");
  for (const [name, binding] of [["Nat", "nat__Nat"], ["W", "w__W"], ["N", "inspection_declared_types__N"]]) {
    const links = result.links.filter(link => link.name === name);
    assert.equal(links.length, name === "N" ? 3 : 2, name);
    for (const link of links) {
      assert.equal(link.binding, binding);
      assert.equal(link.role, "inductive");
    }
  }
  const imported = result.imports.find(info => info.binding === "nat__Nat");
  assert.equal(imported.sourceModule, "nat");
  assert.equal(imported.sourceName, "Nat");
  assert.match(result.sources.nat.slice(imported.definitionStart), /^inductive Nat/);
  assert.deepEqual(program.signatureView("nat__Nat").constructors.map(c => c.name), ["zero", "succ"]);
});

test("shadowed Nat names retain their own local source targets", async t => {
  const { result } = await cases(t, "shadowed_nat");
  const links = result.links.filter(link => link.name === "Nat");
  assert.equal(links.length, 5);
  for (const link of links.slice(0, 3)) {
    assert.notEqual(link.binding, "nat__Nat");
    assert.notEqual(link.role, "inductive");
  }
  assert.equal(links.at(-1).binding, "inspection_shadowed_nat__Nat");
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
  const tree = cubicalMathTree(conclusion, view.symbols);
  assert.equal(tree.left.args.at(-1).kind, "Lambda");
  assert.equal(tree.left.args.at(-1).name, "i");
  assert.equal(tree.left.args.at(-1).domain.fn.name, "Fin");
});

test("type simplification avoids capture, preserves definitions, and has a budget", () => {
  const term = { tag: "App", fn: { tag: "Lam", name: "x", domain: nat,
    body: { tag: "Lam", name: "y", domain: nat, body: variable("x") } }, arg: variable("y") };
  const result = simplifyTypeApplications(term);
  assert.equal(result.tag, "Lam");
  assert.notEqual(result.name, "y");
  assert.equal(result.body.name, "y");
  assert.deepEqual(simplifyTypeApplications({ tag: "DefRef", name: "Named" }), { tag: "DefRef", name: "Named" });
  assert.equal(simplifyTypeApplications(term, 0), term);
});

test("Euclid locals retain checked syntax, source aliases, and navigable assumptions", async t => {
  const program = new CubicalProgram(module, archiveReader("euclid")); t.after(() => program.dispose());
  const source = await archiveSource("euclid"), result = await program.check(source, "euclid");
  assert.equal(result.complete, true);
  const link = result.links.find(link => link.name === "hd");
  const view = program.inspect(link.binding);
  assert.match(view.typeText, /Divides\(succ\(succ\(i\)\), m\)/);
  assert.equal(view.folded.reference.name, "hd");
  assert.equal(view.context[0].label, "n");
  assert.equal(program.inspect(view.context[0].binding).type.tag, "Sort");
  const i = view.locals.find(local => local.name === "i");
  assert.equal(program.inspect(i.binding).type.tag, "Sort");
  assert.equal(source.slice(view.symbols[i.binding].definitionStart).startsWith("i,"), true);
  assert.ok(JSON.stringify(view.type).includes('"Fst"'));
  assert.ok(!JSON.stringify(view.type).includes("DisplayRef"));
  assert.equal(view.locals.some(local => local.name === "hd"), false);
  // Export reconstructs terms from source, never trusts the display projection.
  const payload = program.export(link.binding);
  assert.equal(JSON.stringify(payload).includes("DisplayRef"), false);
  assert.equal(program.inspect("euclid__euclid").folded.reference.name, "euclid__euclid");
});

test("aliases abbreviate exact syntax and never cross a binder or rewrite stored terms", () => {
  const term = { tag: "Fst", pair: variable("pair") };
  const typed = { tag: "App", fn: { tag: "Lam", name: "id", domain: nat, body: variable("id") }, arg: term };
  const view = { name: "other", expression: typed, type: nat, context: [{ name: "hyp", type: term }] };
  const before = structuredClone(view);
  const aliases = [{ name: "local", binding: "source_local", term }];
  const folded = foldedInspection(view, aliases);
  assert.equal(folded.expression.tag, "DisplayRef");
  assert.equal(folded.context[0].type.name, "local");
  assert.deepEqual(view, before);
  for (const expression of [
    { tag: "Lam", name: "pair", domain: nat, body: term },
    { tag: "PLam", dim: "i", family: nat, body: term },
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
  const lambda = cubicalMathTree({ tag: "Lam", name: "inner", domain: nat, body }, symbols);
  assert.equal(lambda.name, "x′");
  assert.equal(lambda.body.left.name, "x′");
  assert.equal(lambda.body.right.name, "x");
  assert.equal(cubicalMathTree({ tag: "Pi", name: "x", domain: nat, body: nat }).kind, "Arrow");
  assert.equal(cubicalMathTree({ tag: "Sigma", name: "x", domain: nat, body: variable("x") }).kind, "Sigma");
});

test("path notation and raw syntax display stay bounded on shared terms", () => {
  let shared = nat;
  for (let i = 0; i < 28; i++) shared = { tag: "App", fn: shared, arg: shared };
  const constant = { tag: "PLam", dim: "i", family: shared, body: variable("x") };
  assert.equal(cubicalMathTree(constant, {}, 1).fn.name, "refl");
  assert.equal(cubicalMathTree({ tag: "Path", dim: "i", family: shared,
    left: variable("x"), right: variable("x") }, {}, 1).kind, "Identity");
  const varying = { tag: "PApp", path: variable("p"), arg: [["i:0"]] };
  assert.equal(cubicalMathTree({ tag: "Path", dim: "i", family: varying,
    left: variable("x"), right: variable("x") }).fn.name, "PathP");
  assert.equal(boundedSyntaxJson(shared), null);
  assert.equal(boundedSyntaxJson(nat), JSON.stringify(nat, null, 2));
  let deep = nat;
  for (let i = 0; i < 600; i++) deep = { tag: "Inl", as: { tag: "Unit" }, value: deep };
  assert.equal(boundedSyntaxJson(deep), null);
});

test("axiom labels and derived cubical helpers remain inspectable", async t => {
  const { program } = await cases(t, "axiom_labels");
  const view = program.inspect("inspection_axiom_labels__Mere");
  const tree = cubicalMathTree(view.folded.expression, view.symbols);
  assert.equal(tree.body.fn.axiomNotation, "truncation");
  assert.equal(tree.body.fn.truncationArgument, 1);
  assert.equal(program.inspect(tree.body.fn.binding).expression.tag, "Var");
  const ordinary = cubicalMathTree(variable("Truncate"), { Truncate: { name: "Truncate" } });
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
