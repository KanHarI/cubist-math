import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";
import { kernelOccurrence, kernelStep } from "../web/cubical-kernel-step.mjs";
import { judgementGraph } from "../web/cubical-graph-view.mjs";

const module = await createCubical();
const unit = { tag: "Unit" }, point = { tag: "Point" };
const variable = name => ({ tag: "Var", name });
const identity = { tag: "Lam", name: "x", domain: unit, body: variable("x") };
const app = (fn, arg) => ({ tag: "App", fn, arg });
async function fixture(t) {
  return (await checkTestModule(t, "reduction_demo", { module })).program;
}
function check(program, expression, type = unit, context = [], dimensions = []) {
  const view = { expression, type, context, dimensions, symbols: {} };
  return { view, checked: program.checker.checkView(expression, type,
    context.map(entry => [entry.name, entry.type]), new Map(dimensions)) };
}
const step = (program, state, side, path, rule, budget) =>
  kernelStep(program, state.view, state.checked, side, path, rule, budget);

// Host contracts for native Step (cubical_kernel.h): the retained judgement,
// occurrence path and readback matter here, not only the final mathematical value.
test("native beta changes one shared occurrence and retains its instruction derivation", async t => {
  const program = await fixture(t);
  const shared = app(identity, point), type = { tag: "Sigma", name: "a", domain: unit, body: unit };
  const initial = check(program, { tag: "Pair", as: type, first: shared, second: shared }, type);
  const first = kernelOccurrence(program.kernel, initial.checked, "expression", [1]).handle;
  assert.equal(first, kernelOccurrence(program.kernel, initial.checked, "expression", [2]).handle);
  const next = step(program, initial, "expression", [1], "beta");
  assert.equal(next.view.expression.first.tag, "Point");
  assert.equal(next.view.expression.second.tag, "App");
  assert.equal(initial.view.expression.first.tag, "App");
  const graph = program.checker.driver.graph, j = graph.judgement(next.checked.judgement);
  assert.equal(j.rule, "step"); assert.equal(j.stepRule, "beta");
  assert.deepEqual(j.position, [1]); assert.equal(j.premises[0], initial.checked.judgement);
  const listing = judgementGraph(program, next.view, next.checked,
    { driver: program.checker.driver, root: next.checked.judgement });
  assert.equal(listing.rows[listing.root - 1].highlight.rule, "beta");
});

test("delta unfolds only the selected reference, then beta uses the resulting lambda", async t => {
  const program = await fixture(t), view = program.inspect("reduction_demo__value");
  const initial = { view, checked: program.checker.checkView(view.expression, view.type,
    view.context.map(entry => [entry.name, entry.type]), new Map(view.dimensions)) };
  const before = kernelOccurrence(program.kernel, initial.checked, "expression", [1, 0]);
  assert.equal(before.kind, "DefRef");
  const unfolded = step(program, initial, "expression", [1, 0], "delta");
  assert.equal(kernelOccurrence(program.kernel, unfolded.checked, "expression", [1, 0]).kind, "Lam");
  assert.equal(program.kernel.node(before.handle).kind, "DefRef", "the registry reference is unchanged");
  const reduced = step(program, unfolded, "expression", [1], "beta");
  assert.equal(reduced.checked.judgement > unfolded.checked.judgement, true);
  assert.equal(program.checker.driver.graph.judgement(reduced.checked.judgement).premises[0], unfolded.checked.judgement);
});

test("steps preserve binders, renamed context entries, and type-side reductions", async t => {
  const program = await fixture(t);
  // Force the same printed name to need two different native context entries.
  program.checker.checkView(variable("y"), { tag: "U", level: 0 }, [["y", { tag: "U", level: 0 }]]);
  const open = check(program, app(identity, variable("y")), unit, [{ name: "y", type: unit }]);
  assert.ok(open.checked.renamings.length);
  const result = step(program, open, "expression", [], "beta");
  assert.equal(result.view.expression.name, "y");
  assert.deepEqual(result.view.context, open.view.context);
  const under = check(program, { tag: "Lam", name: "z", domain: unit, body: app(identity, variable("z")) },
    { tag: "Pi", name: "z", domain: unit, body: unit });
  const body = step(program, under, "expression", [1], "beta").view.expression;
  assert.equal(body.body.tag, "Var"); assert.equal(body.body.name, body.name);
  const type = app({ tag: "Lam", name: "A", domain: { tag: "U", level: 0 }, body: variable("A") }, unit);
  const typed = check(program, point, type);
  const changed = step(program, typed, "type", [], "beta");
  assert.equal(changed.view.type.tag, "Unit");
  assert.equal(changed.checked.expression, typed.checked.expression);
});

test("path steps retain a free interval at slot 63 and iota projects a pair", async t => {
  const program = await fixture(t);
  const pathType = { tag: "Path", dim: "j", family: unit, left: point, right: point };
  const term = { tag: "PApp", path: { tag: "PLam", dim: "j", family: unit,
    body: { tag: "PApp", path: variable("p"), arg: [["j:1"]] } }, arg: [["i:1"]] };
  const initial = check(program, term, unit, [{ name: "p", type: pathType }], [["i", 63]]);
  const reduced = step(program, initial, "expression", [], "path");
  assert.equal(reduced.view.expression.path.name, "p");
  assert.deepEqual(reduced.view.expression.arg, [["i:1"]]);
  assert.deepEqual(reduced.view.dimensions, [["i", 63]]);
  const type = { tag: "Sigma", name: "x", domain: unit, body: unit };
  const pair = { tag: "Pair", as: type, first: point, second: point };
  assert.equal(step(program, check(program, { tag: "Fst", pair }), "expression", [], "iota").view.expression.tag, "Point");
});

test("a refused rule or exhausted budget leaves the checked input usable without automatic retry", async t => {
  const program = await fixture(t), initial = check(program, app(identity, app(identity, point)));
  const id = initial.checked.judgement, kernel = program.kernel;
  assert.throws(() => step(program, initial, "expression", [], "delta"), /Delta needs a definition/);
  assert.throws(() => step(program, initial, "expression", [0.5], "beta"), /operand index/);
  assert.throws(() => step(program, initial, "expression", [3], "beta"), /unused operand/);
  assert.throws(() => step(program, initial, "expression", [], "normalize", 1), error => error.kind === "budget");
  assert.equal(initial.checked.judgement, id); assert.equal(kernel.errorKind(), "none");
  assert.equal(step(program, initial, "expression", [], "normalize").view.expression.tag, "Point");
  assert.equal(step(program, initial, "expression", [], "whnf").view.expression.tag, "Point");
  assert.equal(step(program, initial, "expression", [], "beta").view.expression.tag, "App",
    "one beta instruction does not also contract the resulting redex");
});
