import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";
import { kernelOccurrence, kernelReductionActions, kernelStep } from "../web/cubical-kernel-step.mjs";
import { judgementGraph } from "../web/cubical-graph-view.mjs";
import { T, fill } from "../web/translator/core.mjs";
import { interval as I, face as F } from "../web/translator/lattice.mjs";
import { identityEquivalence } from "../web/translator/equivalence.mjs";

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
const actions = (program, state, path = []) =>
  kernelReductionActions(program.kernel, state.checked, "expression", path);

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
  assert.equal(kernelOccurrence(program.kernel, reduced.checked, "expression", [1]).kind, "Con");
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
  const graph = program.checker.driver.graph;
  assert.deepEqual(graph.judgement(result.checked.judgement).context, graph.judgement(open.checked.judgement).context);
  assert.ok(graph.judgement(result.checked.judgement).context.some(id => graph.entry(id).symbol ===
    program.kernel.node(graph.judgement(result.checked.judgement).term).payload));
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
  assert.ok(actions(program, initial).some(a => a.rule === "path"));
  const reduced = step(program, initial, "expression", [], "path");
  assert.equal(reduced.view.expression.path.name, "p");
  assert.deepEqual(reduced.view.expression.arg, [["i:1"]]);
  const graph = program.checker.driver.graph, context = graph.judgement(reduced.checked.judgement).context;
  assert.deepEqual(context, graph.judgement(initial.checked.judgement).context);
  assert.ok(context.some(id => { const e = graph.entry(id); return e.dimension && e.symbol === 63; }));
  const type = { tag: "Sigma", name: "x", domain: unit, body: unit };
  const pair = { tag: "Pair", as: type, first: point, second: point };
  const projection = check(program, { tag: "Fst", pair });
  const iota = actions(program, projection, [0]).find(a => a.rule === "iota");
  assert.match(iota.label, /at parent/);
  assert.deepEqual(iota.path, []);
  assert.equal(step(program, projection, "expression", iota.path, iota.rule).view.expression.tag, "Point");
});

test("reduction suggestions offer unit and sum elimination without performing reductions", async t => {
  const program = await fixture(t), sum = T.sum(unit, unit);
  const expressions = [
    T.unitrec(T.lam("u", unit, unit), point, point),
    ...[T.inl(sum, point), T.inr(sum, point)].map(value =>
      T.sumrec(T.lam("s", sum, unit), identity, identity, value)),
  ];
  for (const expression of expressions) {
    const state = check(program, expression), before = program.kernel.work();
    const suggestions = actions(program, state);
    const iota = suggestions.find(a => a.rule === "iota");
    assert.ok(iota);
    assert.deepEqual(program.kernel.work(), before, "suggestions perform no kernel instruction or reduction query");
    const result = step(program, state, "expression", iota.path, iota.rule);
    assert.notEqual(result.change.before, result.change.after);
    assert.ok(suggestions.some(a => a.rule === "whnf") && suggestions.some(a => a.rule === "normalize"));
  }
});

test("a refused rule or exhausted budget leaves the checked input usable without automatic retry", async t => {
  const program = await fixture(t), initial = check(program, app(identity, app(identity, point)));
  const id = initial.checked.judgement, kernel = program.kernel;
  assert.throws(() => step(program, initial, "expression", [], "delta"), /Delta needs a definition/);
  assert.throws(() => step(program, initial, "expression", [0.5], "beta"), /operand index/);
  assert.throws(() => step(program, initial, "expression", [3], "beta"), /unused operand/);
  for (const budget of [0, 10000001, NaN])
    assert.throws(() => step(program, initial, "expression", [], "beta", budget), /work budget must be an integer/);
  assert.throws(() => step(program, initial, "expression", [], "normalize", 1), error => error.kind === "budget");
  assert.equal(initial.checked.judgement, id); assert.equal(kernel.errorKind(), "none");
  assert.equal(step(program, initial, "expression", [], "normalize").view.expression.tag, "Point");
  assert.equal(step(program, initial, "expression", [], "whnf").view.expression.tag, "Point");
  assert.equal(step(program, initial, "expression", [], "beta").view.expression.tag, "App",
    "one beta instruction does not also contract the resulting redex");
});

test("cubical steps compute composition, homogeneous composition, transport, and a derived filler", async t => {
  const program = await fixture(t);
  for (const expression of [
    T.comp("i", unit, [{ face: F.top, term: point }], point),
  ]) {
    const initial = check(program, expression);
    assert.ok(actions(program, initial).some(a => a.rule === "face"));
    assert.equal(step(program, initial, "expression", [], "face").view.expression.tag, "Point");
  }
  const filler = fill("i", unit, [], point, I.variable("r"));
  const initial = check(program, filler, unit, [], [["r", 63]]);
  assert.equal(initial.checked.term.tag, "Comp");
  assert.equal(step(program, initial, "expression", [], "whnf").view.expression.tag, "Point");
  // Formal hcomp/trans are admitted for declared higher sorts, not Unit.
  const { program: higher } = await checkTestModule(t, "h1_acceptance_paths", { module });
  const circle = { tag: "Sort", signature: "h1_acceptance_paths__Circle", parameters: [], levels: [] };
  const base = { tag: "Con", sort: circle, index: 0 };
  for (const expression of [T.hcomp("i", circle, [{ face: F.top, term: base }], base), T.trans("i", circle, F.top, base)]) {
    const state = check(higher, expression, circle);
    assert.ok(actions(higher, state).some(a => a.rule === "face"));
    assert.equal(step(higher, state, "expression", [], "face").view.expression.index, 0);
  }
});

test("partial tubes and Glue systems are navigable and retain their cubical certificates", async t => {
  const program = await fixture(t), dimensions = [["i", 62], ["j", 63]];
  const face = F.join(F.endpoint("i", 0), F.endpoint("j", 1));
  const initial = check(program, T.comp("k", unit, [{ face, term: app(identity, point) }], point), unit, [], dimensions);
  const tube = kernelOccurrence(program.kernel, initial.checked, "expression", [1]);
  assert.equal(tube.kind, "Tube");
  const reduced = step(program, initial, "expression", [1, 0], "beta");
  assert.equal(kernelOccurrence(program.kernel, reduced.checked, "expression", [1, 0]).kind, "Point");
  // Checking has already separated disjunctive clauses. Split can still
  // remove a retained empty-face tube.
  const vacuous = check(program, T.comp("k", unit, [{ face: F.bottom, term: point }], point));
  assert.equal(kernelOccurrence(program.kernel, vacuous.checked, "expression", [1]).kind, "Tube");
  const tubeActions = actions(program, vacuous, [1]);
  assert.ok(tubeActions.some(a => a.rule === "split" && a.path.length === 0));
  assert.ok(!tubeActions.some(a => ["whnf", "normalize"].includes(a.rule)), "a system cell is not a standalone term");
  const split = step(program, vacuous, "expression", [], "split");
  assert.equal(kernelOccurrence(program.kernel, split.checked, "expression", []).children[1], 0);
  const graph = program.checker.driver.graph;
  assert.deepEqual(graph.judgement(split.checked.judgement).context, graph.judgement(vacuous.checked.judgement).context);

  const phi = F.endpoint("i", 0);
  const glue = T.glueType(unit, [{ face: phi, type: unit, equiv: identityEquivalence(unit) }]);
  const glued = check(program, T.glue(glue, point, [{ face: phi, term: app(identity, point) }]), glue, [], [["i", 63]]);
  assert.equal(kernelOccurrence(program.kernel, glued.checked, "expression", [0, 1]).kind, "GlueSystem");
  const piece = step(program, glued, "expression", [2, 0], "beta");
  assert.equal(kernelOccurrence(program.kernel, piece.checked, "expression", [2, 0]).kind, "Point");
  const unglued = check(program, T.unglue(glue, glued.view.expression), unit, [], [["i", 63]]);
  assert.equal(step(program, unglued, "expression", [], "whnf").view.expression.tag, "Point");
  const eta = check(program, T.glue(glue, T.unglue(glue, variable("g")),
    [{ face: phi, term: variable("g") }]), glue, [{ name: "g", type: glue }], [["i", 63]]);
  assert.ok(actions(program, eta).some(a => a.rule === "glue"));
  assert.equal(step(program, eta, "expression", [], "glue").view.expression.name, "g");
});
