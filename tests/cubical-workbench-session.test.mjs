import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { WorkbenchSession } from "../web/cubical-workbench-session.mjs";
import { libraryProvenance } from "../web/module-resolution.mjs";
import { moduleListing } from "../web/module-listing.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { traceSnapshot } from "../web/cubical-workbench-trace.mjs";

const module = await createCubical();
const payload = {
  format: "thth-cubical", version: 1, main: "workbench", sources: {},
  source: "def identity(x : Unit) := x; def example := identity(tt);",
  binding: "workbench__example", side: "expression",
  // The workbench must replay source instead of trusting transferred claims.
  expression: { tag: "Void" }, type: { tag: "Void" },
};
async function fixture(t) {
  const session = new WorkbenchSession(module);
  t.after(() => session.dispose());
  return { session, initial: await session.load(payload) };
}

test("workbench replay retains checked states across edits, failures and inspection", async t => {
  const { session, initial } = await fixture(t);
  assert.equal(initial.view.expression.tag, "App");
  assert.equal(initial.view.type.tag, "Unit");
  const args = { state: initial.id, side: "expression", path: [0], rule: "delta", budget: 100000 };
  const unfolded = await session.handle("step", args);
  const edited = await session.handle("check", { state: initial.id, term: { tag: "Point" } });
  assert.equal(edited.view.expression.tag, "Point");
  assert.equal(initial.view.expression.tag, "App");
  assert.equal(session.state(initial.id).checked.judgement, initial.checked.judgement);
  const count = session.states.length;
  await assert.rejects(session.handle("inspect", { binding: "missing" }), /No checked/);
  await assert.rejects(session.handle("step", { ...args, rule: "beta" }), /Beta/);
  assert.equal(session.states.length, count, "refusals publish no state");
  await session.handle("inspect", { binding: "workbench__identity" });
  const reduced = await session.handle("step", { ...args, state: unfolded.id, path: [], rule: "beta" });
  assert.equal(reduced.view.expression.tag, "Point");
  const graph = await session.handle("graph", { state: reduced.id });
  assert.equal(graph.rows[graph.root - 1].id, reduced.checked.judgement);
  assert.equal(session.program.checker.driver.graph.judgement(reduced.checked.judgement).premises[0], unfolded.checked.judgement);
});

test("worker snapshots carry printing getters without changing program metadata", async t => {
  const { session, initial } = await fixture(t);
  const binding = "workbench__identity", info = session.program.symbols[binding];
  assert.equal(Object.getOwnPropertyDescriptor(info, "printing").enumerable, false);
  const printing = [{ literal: true, notation: null }];
  session.program.checker.notationPrinting.set(binding, printing);
  const snapshot = structuredClone(await session.handle("inspect", { binding: "workbench__example" }));
  assert.deepEqual(snapshot.view.symbols[binding].printing, printing);
  assert.equal(Object.getOwnPropertyDescriptor(info, "printing").enumerable, false);
  assert.equal(initial.view.expression.tag, "App");
});

test("occurrence navigation names definitions and remains available after a budget refusal", async t => {
  const { session, initial } = await fixture(t);
  const root = await session.handle("occurrence", { state: initial.id, side: "expression", path: [] });
  assert.equal(root.operands[0].label, "identity");
  assert.equal(root.operands[0].role, "function");
  assert.equal(root.operands[1].kind, "Point");
  await assert.rejects(session.handle("step", {
    state: initial.id, side: "expression", path: [], rule: "normalize", budget: 1,
  }), /budget exhausted/);
  const selected = await session.handle("occurrence", { state: initial.id, side: "expression", path: [0] });
  assert.equal(selected.text, "identity");
  assert.equal(selected.kind, "DefRef");
});

test("native previews handle universe operands and terms under a path binder", async t => {
  const { session, initial } = await fixture(t);
  const publish = (expression, type, context = []) => {
    const view = { ...initial.view, expression, type, context };
    return session.publish(view, session.check(view), initial.selected);
  };
  const universe = publish({ tag: "U", level: 0 }, { tag: "U", level: 1 });
  const level = session.occurrence(universe.id, "expression", [0]);
  assert.equal(level.kind, "LConst"); assert.equal(level.text, "0");
  assert.deepEqual(level.actions, [], "a level operand offers no term reductions");
  const unit = { tag: "Unit" }, point = { tag: "Point" };
  const type = { tag: "Path", dim: "j", family: unit, left: point, right: point };
  const path = publish({ tag: "PLam", dim: "i", family: unit,
    body: { tag: "PApp", path: { tag: "Var", name: "p" }, arg: [["i:1"]] } }, type,
    [{ name: "p", type }]);
  const body = session.occurrence(path.id, "expression", [1]);
  assert.equal(body.kind, "PApp"); assert.match(body.text, /at\(p,/);
});

test("subtree records expose native operands and math reductions publish checked snapshots", async t => {
  const { session, initial } = await fixture(t);
  const tree = await session.handle("subtree", { state: initial.id, side: "expression", path: [] });
  assert.equal(tree.root.kind, "App");
  assert.deepEqual(tree.children.map(node => node?.kind ?? null), ["DefRef", "Point", null, null]);
  assert.match(tree.children[0].annotation, /workbench__identity/);
  const next = await session.handle("reduce", {
    state: initial.id, side: "expression", kind: "delta", path: ["fn"],
  });
  assert.equal(next.view.expression.fn.tag, "Lam");
  assert.equal(initial.view.expression.fn.tag, "DefRef");
  assert.equal(session.program.checker.driver.graph.judgement(next.checked.judgement).kind, "typing");
});

test("unfolding exposes beta actions at both the lambda and its containing application", async t => {
  const { session, initial } = await fixture(t);
  await session.program.check("def poly(U < UU0, A : U, x : A) : A := x;", "levels");
  const term = { tag: "App", fn: { tag: "App",
    fn: { tag: "LApp", fn: { tag: "DefRef", name: "levels__poly" }, level: 0 },
    arg: { tag: "Unit" } }, arg: { tag: "Point" } };
  const polymorphic = await session.handle("check", { state: initial.id, term });
  for (const [state, path, lambda] of [[initial, [0], "Lam"], [polymorphic, [0, 0, 0], "LLam"]]) {
    const args = { state: state.id, side: "expression", path, budget: 100000 };
    const actions = session.occurrence(state.id, args.side, path).actions;
    assert.ok(actions.some(action => action.rule === "delta"));
    const unfolded = await session.handle("step", { ...args, rule: "delta" });
    const selected = session.occurrence(unfolded.id, args.side, path);
    assert.equal(selected.kind, lambda);
    const beta = selected.actions.find(action => action.rule === "beta");
    assert.equal(beta.label, "β reduce containing application");
    assert.deepEqual(beta.path, path.slice(0, -1));
    const root = session.occurrence(unfolded.id, args.side, beta.path);
    assert.equal(root.actions.find(action => action.rule === "beta").label, "β reduce application");
    const reduced = await session.handle("step", { ...args, state: unfolded.id, ...beta });
    assert.deepEqual(reduced.change.path, beta.path);
    assert.notEqual(reduced.change.before, reduced.change.after);
    assert.ok(!session.occurrence(unfolded.id, args.side, [...beta.path, 1]).actions.some(a => a.rule === "beta"),
      "an argument never offers beta of its parent");
  }
});

test("native trace records raw nodes, source identity, costs and retained state on refusal", async t => {
  const { session, initial } = await fixture(t);
  assert.equal(initial.traceSession.mainSource.text, payload.source);
  const source = initial.traceSession.sources.find(s => s.name === payload.main);
  const { createHash } = await import("node:crypto");
  assert.equal(source.sha256, createHash("sha256").update(payload.source).digest("hex"));
  assert.equal(initial.traceInitial.nodes[0].kind, "App");
  const before = session.program.kernel.work();
  const excerpt = traceSnapshot(session.program, session.state(initial.id), "expression", [], 1);
  assert.equal(excerpt.nodes.length, 1);
  assert.ok(excerpt.omittedDiscoveredNodes > 0);
  assert.deepEqual(session.program.kernel.work(), before, "tracing reads never reduce or check");
  const args = { state: initial.id, side: "expression", path: [0], rule: "delta", budget: 100000 };
  const unfolded = await session.handle("step", args);
  assert.equal(unfolded.trace.before.nodes[0].definition.name, "workbench__identity");
  assert.equal(unfolded.trace.after.nodes[0].kind, "Lam");
  assert.equal(unfolded.trace.after.state, unfolded.id);
  assert.ok(unfolded.trace.cost.work.instructions > 0);
  assert.ok(unfolded.trace.cost.elapsedMs >= 0);
  await assert.rejects(session.handle("step", { ...args, path: [], rule: "normalize", budget: 1 }), error => {
    assert.equal(error.kind, "budget");
    assert.equal(error.trace.retainedState, initial.id);
    assert.equal(error.trace.before.nodes[0].kind, "App");
    assert.ok(error.trace.cost.work.exhausted > 0);
    assert.ok(error.trace.cost.work.instructionSteps > 0);
    assert.doesNotThrow(() => JSON.stringify(error.trace));
    return true;
  });
  const type = await session.handle("step", { ...args, side: "type", path: [], rule: "whnf" });
  assert.equal(type.trace.before.side, "type");
  assert.equal(type.trace.before.selected, initial.checked.typeHandle);
});

// The workbench's normalize shows the folded normal form, as every normal
// form shown on request is (docs/roadmaps/historical/folded-normal-forms.md):
// identity(tt) computes, and identity, a function, stays named.
test("workbench normalization keeps a named function folded and checks the result", async t => {
  const session = new WorkbenchSession(module);
  t.after(() => session.dispose());
  const initial = await session.load({ ...payload, source: "def identity(x : Unit) := x; def example : (Unit -> Unit) and Unit := (identity, identity(tt));" });
  const next = await session.handle("reduce", { state: initial.id, side: "expression", kind: "normalize", path: [] });
  assert.equal(next.change.rule, "Normalized");
  assert.equal(next.view.expression.first.tag, "DefRef");
  assert.equal(next.view.expression.second.tag, "Point");
  assert.equal(session.program.checker.driver.graph.judgement(next.checked.judgement).kind, "typing");
});

// A transfer's sources are text no reader placed: the workbench asks which
// are the library's, as library/ holds them, so a library axiom keeps its
// bare name, and an edited import, or no way to ask, leaves it qualified
// (#317's review round 3, finding 4).
test("a transfer keeps the library's labels only for the library's own text", async t => {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  await program.check("import classical_axioms;\ndef excluded : ExcludedMiddle(U0) := LEM(U0);", "workbench");
  const exported = program.export("workbench__excluded");
  const fromLibrary = libraryProvenance(moduleListing, path => readFile(new URL(`../${path}`, import.meta.url), "utf8"));
  const label = async (sources, options) => {
    const session = new WorkbenchSession(module, options);
    t.after(() => session.dispose());
    const loaded = await session.load({ ...exported, sources });
    return Object.values(loaded.view.symbols).filter(symbol => symbol.kind === "axiom").map(symbol => symbol.name).sort();
  };
  assert.deepEqual(await label(exported.sources, { fromLibrary }), ["Choice", "LEM"]);
  assert.deepEqual(await label(exported.sources, {}), ["classical_axioms::Choice", "classical_axioms::LEM"]);
  const edited = { ...exported.sources, h1_truncation: `${exported.sources.h1_truncation}\ndef extra := tt;\n` };
  assert.deepEqual(await label(edited, { fromLibrary }), ["classical_axioms::Choice", "classical_axioms::LEM"]);
});

// Provenance only names axioms: a transfer whose library text cannot be
// fetched keeps its own sources, with qualified labels, and loads the term
// that was checked, over classical_axioms's LEM; one that does not replay
// completely, which would load another term, is refused (#317's review
// round 4, finding 1).
test("a transfer whose provenance cannot be read keeps its sources, and an incomplete one is refused", async t => {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  await program.check("import classical_axioms;\ndef e := LEM(U0);", "workbench");
  const exported = program.export("workbench__e");
  const offline = () => Promise.reject(new Error("offline"));
  for (const fromLibrary of [libraryProvenance(moduleListing, offline), offline]) {
    const session = new WorkbenchSession(module, { fromLibrary });
    t.after(() => session.dispose());
    const loaded = await session.load(exported);
    assert.deepEqual(loaded.view.axioms.map(name => loaded.view.symbols[name].name), ["classical_axioms::LEM"]);
  }
  const session = new WorkbenchSession(module);
  t.after(() => session.dispose());
  const { h1_truncation, ...missing } = exported.sources;
  assert.equal(typeof h1_truncation, "string");
  await assert.rejects(session.load({ ...exported, sources: missing }), /did not replay completely/);
});
