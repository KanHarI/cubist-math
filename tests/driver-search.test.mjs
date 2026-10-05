import "./fresh-build.mjs";
// The instruction driver's search as data (docs/roadmaps/learned-search.md,
// phases 1 and 2): kernel work read through the bridge, the moves each
// branch point of `agree` offers, pluggable policies, and the coverage
// tool's report and exit status.
import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtemp, readFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { InstructionDriver, heuristicPolicy } from "../web/cubical-instruction-driver.mjs";
import { countingPolicy, recordingPolicy, workSince, kernelSteps } from "../tools/search-telemetry.mjs";
import { driverTrace, traceSource } from "./driver-trace.mjs";

const point = { tag: "Point" }, unit = { tag: "Unit" }, two = { tag: "Sum", left: unit, right: unit };
const identity = { tag: "Lam", name: "x", domain: unit, body: { tag: "Var", name: "x" } };

async function session(t) {
  const kernel = new CubicalKernel(await createCubical());
  t.after(() => kernel.dispose());
  return { kernel, syntax: new CubicalSyntax(kernel), graph: new InstructionGraph(kernel) };
}

test("kernel work: instructions, queries, failures and budgets, read as differences through the bridge", async t => {
  const { kernel, syntax, graph } = await session(t);
  assert.deepEqual(Object.values(kernel.work()), [0, 0, 0, 0, 0, 0, 0, 0]);
  let before = kernel.work();
  const n = graph.unit();
  const first = workSince(before, kernel.work());
  assert.equal(first.instructions, 1);
  assert.ok(first.instructionSteps >= 1);
  // Answered from the derivation memo, an instruction costs its entry step.
  before = kernel.work();
  assert.equal(graph.unit(), n);
  assert.deepEqual(workSince(before, kernel.work()), { ...first, instructionSteps: 1 });
  // A rejected instruction counts, and so does its error.
  before = kernel.work();
  assert.throws(() => graph.apply(n, n), /Π type/);
  const rejected = workSince(before, kernel.work());
  assert.equal(rejected.instructions, 1);
  assert.equal(rejected.rejected, 1);
  // The guide's weak heads are queries, with their own budget: a question
  // cut short spends exactly that budget, and is no answer.
  const redex = syntax.encode({ tag: "App", fn: identity, arg: point });
  before = kernel.work();
  assert.equal(graph.head(redex, 1), 0);
  const short = workSince(before, kernel.work());
  assert.deepEqual([short.queries, short.failedQueries, short.querySteps, short.exhausted], [1, 1, 1, 1]);
  before = kernel.work();
  assert.ok(graph.head(redex, 4000));
  const answered = workSince(before, kernel.work());
  assert.equal(answered.queries, 1);
  assert.equal(answered.failedQueries, 0);
  // Rollback discards judgements, not the work that made them.
  kernel.module._cb_checkpoint(kernel.handle);
  graph.point();
  const kept = kernel.work();
  kernel.module._cb_rollback(kernel.handle);
  assert.deepEqual(kernel.work(), kept);
});

// Two sides to agree: (λx. x) tt and tt, as the right sides of reflexivity.
async function sides(t, policy) {
  const { kernel, syntax, graph } = await session(t);
  const driver = new InstructionDriver(kernel, { policy });
  const focus = term => driver.focus(graph.refl(driver.infer(syntax.encode(term))), "other");
  return { kernel, driver, a: focus({ tag: "App", fn: identity, arg: point }), b: focus(point) };
}

test("agree: a branch point lists the moves the shapes allow, and the heuristic makes today's move", async t => {
  const points = [];
  const { kernel, driver, a, b } = await sides(t, null);
  driver.policy = recordingPolicy(heuristicPolicy, kernel, point => points.push(point));
  assert.equal(driver.agree(a, b), true);
  // One point: a beta step on the left, or its weak head. No congruence:
  // the heads differ; no eta: neither is a lambda.
  assert.equal(points.length, 1);
  assert.deepEqual(points[0].heads, ["App", "Point"]);
  const [listing] = points[0].listings;
  assert.deepEqual(listing.moves, ["step:left:beta", "whnf:left"]);
  assert.deepEqual(listing.made.map(([name, outcome]) => [name, outcome]), [["step:left:beta", "progress"]]);
  assert.ok(listing.made[0][2] > 0, "the step's kernel steps are recorded");
});

test("agree: comparisons nest by congruence, and the record keeps each point's moves apart", async t => {
  const { kernel, syntax, graph } = await session(t), points = [];
  const driver = new InstructionDriver(kernel, { policy: recordingPolicy(heuristicPolicy, kernel, point => points.push(point)) });
  const focus = term => driver.focus(graph.refl(driver.infer(syntax.encode(term))), "other");
  // inl((λx. x) tt) against inl(tt): descend, and inside, a beta step.
  const left = { tag: "Inl", as: two, value: point };
  assert.equal(driver.agree(focus({ tag: "Inl", as: two, value: { tag: "App", fn: identity, arg: point } }), focus(left)), true);
  assert.deepEqual(points.map(point => [point.depth, point.heads, point.listings.map(listing => listing.made.map(([name, outcome]) => `${name} ${outcome}`))]), [
    [0, ["Inl", "Inl"], [["descend agreed"]]],
    [1, ["App", "Point"], [["step:left:beta progress"]]],
  ]);
  // The outer move's steps include the nested comparison's.
  assert.ok(points[0].listings[0].made[0][2] >= points[1].listings[0].made[0][2]);
});

test("agree: a move that throws is reported to observers with its work, and the error ends the comparison", async t => {
  const points = [];
  const { kernel, driver, a, b } = await sides(t, null);
  driver.policy = recordingPolicy(heuristicPolicy, kernel, point => points.push(point));
  // One step of budget: the beta step's instruction takes it on entry and
  // runs out computing.
  kernel.stepBudget = 1n; kernel.module._cb_step_budget(kernel.handle, 1, 0);
  assert.throws(() => driver.agree(a, b), error => error.kind === "budget");
  const [made] = points[0].listings[0].made;
  assert.equal(made[0], "step:left:beta");
  assert.equal(made[1], "error");
  assert.ok(made[2] >= 1, "the failed move's kernel steps are recorded");
  const counting = countingPolicy(heuristicPolicy);
  const again = await sides(t, counting);
  again.kernel.stepBudget = 1n; again.kernel.module._cb_step_budget(again.kernel.handle, 1, 0);
  assert.throws(() => again.driver.agree(again.a, again.b), error => error.kind === "budget");
  assert.deepEqual(counting.counts.moves, { "step:left:beta": { error: 1 } });
});

test("the default policy makes the driver's pinned moves: a recorded trace", async () => {
  // Independent of the policy interface: the instructions issued and the
  // guide's queries, in order, against tests/fixtures/driver-trace.json.
  // First recorded from the pre-refactor driver at d44239e, which the
  // policy refactor reproduced exactly; re-recorded after the context-scope
  // fix, as the fixture's method says.
  const pinned = JSON.parse(await readFile(new URL("./fixtures/driver-trace.json", import.meta.url), "utf8"));
  const trace = await driverTrace();
  assert.deepEqual(trace.failed, []);
  assert.deepEqual({ issued: trace.issued, heads: trace.heads, checked: trace.checked, sha256: trace.sha256 },
    { issued: pinned.issued, heads: pinned.heads, checked: pinned.checked, sha256: pinned.sha256 });
  // The fixture exercises the branch points that matter.
  const program = new CubicalProgram(await createCubical(), name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8"),
    { collectReferences: false });
  try {
    const counting = countingPolicy(heuristicPolicy);
    program.kernel.policy = counting;
    await program.check(traceSource, "trace");
    const { moves } = counting.counts;
    assert.ok(moves.normalize?.agreed, "a long closed computation is normalized");
    assert.ok(moves.descend?.changed, "congruence fails and the search goes on");
    assert.ok(moves["step:both:delta"]?.progress, "the same definition unfolds on both sides");
    assert.ok(moves["step:left:delta"]?.progress && moves["step:right:delta"]?.progress, "the later definition unfolds first");
    assert.ok(moves["whnf:left"]?.stuck || moves["whnf:right"]?.stuck, "a weak head that does not compute");
  } finally { program.dispose(); }
});

// Two compositions that are one partial element, split otherwise: (path k.
// comp^z A [k = 0 ↦ x] x) @ (i ∧ j), whose tube is on i = 0 ∨ j = 0 once the
// path is applied, and comp^z A [i = 0 ↦ x, j = 0 ↦ x] x, over a type A
// whose compositions do not compute.
async function splitSides(t, policy) {
  const { kernel, syntax, graph } = await session(t);
  const driver = new InstructionDriver(kernel, { policy });
  const A = { tag: "Var", name: "A" }, x = { tag: "Var", name: "x" };
  const at0 = name => [[`${name}:0`]];
  const dimensions = new Map([["i", 2], ["j", 3]]);
  const context = [[kernel.symbol("A"), syntax.encode({ tag: "U", level: 0 })], [kernel.symbol("x"), syntax.encode(A)]];
  const line = { tag: "PLam", dim: "k", family: A, body: { tag: "Comp", dim: "z", family: A, system: [{ face: at0("k"), term: x }], base: x } };
  const meet = [["i:1", "j:1"]];
  const left = { tag: "PApp", path: line, arg: meet };
  const right = { tag: "Comp", dim: "z", family: A, system: [{ face: at0("i"), term: x }, { face: at0("j"), term: x }], base: x };
  const focus = term => driver.focus(graph.refl(driver.infer(syntax.encode(term, dimensions), context, 0b1100n)), "other");
  return { kernel, driver, a: focus(left), b: focus(right) };
}

test("agree: compositions whose tubes are split otherwise agree by the kernel's split step", async t => {
  const points = [];
  const { kernel, driver, a, b } = await splitSides(t, null);
  driver.policy = recordingPolicy(heuristicPolicy, kernel, point => points.push(point));
  assert.equal(driver.agree(a, b), true);
  const made = points.flatMap(point => point.listings.flatMap(listing => listing.made.map(([name]) => name)));
  assert.ok(made.includes("split:left"), made.join(", "));
  // Without the split move, the two systems cannot be compared.
  const withoutSplit = { name: "without split", *rank(point) {
    for (const move of heuristicPolicy.rank(point)) if (move.move !== "split") yield move;
  } };
  const again = await splitSides(t, withoutSplit);
  assert.equal(again.driver.agree(again.a, again.b), false);
});

test("a formula of the wrong sort is refused, not read as the other sort", async t => {
  const { kernel, syntax } = await session(t);
  const driver = new InstructionDriver(kernel);
  // A path applied at the face 1, which the driver read as the endpoint 1.
  const line = syntax.encode({ tag: "PLam", dim: "k", family: unit, body: point });
  const one = clauses => [[0n, 0n], ...clauses];
  const atFace = kernel.term("PApp", kernel.formula("face", one([])), line, 0);
  assert.throws(() => driver.infer(atFace), /A path is applied at an interval point; found a face formula\./);
  assert.ok(driver.infer(kernel.term("PApp", kernel.formula("interval", one([])), line, 0)));
  // A tube on the interval point 1, which the driver read as the face 1.
  const tube = kernel.term("Tube", kernel.formula("interval", one([])), syntax.encode(point), 0);
  const comp = kernel.term("Comp", 0, syntax.encode(unit), tube, syntax.encode(point));
  assert.throws(() => driver.infer(comp), /A partial element's face is a face formula; found an interval point\./);
  const faced = kernel.term("Comp", 0, syntax.encode(unit),
    kernel.term("Tube", kernel.formula("face", one([])), syntax.encode(point), 0), syntax.encode(point));
  assert.ok(driver.infer(faced));
});

test("agree: policies are pluggable and untrusted", async t => {
  // A policy that makes no move: the comparison fails.
  const none = await sides(t, { name: "none", *rank() {} });
  assert.equal(none.driver.agree(none.a, none.b), false);
  // Another order still agrees: every move is checked by the kernel.
  const lazy = await sides(t, { name: "whnf first", *rank(point) {
    yield* point.moves.filter(move => move.move === "whnf");
    yield* heuristicPolicy.rank(point);
  } });
  assert.equal(lazy.driver.agree(lazy.a, lazy.b), true);
  // A move the point did not offer is refused.
  const rogue = await sides(t, { name: "rogue", *rank() { yield { move: "eta" }; } });
  assert.throws(() => rogue.driver.agree(rogue.a, rogue.b), /ranked a move that is not open/);
});

test("the heuristic policy, counted, derives the first library exactly as the default driver does", async t => {
  const source = await readFile(new URL("../library/nat.cubist", import.meta.url), "utf8");
  const derive = async policy => {
    const program = new CubicalProgram(await createCubical(), async () => { throw new Error("no imports"); });
    t.after(() => program.dispose());
    await program.check(source, "nat");
    const kernel = program.kernel, before = kernel.work(), judgements = [];
    for (const [name, reference] of kernel.definitions) {
      const { value, type } = kernel.definition(reference);
      const driver = new InstructionDriver(kernel, { policy });
      judgements.push([name, driver.graph.judgement(driver.check(value, type)).rule]);
    }
    return { work: workSince(before, kernel.work()), judgements };
  };
  const counting = countingPolicy(heuristicPolicy);
  const plain = await derive(undefined), counted = await derive(counting);
  assert.deepEqual(counted, plain);
  assert.ok(kernelSteps(plain.work) > 0);
  assert.ok(counting.counts.points > 0);
  const outcomes = Object.values(counting.counts.moves).flatMap(Object.keys);
  assert.ok(outcomes.includes("progress"));
});

const tool = fileURLToPath(new URL("../tools/instruction-coverage.mjs", import.meta.url));
const coverage = (args, report) => spawnSync(process.execPath, [tool, ...args, `--report=${report}`],
  { encoding: "utf8", timeout: 120000 });

test("instruction coverage: the report pins what it measured, and the exit status is the verdict", async t => {
  const directory = await mkdtemp(join(tmpdir(), "coverage-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const report = join(directory, "report.json"), trajectories = join(directory, "trajectories.jsonl");
  const passed = coverage(["--modules=basics", `--trajectories=${trajectories}`], report);
  assert.equal(passed.status, 0, passed.stderr + passed.stdout);
  assert.match(passed.stdout, /28 of 28 declarations in 1 module, 0 gaps/);
  assert.match(passed.stdout, /Coverage complete\./);
  const written = JSON.parse(await readFile(report, "utf8"));
  assert.equal(written.success, true);
  assert.equal(written.derived, written.definitions);
  assert.ok(written.environment.node && written.budgets.fuel && written.session);
  assert.ok(written.work.instructions > 0 && written.search.points > 0);
  // A record for every definition derived again, with its work and outcome.
  assert.equal(written.perDefinition.rows.length, written.definitions);
  const field = name => written.perDefinition.fields.indexOf(name);
  assert.ok(written.perDefinition.rows.every(row => row[field("outcome")] === "derived" && row[field("instructions")] > 0));
  const lines = (await readFile(trajectories, "utf8")).trim().split("\n").map(line => JSON.parse(line));
  assert.equal(lines.length, written.definitions);
  assert.ok(lines.every(line => line.outcome === "derived" && Array.isArray(line.points)));
  // Nothing derived is no success; neither is a module that does not load.
  // A definition that fails has its record too.
  const tight = coverage(["--modules=basics", "--limit-ms=0.000001"], report);
  assert.equal(tight.status, 1);
  const failed = JSON.parse(await readFile(report, "utf8"));
  assert.equal(failed.perDefinition.rows.length, failed.definitions);
  assert.ok(failed.perDefinition.rows.some(row => row[failed.perDefinition.fields.indexOf("outcome")] !== "derived"));
  const empty = coverage(["--modules=basics", "--select=^no_such_definition$"], report);
  assert.equal(empty.status, 1);
  assert.match(empty.stdout, /Coverage incomplete/);
  const missing = coverage(["--modules=no_such_module"], report);
  assert.equal(missing.status, 1);
  assert.match(missing.stdout, /1 gap;/);
});
