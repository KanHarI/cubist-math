import "./fresh-build.mjs";
import createLegacyCubical from "../tools/legacy-kernel.mjs";
// The instruction driver's search as data (docs/roadmaps/learned-search.md,
// phases 1 and 2): kernel work read through the bridge, the moves each
// branch point of `agree` offers, pluggable choosers, and the coverage
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
import { InstructionDriver, heuristicChooser } from "../web/cubical-instruction-driver.mjs";
import { countingChooser, recordingChooser, workSince, kernelSteps } from "../tools/search-telemetry.mjs";
import { driverTrace, traceSource } from "./driver-trace.mjs";

const zero = { tag: "Zero" }, nat = { tag: "Nat" };
const identity = { tag: "Lam", name: "x", domain: nat, body: { tag: "Var", name: "x" } };

async function session(t) {
  const kernel = new CubicalKernel(await createLegacyCubical());
  t.after(() => kernel.dispose());
  return { kernel, syntax: new CubicalSyntax(kernel), graph: new InstructionGraph(kernel) };
}

test("kernel work: instructions, queries, failures and budgets, read as differences through the bridge", async t => {
  const { kernel, syntax, graph } = await session(t);
  assert.deepEqual(Object.values(kernel.work()), [0, 0, 0, 0, 0, 0, 0, 0]);
  let before = kernel.work();
  const n = graph.nat();
  const first = workSince(before, kernel.work());
  assert.equal(first.instructions, 1);
  assert.ok(first.instructionSteps >= 1);
  // Answered from the derivation memo, an instruction costs its entry step.
  before = kernel.work();
  assert.equal(graph.nat(), n);
  assert.deepEqual(workSince(before, kernel.work()), { ...first, instructionSteps: 1 });
  // A rejected instruction counts, and so does its error.
  before = kernel.work();
  assert.throws(() => graph.apply(n, n), /Π type/);
  const rejected = workSince(before, kernel.work());
  assert.equal(rejected.instructions, 1);
  assert.equal(rejected.rejected, 1);
  // The guide's weak heads are queries, with their own budget: a question
  // cut short spends exactly that budget, and is no answer.
  const redex = syntax.encode({ tag: "App", fn: identity, arg: zero });
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
  graph.zero();
  const kept = kernel.work();
  kernel.module._cb_rollback(kernel.handle);
  assert.deepEqual(kernel.work(), kept);
});

// Two sides to agree: (λx. x) 0 and 0, as the right sides of reflexivity.
async function sides(t, chooser) {
  const { kernel, syntax, graph } = await session(t);
  const driver = new InstructionDriver(kernel, { chooser });
  const focus = term => driver.focus(graph.refl(driver.infer(syntax.encode(term))), "other");
  return { kernel, driver, a: focus({ tag: "App", fn: identity, arg: zero }), b: focus(zero) };
}

test("agree: a branch point lists the moves the shapes allow, and the heuristic makes today's choice", async t => {
  const points = [];
  const { kernel, driver, a, b } = await sides(t, null);
  driver.chooser = recordingChooser(heuristicChooser, kernel, point => points.push(point));
  assert.equal(driver.agree(a, b), true);
  // One point: a beta step on the left, or its weak head. No congruence:
  // the heads differ; no eta: neither is a lambda.
  assert.equal(points.length, 1);
  assert.deepEqual(points[0].heads, ["App", "Zero"]);
  const [listing] = points[0].listings;
  assert.deepEqual(listing.moves, ["step:left:beta", "whnf:left"]);
  assert.deepEqual(listing.made.map(([name, outcome]) => [name, outcome]), [["step:left:beta", "progress"]]);
  assert.ok(listing.made[0][2] > 0, "the step's kernel steps are recorded");
});

test("agree: comparisons nest by congruence, and the record keeps each point's moves apart", async t => {
  const { kernel, syntax, graph } = await session(t), points = [];
  const driver = new InstructionDriver(kernel, { chooser: recordingChooser(heuristicChooser, kernel, point => points.push(point)) });
  const focus = term => driver.focus(graph.refl(driver.infer(syntax.encode(term))), "other");
  // succ((λx. x) 0) against succ(0): descend, and inside, a beta step.
  const one = { tag: "Succ", value: zero };
  assert.equal(driver.agree(focus({ tag: "Succ", value: { tag: "App", fn: identity, arg: zero } }), focus(one)), true);
  assert.deepEqual(points.map(point => [point.depth, point.heads, point.listings.map(listing => listing.made.map(([name, outcome]) => `${name} ${outcome}`))]), [
    [0, ["Succ", "Succ"], [["descend agreed"]]],
    [1, ["App", "Zero"], [["step:left:beta progress"]]],
  ]);
  // The outer move's steps include the nested comparison's.
  assert.ok(points[0].listings[0].made[0][2] >= points[1].listings[0].made[0][2]);
});

test("agree: a move that throws is reported to observers with its work, and the error ends the comparison", async t => {
  const points = [];
  const { kernel, driver, a, b } = await sides(t, null);
  driver.chooser = recordingChooser(heuristicChooser, kernel, point => points.push(point));
  // One step of budget: the beta step's instruction takes it on entry and
  // runs out computing.
  kernel.stepBudget = 1n; kernel.module._cb_step_budget(kernel.handle, 1, 0);
  assert.throws(() => driver.agree(a, b), error => error.kind === "budget");
  const [made] = points[0].listings[0].made;
  assert.equal(made[0], "step:left:beta");
  assert.equal(made[1], "error");
  assert.ok(made[2] >= 1, "the failed move's kernel steps are recorded");
  const counting = countingChooser(heuristicChooser);
  const again = await sides(t, counting);
  again.kernel.stepBudget = 1n; again.kernel.module._cb_step_budget(again.kernel.handle, 1, 0);
  assert.throws(() => again.driver.agree(again.a, again.b), error => error.kind === "budget");
  assert.deepEqual(counting.counts.moves, { "step:left:beta": { error: 1 } });
});

test("the default chooser makes the driver's pinned moves: a recorded trace", async () => {
  // Independent of the chooser interface: the instructions issued and the
  // guide's queries, in order, against tests/fixtures/driver-trace.json.
  // First recorded from the pre-refactor driver at d44239e, which the
  // chooser refactor reproduced exactly; re-recorded after the context-scope
  // fix, as the fixture's method says.
  const pinned = JSON.parse(await readFile(new URL("./fixtures/driver-trace.json", import.meta.url), "utf8"));
  const trace = await driverTrace();
  assert.deepEqual(trace.failed, []);
  assert.deepEqual({ issued: trace.issued, heads: trace.heads, checked: trace.checked, sha256: trace.sha256 },
    { issued: pinned.issued, heads: pinned.heads, checked: pinned.checked, sha256: pinned.sha256 });
  // The fixture exercises the choices that matter.
  const program = new CubicalProgram(await createCubical(), name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8"),
    { collectReferences: false });
  try {
    const counting = countingChooser(heuristicChooser);
    program.kernel.chooser = counting;
    await program.check(traceSource, "trace");
    const { moves } = counting.counts;
    assert.ok(moves.normalize?.agreed, "a long closed computation is normalized");
    assert.ok(moves.descend?.changed, "congruence fails and the search goes on");
    assert.ok(moves["step:both:delta"]?.progress, "the same definition unfolds on both sides");
    assert.ok(moves["step:left:delta"]?.progress && moves["step:right:delta"]?.progress, "the later definition unfolds first");
    assert.ok(moves["whnf:left"]?.stuck || moves["whnf:right"]?.stuck, "a weak head that does not compute");
  } finally { program.dispose(); }
});

test("agree: choosers are pluggable and untrusted", async t => {
  // A chooser that makes no move: the comparison fails.
  const none = await sides(t, { name: "none", *rank() {} });
  assert.equal(none.driver.agree(none.a, none.b), false);
  // Another order still agrees: every move is checked by the kernel.
  const lazy = await sides(t, { name: "whnf first", *rank(point) {
    yield* point.moves.filter(move => move.move === "whnf");
    yield* heuristicChooser.rank(point);
  } });
  assert.equal(lazy.driver.agree(lazy.a, lazy.b), true);
  // A move the point did not offer is refused.
  const rogue = await sides(t, { name: "rogue", *rank() { yield { move: "eta" }; } });
  assert.throws(() => rogue.driver.agree(rogue.a, rogue.b), /chose a move that is not open/);
});

test("the heuristic chooser, counted, derives the first library exactly as the default driver does", async t => {
  const source = await readFile(new URL("../library/naturals.cubist", import.meta.url), "utf8");
  const derive = async chooser => {
    const program = new CubicalProgram(await createCubical(), async () => { throw new Error("no imports"); });
    t.after(() => program.dispose());
    await program.check(source, "naturals");
    const kernel = program.kernel, before = kernel.work(), judgements = [];
    for (const [name, reference] of kernel.definitions) {
      const { value, type } = kernel.definition(reference);
      const driver = new InstructionDriver(kernel, { chooser });
      judgements.push([name, driver.graph.judgement(driver.check(value, type)).rule]);
    }
    return { work: workSince(before, kernel.work()), judgements };
  };
  const counting = countingChooser(heuristicChooser);
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
  assert.match(passed.stdout, /5 of 5 declarations in 1 module, 0 gaps/);
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
