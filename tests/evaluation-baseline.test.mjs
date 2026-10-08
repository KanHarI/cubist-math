// The runtime evaluation baseline (EVAL0 of
// docs/roadmaps/runtime-evaluation-roadmap.md): tools/evaluation-baseline.mjs
// --write records tests/fixtures/evaluation-baseline.json, and the code keeps
// to it. Outcomes and the normalizations and comparisons an entry asks are
// exact; the kernel's deterministic work and the arena's growth may fall,
// but grow by at most a quarter. A change past that records the baseline
// again, with its reason. Times are never compared.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { workloads, measureWorkload, deterministic, fixture, version, contractOf, phases } from "../tools/evaluation-baseline.mjs";

const recorded = JSON.parse(await readFile(fixture, "utf8"));
const module = await createCubical();
const runs = new Map();
// A workload's cold run in a new program, measured once for every test here.
const cold = async id => {
  if (!runs.has(id)) runs.set(id, (await measureWorkload(module, workloads.find(workload => workload.id === id))).cold);
  return runs.get(id);
};
const recordOf = id => recorded.workloads.find(workload => workload.id === id);
// Growth allowed in a deterministic counter: a quarter, and a little for small counts.
const bound = value => Math.ceil(value * 1.25) + 64;
const counters = ["instructions", "instructionSteps", "queries", "querySteps", "failedQueries", "nodes"];
// Kernel outcomes retain the full rendered length and hash even when text is
// only a preview. Also compare text directly when the report holds it whole.
const sameOutcome = (live, record, label) => {
  assert.equal(live.status, record.status, label);
  assert.equal(live.code, record.code, label);
  assert.equal(live.length, record.length, `${label}: rendered length`);
  assert.equal(live.sha256, record.sha256, `${label}: rendered hash`);
  if (record.text.length === record.length) assert.equal(live.text, record.text, label);
};

test("the recorded baseline covers every workload, at this version, each deterministic", () => {
  assert.equal(recorded.version, version);
  assert.deepEqual(recorded.workloads.map(workload => [workload.id, workload.setup, workload.entry, workload.contract]),
    workloads.map(workload => [workload.id, workload.setup, workload.entry, contractOf(workload)]));
  assert.deepEqual(recorded.workloads.filter(workload => !workload.deterministic).map(workload => workload.id), []);
  assert.deepEqual(Object.keys(recorded.phases), Object.keys(phases));
  assert.ok(recorded.settings.samples >= 3, "a published baseline repeats each sample");
});

test("each workload's outcome, normalizations and comparisons are the recorded ones; its work grows by at most a quarter", async () => {
  for (const workload of workloads) {
    const live = await cold(workload.id), record = recordOf(workload.id), label = workload.id;
    if (workload.series === "scratch") {
      sameOutcome(live.outcome, record.outcome, label);
      assert.equal(live.stage, record.stage, label);
      if (record.outcome.status === "value") for (const [counter, value] of Object.entries(record.stats))
        assert.ok(live.stats[counter] <= bound(value), `${label}: ${counter}`);
      continue;
    }
    sameOutcome(live.outcome, record.outcome, label);
    for (const phase of ["normalize", "compare"]) {
      const figures = live.phases[phase], expected = record.phases[phase];
      assert.deepEqual(figures && [figures.calls, figures.failures], expected && [expected.calls, expected.failures ?? 0], `${label}: ${phase}`);
    }
    // The report leaves out counters that are zero.
    for (const [part, figures, expected] of [["the entry", live.entry, record.total],
      ...Object.entries(record.phases).map(([phase, expected]) => [phase, live.phases[phase] ?? {}, expected])])
      for (const counter of counters) assert.ok((figures[counter] ?? 0) <= bound(expected[counter] ?? 0),
        `${label}: ${part}'s ${counter} is ${figures[counter]}, recorded ${expected[counter] ?? 0}`);
  }
});

test("plain REPL evaluation normalizes and compares twice; print normalizes once and shows the same value", async () => {
  const repl = await cold("euclid-3"), print = await cold("euclid-3-print");
  assert.equal(repl.outcome.sha256, print.outcome.sha256);
  assert.match(repl.outcome.text, /^\(7, /);
  assert.equal(repl.phases.normalize.calls, 2);
  assert.equal(repl.phases.compare.calls, 2);
  assert.equal(print.phases.normalize.calls, 1);
  assert.equal(print.phases.compare, undefined);
  // The self-comparison checks the certificate again: almost all the entry's instructions.
  assert.ok(repl.phases.compare.instructions > 0.9 * repl.entry.instructions);
  assert.ok(print.entry.instructions < 100);
});

test("the depth failures are reproduced, with the work done before them", async () => {
  for (const id of ["euclid-4", "euclid-4-pattern", "euclid-4-prime", "euclid-4-prime-print", "euclid-5-prime"]) {
    const run = await cold(id);
    assert.equal(run.outcome.code, "K344", id);
    assert.equal(run.phases.normalize.failures, 1, id);
    assert.ok(run.phases.normalize.querySteps > 0 && run.phases.normalize.nodes > 10000, `${id} counts the failed normalization's work`);
    assert.equal(run.phases.compare, undefined, `${id} fails before any comparison`);
  }
  // A unary 510 is a normal form of depth 512, the limit: printed, it shows;
  // the REPL's self-comparison wraps it once more, and fails there.
  const printed = await cold("multiply-2-255-print"), compared = await cold("multiply-2-255");
  assert.equal(printed.outcome.text, "510");
  assert.equal(compared.outcome.code, "K344");
  assert.equal(compared.phases.normalize.failures, 0);
  assert.equal(compared.phases.compare.failures, 1);
  assert.equal((await cold("multiply-2-254")).outcome.text, "508");
  assert.equal((await cold("multiply-2-256-print")).outcome.code, "K344");
});

test("counters are deterministic: a new program repeats a run's", async () => {
  for (const id of ["euclid-4-prime", "divides-3-6", "scratch-euclid-3-prime"]) {
    const again = (await measureWorkload(module, workloads.find(workload => workload.id === id))).cold;
    assert.deepEqual(deterministic(again), deterministic(await cold(id)), id);
  }
});

test("the closure experiment is a separate, untrusted series that asks the kernel nothing", async () => {
  const expected = { 3: "7", 4: "5", 5: "11" };
  for (const [n, prime] of Object.entries(expected)) {
    const id = `scratch-euclid-${n}-prime`, run = await cold(id);
    assert.equal(contractOf(workloads.find(workload => workload.id === id)), "scratch");
    assert.deepEqual(run.outcome, { status: "value", text: prime }, id);
    assert.deepEqual([run.kernel.instructions, run.kernel.queries, run.kernel.nodes], [0, 0, 0], id);
    assert.ok(run.stats.forces > 0 && run.stats.hits > 0, id);
  }
  // It recurses on the host's stack, and overflows it: no controlled diagnostic yet (EVAL4).
  const overflow = await cold("scratch-euclid-6-prime");
  assert.equal(overflow.outcome.status, "error");
  assert.match(overflow.outcome.text, /call stack/);
});
