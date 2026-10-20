import test from "node:test";
import assert from "node:assert/strict";
import { WorkbenchTrace, traceAttempt } from "../web/cubical-workbench-trace.mjs";

test("trace preserves failed attempts and branches, with serializable pending work", () => {
  const trace = new WorkbenchTrace();
  const attempt = { state: 0, side: "expression", path: [1, 0], rule: "normalize", budget: 1 };
  const failed = trace.begin(traceAttempt("step", attempt));
  assert.equal(JSON.parse(trace.text({ state: 0 })).entries[0].status, "running");
  trace.finish(failed, { status: "refused", error: { kind: "budget", message: "budget exhausted" } });
  const accepted = trace.begin(traceAttempt("step", { ...attempt, rule: "delta", budget: 100000 }));
  trace.finish(accepted, { status: "accepted", resultState: 1 });
  trace.finish(trace.begin({ command: "back", state: 1 }), { status: "accepted", resultState: 0 });
  const next = trace.begin(traceAttempt("step", { ...attempt, rule: "whnf" }));
  trace.finish(next, { status: "accepted", resultState: 2 });
  const copied = JSON.parse(trace.text({ state: 2 }));
  assert.deepEqual(copied.entries.map(e => [e.command, e.state, e.resultState, e.status]), [
    ["step", 0, undefined, "refused"], ["step", 0, 1, "accepted"],
    ["back", 1, 0, "accepted"], ["step", 0, 2, "accepted"],
  ]);
  assert.deepEqual(copied.entries[0].path, [1, 0]);
  assert.equal(copied.entries[0].budget, 1);
  assert.equal(traceAttempt("occurrence", attempt), null);
});

test("trace bounds retained history and flags omitted input instead of expanding a DAG", () => {
  const trace = new WorkbenchTrace({ maxEntries: 2, maxCharacters: 1000 });
  for (let n = 0; n < 4; n++) trace.finish(trace.begin({ command: "step", state: n }), { status: "accepted" });
  assert.deepEqual(JSON.parse(trace.text({})).entries.map(e => e.sequence), [3, 4]);
  assert.equal(trace.dropped, 2);
  const next = trace.begin({ command: "step" });
  trace.finish(next, { status: "refused", detail: "x".repeat(900) });
  assert.equal(trace.entries.length, 1);
  let shared = { tag: "Point" };
  for (let i = 0; i < 40; i++) shared = { tag: "App", fn: shared, arg: shared };
  const edited = traceAttempt("check", { state: 0, term: shared });
  assert.match(edited.editedSyntax.omitted, /exceeds the trace limit/);
});
