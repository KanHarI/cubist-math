import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { proofRequestWatchdog, checkingCommands, queryCommands } from "../web/proof-watchdog.mjs";

function fakeClock() {
  let now = 0;
  let serial = 0;
  const timers = new Map();
  return {
    setTimeout(callback, delay) {
      const id = ++serial;
      timers.set(id, { callback, deadline: now + delay });
      return id;
    },
    clearTimeout(id) { timers.delete(id); },
    advance(delta) {
      const target = now + delta;
      while (true) {
        const next = [...timers].sort((a, b) => a[1].deadline - b[1].deadline)[0];
        if (!next || next[1].deadline > target) break;
        now = next[1].deadline;
        timers.delete(next[0]);
        next[1].callback();
      }
      now = target;
    },
  };
}

test("a proof may run past five minutes while kernel steps advance", () => {
  const clock = fakeClock();
  let expired = 0;
  const request = proofRequestWatchdog("check", () => expired++, clock);
  for (let i = 1; i <= 4; i++) {
    clock.advance(299000);
    request.progress({ instructions: i * 1000, completed: 0 });
    assert.equal(expired, 0);
  }
  // Repeated or regressing counters cannot keep a stalled worker alive.
  clock.advance(299000);
  request.progress({ instructions: 4000, completed: 0 });
  request.progress({ instructions: 3000, completed: 0 });
  clock.advance(1000);
  assert.equal(expired, 1);
});

test("completed definitions also advance a check, and completion cancels its timer", () => {
  const clock = fakeClock();
  let expired = 0;
  const request = proofRequestWatchdog("check", () => expired++, clock);
  clock.advance(299000);
  request.progress({ instructions: 0, completed: 1 });
  clock.advance(299000);
  assert.equal(expired, 0);
  request.stop();
  request.progress({ instructions: 1000, completed: 2 });
  clock.advance(600000);
  assert.equal(expired, 0);
});

test("silent checks and other requests still time out", () => {
  const clock = fakeClock();
  let checks = 0;
  let inspections = 0;
  proofRequestWatchdog("check", () => checks++, clock);
  const inspection = proofRequestWatchdog("inspect", () => inspections++, clock);
  clock.advance(29999);
  inspection.progress({ instructions: 1000, completed: 1 });
  assert.equal(inspections, 0);
  clock.advance(1);
  assert.equal(inspections, 1);
  assert.equal(checks, 0);
  clock.advance(270000);
  assert.equal(checks, 1);
});

test("module and contextual queries share the finite checking timeout", () => {
  for (const command of ["repl", "context-run"]) {
    const clock = fakeClock();
    let expired = 0;
    const request = proofRequestWatchdog(command, () => expired++, clock);
    clock.advance(299999);
    assert.equal(expired, 0, command);
    request.progress({ instructions: 1000, completed: 1 });
    clock.advance(1);
    assert.equal(expired, 1, command);
  }
});

// Every command the worker answers is checking work or a query: a session's
// restore on a new worker checks its entries again, imports among them, so
// it has the time an entry has (proof-watchdog.mjs).
test("every worker command is classified, and a session's restore is checking work", () => {
  const worker = readFileSync(new URL("../web/cubical-worker.mjs", import.meta.url), "utf8");
  const commands = new Set(worker.split("\n").filter(line => /\bcommand\b/.test(line))
    .flatMap(line => [...line.matchAll(/"([a-z-]+)"/g)].map(match => match[1])));
  assert.deepEqual([...commands].sort(), [...checkingCommands, ...queryCommands].sort());
  assert.deepEqual([...checkingCommands].filter(command => queryCommands.has(command)), []);
  for (const command of ["repl-restore", "elaborate"]) {
    const clock = fakeClock();
    let expired = 0;
    proofRequestWatchdog(command, () => expired++, clock);
    clock.advance(299999);
    assert.equal(expired, 0, command);
    clock.advance(1);
    assert.equal(expired, 1, command);
  }
});
