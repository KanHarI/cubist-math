// A REPL's entries, run again on a new worker after a kernel failure stopped
// the old one (replaying in web/repl-console.mjs).
import test from "node:test";
import assert from "node:assert/strict";
import { replaying } from "../web/repl-console.mjs";

// A worker as a REPL sees it: each entry checked as the next repl_N of its
// session, and a kernel failure, marked fatal, that ends the worker. The
// next request goes to a new worker, with an empty session.
function host() {
  let worker = 1, session = [], failing = null, refusing = new Set();
  return {
    generation: () => worker,
    session: () => session,
    fail(input) { failing = input; },
    refuse(input) { refusing.add(input); },
    replace() { worker++; session = []; },
    async run(input) {
      if (input === failing) {
        failing = null; worker++; session = [];
        throw Object.assign(new Error("The kernel failed."), { fatal: true });
      }
      session.push(input);
      return input.startsWith("bad") || refusing.has(input) ? [{ kind: "error", text: `${input} refused` }]
        : [{ kind: "defined", text: `${input} : repl_${session.length}` }];
    },
  };
}
const restarted = "The kernel was restarted. The session's entries were checked again.";

test("an entry a kernel failure ends: the entries before it run again, in order, under their names", async () => {
  const worker = host(), entries = replaying(input => worker.run(input), worker.generation);
  for (const input of ["a", "bad", "b"]) await entries.run(input);
  worker.fail("c");
  assert.deepEqual(await entries.run("c"), [{ kind: "error", text: "The kernel failed." }, { kind: "info", text: restarted }]);
  // The refused entry is run again too, so that b is still repl_3.
  assert.deepEqual(worker.session(), ["a", "bad", "b"]);
  assert.deepEqual(await entries.run("d"), [{ kind: "defined", text: "d : repl_4" }]);
});

test("a worker replaced by another request: the entries run again before the next one", async () => {
  const worker = host(), entries = replaying(input => worker.run(input), worker.generation);
  await entries.run("a");
  worker.replace();
  assert.deepEqual(await entries.run("b"), [{ kind: "info", text: restarted }, { kind: "defined", text: "b : repl_2" }]);
  // A session with nothing to run again says nothing.
  const empty = host(), fresh = replaying(input => empty.run(input), empty.generation);
  empty.replace();
  assert.deepEqual(await fresh.run("a"), [{ kind: "defined", text: "a : repl_1" }]);
});

test("an entry that no longer checks when run again is named, and a failure while running them again loses the session", async () => {
  const worker = host(), entries = replaying(input => worker.run(input), worker.generation);
  for (const input of ["a", "b"]) await entries.run(input);
  worker.refuse("b");
  worker.fail("c");
  assert.deepEqual((await entries.run("c")).at(-1), { kind: "info",
    text: "The kernel was restarted. These entries could not be checked again, and what they defined is gone: b." });
  worker.replace();
  worker.fail("a");
  assert.deepEqual(await entries.run("d"), [{ kind: "error", text: "The kernel failed." },
    { kind: "info", text: "The kernel was restarted. The session's entries could not be checked again, and what they defined is gone." },
    { kind: "defined", text: "d : repl_1" }]);
  // Nothing is left to run again: the session started over.
  worker.replace();
  assert.deepEqual(await entries.run("e"), [{ kind: "info", text: restarted }, { kind: "defined", text: "e : repl_2" }]);
});

test("a reset forgets the entries, and errors that are not fatal pass through", async () => {
  const worker = host(), entries = replaying(input => worker.run(input), worker.generation);
  await entries.run("a");
  entries.reset();
  worker.replace();
  assert.deepEqual(await entries.run("b"), [{ kind: "defined", text: "b : repl_1" }]);
  const refusing = replaying(async () => { throw new Error("unavailable"); }, () => 1);
  await assert.rejects(refusing.run("a"), /unavailable/);
});
