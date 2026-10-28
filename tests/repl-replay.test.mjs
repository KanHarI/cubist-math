// A REPL's session, restored on a new worker after a kernel failure stopped
// the old one, from the record the page kept (recordedSession in
// web/repl-console.mjs; ReplSession.record and restore do the checking).
import test from "node:test";
import assert from "node:assert/strict";
import { recordedSession } from "../web/repl-console.mjs";

// A worker as a REPL's page sees it: each entry checked as the next repl_N
// of its session and answered with the session's record, a record restored
// on a new worker, and a kernel failure, marked fatal, that ends the worker.
// The next request goes to a new worker, with an empty session. An entry
// "bad…" is refused, and extends nothing. A worker over a proof answers
// nothing until it has checked it (`proven`), and a restore can be held up.
function host() {
  let worker = 1, session = { accepted: [], count: 0 }, failing = null, holding = null;
  const losing = new Set(), restores = [];
  const fatal = () => {
    failing = null; worker++; session = { accepted: [], count: 0 };
    return Object.assign(new Error("The kernel failed."), { fatal: true });
  };
  return {
    generation: () => worker,
    restores,
    proven: true,
    fail(input) { failing = input; },
    lose(text) { losing.add(text); },
    replace() { worker++; session = { accepted: [], count: 0 }; },
    hold() { let release; holding = new Promise(resolve => { release = resolve; }); return release; },
    async request(command, args) {
      if (!this.proven) throw new Error("Check a proof first.");
      if (command === "repl-restore" && holding) { await holding; holding = null; }
      if (command === "repl") {
        if (args.input === failing) throw fatal();
        const entry = ++session.count;
        if (!args.input.startsWith("bad")) session.accepted.push({ text: args.input, entry });
        const results = [args.input.startsWith("bad") ? { kind: "error", text: `${args.input} refused` }
          : { kind: "defined", text: `${args.input} : repl_${entry}` }];
        return args.record ? { results, record: structuredClone(session) } : results;
      }
      assert.equal(command, "repl-restore");
      restores.push(structuredClone(args.record));
      if (failing === "restore") throw fatal();
      session = { accepted: args.record.accepted.filter(({ text }) => !losing.has(text)), count: args.record.count };
      return { lost: args.record.accepted.filter(({ text }) => losing.has(text)).map(({ text }) => text), record: structuredClone(session) };
    },
  };
}
const restarted = { kind: "info", text: "The kernel was restarted. The session's entries were checked again." };
const failed = { kind: "error", text: "The kernel failed." };

test("an entry a kernel failure ends: the session's record is restored at once on a new worker", async () => {
  const worker = host(), session = recordedSession((...call) => worker.request(...call), { generation: worker.generation });
  for (const input of ["a", "bad", "b"]) await session.run(input);
  worker.fail("c");
  assert.deepEqual(await session.run("c"), [failed, restarted]);
  // What was refused is not in the record, so not checked again; b is still
  // repl_3, and the next entry comes after it.
  assert.deepEqual(worker.restores, [{ accepted: [{ text: "a", entry: 1 }, { text: "b", entry: 3 }], count: 3 }]);
  assert.deepEqual(await session.run("d"), [{ kind: "defined", text: "d : repl_4" }]);
});

test("a worker replaced by another request: the session is restored before the next entry", async () => {
  const worker = host(), session = recordedSession((...call) => worker.request(...call), { generation: worker.generation });
  await session.run("a");
  worker.replace();
  assert.deepEqual(await session.run("b"), [restarted, { kind: "defined", text: "b : repl_2" }]);
  assert.equal(worker.restores.length, 1);
  // A session with nothing recorded restores nothing and says nothing.
  const empty = host(), fresh = recordedSession((...call) => empty.request(...call), { generation: empty.generation });
  empty.replace();
  assert.deepEqual(await fresh.run("a"), [{ kind: "defined", text: "a : repl_1" }]);
  assert.deepEqual(empty.restores, []);
});

test("each statement that no longer checks is named, and a restore that fails loses the session", async () => {
  const worker = host(), session = recordedSession((...call) => worker.request(...call), { generation: worker.generation });
  for (const input of ["a", "b"]) await session.run(input);
  worker.lose("b");
  worker.fail("c");
  assert.deepEqual((await session.run("c")).at(-1), { kind: "info",
    text: "The kernel was restarted. These entries could not be checked again, and what they defined is gone: b." });
  // The record restored is what the new worker kept: b is gone from it.
  worker.replace();
  worker.fail("restore");
  assert.deepEqual(await session.run("d"), [failed,
    { kind: "info", text: "The kernel was restarted. The session's entries could not be checked again, and what they defined is gone." },
    { kind: "defined", text: "d : repl_1" }]);
  assert.deepEqual(worker.restores.at(-1), { accepted: [{ text: "a", entry: 1 }], count: 2 });
  // Nothing is left to restore: the session started over.
  worker.replace();
  assert.deepEqual(await session.run("e"), [restarted, { kind: "defined", text: "e : repl_2" }]);
});

test("a page that rebuilds restores the session itself; a reset forgets it; errors that are not fatal pass through", async () => {
  const worker = host(), session = recordedSession((...call) => worker.request(...call), { generation: worker.generation, restoreAfterFault: false });
  await session.run("a");
  worker.fail("b");
  assert.deepEqual(await session.run("b"), [failed]);
  assert.deepEqual(await session.restore(), [restarted]);
  assert.deepEqual(await session.run("c"), [{ kind: "defined", text: "c : repl_2" }]);
  session.reset();
  worker.replace();
  assert.deepEqual(await session.run("d"), [{ kind: "defined", text: "d : repl_1" }]);
  const refusing = recordedSession(async () => { throw new Error("unavailable"); });
  await assert.rejects(refusing.run("a"), /unavailable/);
});

test("a reset while a restore is under way forgets the session: what the restore answers is not kept", async () => {
  const worker = host(), session = recordedSession((...call) => worker.request(...call),
    { generation: worker.generation, restoreAfterFault: false });
  await session.run("secret");
  worker.replace();
  const release = worker.hold(), restoring = session.restore();
  session.reset();
  release();
  assert.deepEqual(await restoring, []);
  // On a later worker nothing comes back: the next entry is the first.
  worker.replace();
  assert.deepEqual(await session.run("a"), [{ kind: "defined", text: "a : repl_1" }]);
  assert.equal(worker.restores.length, 1);
});

test("a session over a proof is restored once the new worker has checked it; an entry before is refused, and the record kept", async () => {
  const worker = host(), session = recordedSession((...call) => worker.request(...call),
    { generation: worker.generation, restoreAfterFault: false, restorable: () => worker.proven });
  await session.run("kept");
  worker.fail("check");
  assert.deepEqual(await session.run("check"), [failed]);
  worker.proven = false;
  await assert.rejects(session.run("typeof kept"), /Check a proof first/);
  assert.deepEqual(worker.restores, []);
  worker.proven = true;
  assert.deepEqual(await session.run("b"), [restarted, { kind: "defined", text: "b : repl_2" }]);
  assert.deepEqual(worker.restores, [{ accepted: [{ text: "kept", entry: 1 }], count: 1 }]);
});
