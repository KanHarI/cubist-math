// A page's maintenance of its worker (web/worker-maintenance.mjs): every
// restore of a console's session (recordedSession in web/repl-console.mjs),
// however it starts, is maintenance, and a request from outside it waits
// until it is done, and is sent only then, its deadline (proofRequestWatchdog)
// starting as it is sent. Each way a restore starts: in the rebuild after a
// kernel failure, before an entry once the reader's check after a failure
// in a check is done, after a Restart, and after the reader's check on a
// worker started for it.
import test from "node:test";
import assert from "node:assert/strict";
import { workerMaintenance } from "../web/worker-maintenance.mjs";
import { recordedSession } from "../web/repl-console.mjs";
import { proofRequestWatchdog } from "../web/proof-watchdog.mjs";

function fakeClock() {
  let now = 0, serial = 0;
  const timers = new Map();
  return {
    setTimeout(callback, delay) { timers.set(++serial, { callback, deadline: now + delay }); return serial; },
    clearTimeout(id) { timers.delete(id); },
    advance(delta) {
      const target = now + delta;
      for (;;) {
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
const tick = () => new Promise(resolve => setImmediate(resolve));

// A worker over a proof, as the page sees it: a check installs the proof,
// an entry or a restore needs one, and a request can be held up until the
// test releases it. A new worker (replace) has neither proof nor session.
function worker() {
  let generation = 1, proven = false, session = { accepted: [], count: 0 };
  const held = new Map();
  return {
    generation: () => generation,
    get proven() { return proven; },
    replace() { generation++; proven = false; session = { accepted: [], count: 0 }; },
    hold(command) { let release; held.set(command, new Promise(resolve => { release = resolve; })); return release; },
    async answer(command, args) {
      const holding = held.get(command);
      held.delete(command);
      if (holding) await holding;
      if (command === "check") { proven = true; return { complete: true }; }
      if (["repl", "repl-restore"].includes(command) && !proven) throw new Error("Check a proof first.");
      if (command === "repl") {
        const entry = ++session.count;
        session.accepted.push({ text: args.input, entry });
        return { results: [{ kind: "defined", text: `${args.input} : repl_${entry}` }], record: structuredClone(session) };
      }
      if (command === "repl-restore") { session = structuredClone(args.record); return { lost: [], record: structuredClone(session) }; }
      if (command === "repl-reset") session = { accepted: [], count: 0 };
      return {};
    },
  };
}

// The page, as proof.mjs wires it: each request sent with its deadline, from
// outside maintenance or as its own, and the console's session restored as
// maintenance. The rebuild after a failure is maintenance: a new worker,
// its check, and the session's restore.
function page() {
  const clock = fakeClock(), host = worker(), upkeep = workerMaintenance(), sent = [], expired = [];
  const request = (command, args = {}, { internal = false } = {}) => {
    const send = () => {
      sent.push({ command, args, internal, during: upkeep.busy });
      const watchdog = proofRequestWatchdog(command, () => expired.push(command), clock);
      return host.answer(command, args).finally(() => watchdog.stop());
    };
    return internal ? upkeep.internal(send) : upkeep.request(send);
  };
  const internal = (command, args) => request(command, args, { internal: true });
  const session = recordedSession(request, { generation: host.generation, restoreAfterFault: false,
    restorable: () => host.proven, maintain: work => upkeep.run(() => work(internal)) });
  const rebuild = ({ recheck = true } = {}) => upkeep.run(async () => {
    host.replace();
    if (!recheck) return [];
    await internal("check");
    return session.restore(internal);
  });
  return { clock, host, sent, expired, request, session, rebuild, commands: () => sent.map(({ command }) => command) };
}
// Nothing from outside maintenance was sent while it was under way, every
// restore was its own, and no deadline ran out.
function kept(page) {
  assert.deepEqual(page.sent.filter(({ internal, during }) => !internal && during).map(({ command }) => command), []);
  assert.deepEqual(page.sent.filter(({ command, internal, during }) => command === "repl-restore" && !(internal && during)), []);
  assert.deepEqual(page.expired, []);
}
const restarted = { kind: "info", text: "The kernel was restarted. The session's entries were checked again." };

test("a restore in the rebuild after a kernel failure: what is asked meanwhile waits, and its deadline with it", async () => {
  const p = page();
  await p.request("check");
  await p.session.run("a");
  const restore = p.host.hold("repl-restore"), rebuilt = p.rebuild();
  await tick();
  const inspection = p.request("inspect");
  await tick();
  p.clock.advance(31000);
  assert.deepEqual(p.commands(), ["check", "repl", "check", "repl-restore"]);
  restore();
  assert.deepEqual(await rebuilt, [restarted]);
  await inspection;
  assert.deepEqual(p.commands().at(-1), "inspect");
  kept(p);
});

test("a restore before an entry, once the reader's check after a failure in a check is done: the check's inspection waits", async () => {
  const p = page();
  await p.request("check");
  await p.session.run("a");
  await p.rebuild({ recheck: false });
  await assert.rejects(p.session.run("b"), /Check a proof first/);
  // The reader's check, and an entry made while it runs; the check's
  // inspection is asked when it answers.
  const check = p.host.hold("check"), restore = p.host.hold("repl-restore");
  const checked = p.request("check").then(() => p.request("inspect"));
  await tick();
  const entry = p.session.run("b");
  await tick();
  check();
  for (let i = 0; i < 5; i++) await tick();
  p.clock.advance(31000);
  assert.deepEqual(p.commands().slice(-2), ["check", "repl-restore"]);
  restore();
  assert.deepEqual(await entry, [restarted, { kind: "defined", text: "b : repl_2" }]);
  await checked;
  assert.ok(p.commands().indexOf("inspect") > p.commands().indexOf("repl-restore"));
  kept(p);
});

test("a Restart during a restore waits for it, and what comes back after is only the new session", async () => {
  const p = page();
  await p.request("check");
  await p.session.run("secret");
  const restore = p.host.hold("repl-restore"), rebuilt = p.rebuild();
  await tick();
  p.session.reset();
  const reset = p.request("repl-reset");
  await tick();
  p.clock.advance(31000);
  assert.ok(!p.commands().includes("repl-reset"));
  restore();
  assert.deepEqual(await rebuilt, []);
  await reset;
  assert.deepEqual(await p.session.run("fresh"), [{ kind: "defined", text: "fresh : repl_1" }]);
  const again = p.host.hold("repl-restore"), rebuiltAgain = p.rebuild();
  await tick();
  const inspection = p.request("inspect");
  await tick();
  p.clock.advance(31000);
  again();
  await rebuiltAgain;
  await inspection;
  assert.deepEqual(p.sent.filter(({ command }) => command === "repl-restore").at(-1).args.record,
    { accepted: [{ text: "fresh", entry: 1 }], count: 1 });
  kept(p);
});

test("a restore before an entry on a worker started for the reader's check: what is asked meanwhile waits", async () => {
  const p = page();
  await p.request("check");
  await p.session.run("a");
  // The page stopped replacing workers; the reader's check starts one.
  p.host.replace();
  await p.request("check");
  const restore = p.host.hold("repl-restore"), entry = p.session.run("b");
  await tick();
  const inspection = p.request("inspect");
  await tick();
  p.clock.advance(31000);
  assert.ok(!p.commands().includes("inspect"));
  restore();
  assert.deepEqual(await entry, [restarted, { kind: "defined", text: "b : repl_2" }]);
  await inspection;
  kept(p);
});
