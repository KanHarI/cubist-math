import test from "node:test";
import assert from "node:assert/strict";
import { WorkerRequests } from "../web/worker-requests.mjs";

function worker() {
  return { sent: [], stopped: false,
    postMessage(data) { this.sent.push(data); },
    receive(data) { this.onmessage?.({ data }); },
    terminate() { this.stopped = true; },
  };
}

test("requests wait for readiness, track progress and preserve structured errors", async () => {
  const native = worker(), client = new WorkerRequests(native), progress = [];
  const first = client.request("check", { source: "def x := tt;" }, update => progress.push(update));
  const second = client.request("inspect", { name: "x" });
  const refused = assert.rejects(second, { message: "refused", code: "E606", offset: 12 });
  assert.equal(client.pendingCount, 2);
  assert.deepEqual(native.sent, []);
  native.receive({ ready: true });
  await client.ready;
  assert.deepEqual(native.sent, [
    { id: 1, command: "check", args: { source: "def x := tt;" } },
    { id: 2, command: "inspect", args: { name: "x" } },
  ]);
  native.receive({ id: 1, progress: { completed: 1 } });
  assert.deepEqual(progress, [{ completed: 1 }]);
  assert.equal(client.pendingCount, 2);
  native.receive({ id: 2, error: { message: "refused", code: "E606", offset: 12 } });
  native.receive({ id: 1, result: "checked" });
  assert.equal(await first, "checked");
  await refused;
  assert.equal(client.pendingCount, 0);
});

test("startup and running failures settle all requests and reject later requests", async () => {
  for (const ready of [false, true]) {
    const native = worker(), errors = [], client = new WorkerRequests(native, { onError: e => errors.push(e) });
    if (ready) { native.receive({ ready: true }); await client.ready; }
    const first = assert.rejects(client.request("check"), /startup failed/);
    const second = assert.rejects(client.request("inspect"), /startup failed/);
    if (ready) { await Promise.resolve(); assert.equal(native.sent.length, 2); }
    native.onerror({ message: "startup failed" });
    await Promise.all([first, second]);
    if (!ready) await assert.rejects(client.ready, /startup failed/);
    assert.equal(native.stopped, true);
    assert.equal(client.pendingCount, 0);
    assert.equal(errors.length, 1);
    await assert.rejects(client.request("repl"), /startup failed/);
  }
});

test("a startup failure without a message retains the build instruction", async () => {
  const native = worker(), client = new WorkerRequests(native);
  const request = assert.rejects(client.request("check"), /Build with make wasm\./);
  native.onerror({});
  await request;
});

test("termination isolates replacement workers from late replies with reused request IDs", async () => {
  const oldNative = worker(), oldClient = new WorkerRequests(oldNative);
  const reply = oldNative.onmessage;
  const oldRequest = assert.rejects(oldClient.request("check"), /cancelled/);
  oldClient.terminate(new Error("cancelled"));
  await oldRequest;
  reply({ data: { ready: true } });
  assert.deepEqual(oldNative.sent, []);
  const native = worker(), client = new WorkerRequests(native);
  native.receive({ ready: true });
  const current = client.request("repl");
  await client.ready;
  reply({ data: { id: 1, result: "stale" } });
  assert.equal(client.pendingCount, 1);
  native.receive({ id: 1, result: "current" });
  assert.equal(await current, "current");
});

test("a message that cannot be posted releases its pending request", async () => {
  const native = worker(), client = new WorkerRequests(native);
  native.postMessage = () => { throw new Error("cannot clone"); };
  native.receive({ ready: true });
  await assert.rejects(client.request("check"), /cannot clone/);
  assert.equal(client.pendingCount, 0);
});

// A fatal reply: the worker's kernel instance failed and the worker stopped.
// The request and every other one fail with it, the transport stops, and
// its owner hears of it, with the command that failed.
test("a fatal reply fails every request and stops the transport", async () => {
  const native = worker(), errors = [], client = new WorkerRequests(native, { onError: error => errors.push(error) });
  native.receive({ ready: true });
  await client.ready;
  const failed = client.request("inspect", { binding: "x" }), queued = client.request("signature", { binding: "T" });
  native.receive({ id: 1, error: { message: "The kernel failed.", kind: "fault", fatal: true } });
  await assert.rejects(failed, { message: "The kernel failed.", fatal: true, command: "inspect" });
  await assert.rejects(queued, { message: "The kernel failed.", fatal: true });
  assert.equal(native.stopped, true);
  assert.equal(errors.length, 1);
  assert.equal(errors[0].command, "inspect");
  await assert.rejects(client.request("check"), /The kernel failed/);
});
