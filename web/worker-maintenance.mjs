// What a page does on its checking worker for itself, as against what it
// asks for the reader: building again on a new worker what it held after a
// kernel failure stopped the old one, and restoring a console's session
// there (recordedSession in repl-console.mjs). Maintenance runs one piece
// at a time, in the order asked, each once the requests already sent have
// settled, so that it has the worker to itself; its own requests it sends at
// once. Every other request waits until no maintenance is under way or
// asked for, and only then is sent, so that its deadline
// (proofRequestWatchdog), which starts when it is sent, never runs behind
// maintenance. `onIdle` is told when the last maintenance ends.
export function workerMaintenance({ onIdle = () => {} } = {}) {
  let gate = null;
  const sent = new Set();
  // A request sent, kept until it settles.
  const track = result => {
    sent.add(result);
    result.then(() => sent.delete(result), () => sent.delete(result));
    return result;
  };
  const request = send => gate ? gate.then(() => request(send)) : track(send());
  return {
    get busy() { return gate !== null; },
    // Run `work` as maintenance, and answer what it answers.
    run(work) {
      const done = (gate ?? Promise.resolve()).then(() => Promise.allSettled([...sent])).then(() => work());
      const settled = done.then(() => {}, () => {}).then(() => {
        if (gate !== settled) return;
        gate = null;
        onIdle();
      });
      gate = settled;
      return done;
    },
    // A request from outside maintenance: sent by `send` once none is under
    // way or asked for.
    request,
    // A request of maintenance: sent at once.
    internal(send) { return track(send()); },
    // Settles once no maintenance is under way or asked for.
    async idle() { while (gate) await gate; },
  };
}
