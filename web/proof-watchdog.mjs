// Long checks may continue while the worker reports advancing counters.
// Repeated heartbeats do not extend a stalled request's deadline.
export function proofRequestWatchdog(command, onTimeout, clock = globalThis) {
  // A REPL entry is checked like a small file, and may evaluate at length.
  let duration = ["check", "repl", "context-run"].includes(command) ? 300000 : 30000;
  let checking = command === "check";
  let timer;
  let instructions = 0;
  let completed = 0;
  let stopped = false;
  function arm() {
    clock.clearTimeout(timer);
    timer = clock.setTimeout(() => {
      stopped = true;
      onTimeout();
    }, duration);
  }
  arm();
  return {
    // The worker replaces a failed kernel instance before it answers, and
    // checks the proof again: from here on the request is watched as a check.
    recovering() {
      if (stopped) return;
      checking = true; duration = 300000; instructions = completed = 0;
      arm();
    },
    progress(value) {
      if (stopped || !checking) return;
      const nextInstructions = value.instructions ?? 0;
      const nextCompleted = value.completed ?? 0;
      if (nextInstructions > instructions || nextCompleted > completed) {
        instructions = Math.max(instructions, nextInstructions);
        completed = Math.max(completed, nextCompleted);
        arm();
      }
    },
    stop() {
      stopped = true;
      clock.clearTimeout(timer);
    },
  };
}
