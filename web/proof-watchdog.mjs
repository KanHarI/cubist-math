// Long checks may continue while the worker reports advancing counters.
// Repeated heartbeats do not extend a stalled request's deadline.
export function proofRequestWatchdog(command, onTimeout, clock = globalThis) {
  const duration = command === "check" ? 300000 : 30000;
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
    progress(value) {
      if (stopped || command !== "check") return;
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
