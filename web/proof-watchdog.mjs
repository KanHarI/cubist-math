// Every command the worker answers (web/cubical-worker.mjs) is checking
// work, which checks source as a file is checked and may load imports and
// evaluate at length, or a query of what was checked. Checking work has five
// minutes, a query thirty seconds. A REPL entry, a session's restore on a
// new worker, a contextual entry and a scratch elaboration are checking work.
export const checkingCommands = new Set(["check", "elaborate", "repl", "repl-restore", "context-run"]);
export const queryCommands = new Set(["repl-reset", "contexts", "context-open", "context-close", "context-invalidate",
  "inspect", "generation", "signature", "export-inspection", "export"]);
// Long checks may continue while the worker reports advancing counters.
// Repeated heartbeats do not extend a stalled request's deadline.
export function proofRequestWatchdog(command, onTimeout, clock = globalThis) {
  const duration = checkingCommands.has(command) ? 300000 : 30000;
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
