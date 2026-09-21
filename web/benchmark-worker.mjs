import { benchmark } from "./benchmark-runner.mjs";

self.onmessage = async ({ data: { limitMs = 100, optimizations = {} } }) => {
  let last = 0;
  try {
    const report = await benchmark({ limitMs, optimizations, onSnapshot: snapshot => {
      if (performance.now() - last < 250) return;
      last = performance.now();
      self.postMessage({ type: "progress", report: { ...snapshot, limitMs, optimizations, complete: false, generatedAt: new Date().toISOString() } });
    } });
    self.postMessage({ type: "complete", report: { ...report, complete: true, runtime: navigator.userAgent } });
  } catch (error) { self.postMessage({ type: "error", message: error.message }); }
};
