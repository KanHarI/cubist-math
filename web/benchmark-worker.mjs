import { benchmark } from "./benchmark-runner.mjs";

self.onmessage = async () => {
  let last = 0;
  try {
    const report = await benchmark({ onSnapshot: snapshot => {
      if (performance.now() - last < 250) return;
      last = performance.now();
      self.postMessage({ type: "progress", report: { ...snapshot, complete: false, generatedAt: new Date().toISOString() } });
    } });
    self.postMessage({ type: "complete", report: { ...report, complete: true, runtime: navigator.userAgent } });
  } catch (error) { self.postMessage({ type: "error", message: error.message }); }
};
