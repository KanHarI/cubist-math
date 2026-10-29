// Request transport only: each caller still owns its worker and program.
export class WorkerRequests {
  #pending = new Map();
  #serial = 0;
  #stopped = null;
  #rejectReady;
  constructor(worker, { onError = () => {} } = {}) {
    this.worker = worker;
    let ready;
    this.ready = new Promise((resolve, reject) => { ready = resolve; this.#rejectReady = reject; });
    // A worker can fail before its owner submits a request.
    this.ready.catch(() => {});
    worker.onmessage = ({ data }) => {
      if (this.#stopped) return;
      if (data.ready) { ready(); return; }
      const waiting = this.#pending.get(data.id);
      if (!waiting) return;
      if (data.progress) { waiting.progress?.(data.progress); return; }
      this.#pending.delete(data.id);
      if (!data.error) { waiting.resolve(data.result); return; }
      const error = Object.assign(new Error(data.error.message), data.error, { command: waiting.command });
      waiting.reject(error);
      // A fatal reply: the worker's kernel instance failed, and the worker
      // stopped. Every other request fails with it, and the owner starts a
      // new worker if it will (onError, with error.fatal set).
      if (error.fatal) { this.terminate(error); onError(error); }
    };
    worker.onerror = event => {
      if (this.#stopped) return;
      const error = new Error(event.message || "Unable to load the checking worker. Build with make wasm.");
      this.terminate(error);
      onError(error);
    };
  }
  get pendingCount() { return this.#pending.size; }
  request(command, args = {}, progress) {
    if (this.#stopped) return Promise.reject(this.#stopped);
    const id = ++this.#serial;
    return new Promise((resolve, reject) => {
      this.#pending.set(id, { command, resolve, reject, progress });
      this.ready.then(() => {
        if (!this.#pending.has(id)) return;
        try { this.worker.postMessage({ id, command, args }); }
        catch (error) { this.#pending.delete(id); reject(error); }
      }, () => {}); // terminate already rejects requests waiting for readiness.
    });
  }
  terminate(error = new Error("The checking worker is unavailable. Reload the page to restart it.")) {
    if (this.#stopped) return;
    this.#stopped = error;
    this.#rejectReady(error);
    this.worker.terminate();
    this.worker.onmessage = this.worker.onerror = null;
    for (const waiting of this.#pending.values()) waiting.reject(error);
    this.#pending.clear();
  }
}
