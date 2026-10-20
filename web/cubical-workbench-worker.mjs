import createCubical from "./dist/cubical.mjs";
import { WorkbenchSession } from "./cubical-workbench-session.mjs";
let aborted = null;
const session = new WorkbenchSession(await createCubical({ onAbort: reason => { aborted = String(reason); } }));
self.postMessage({ ready: true });
let queue = Promise.resolve();
self.onmessage = ({ data: { id, command, args } }) => {
  queue = queue.then(async () => {
    try {
      const result = command === "load"
        ? await session.load(args, progress => self.postMessage({ id, progress }))
        : await session.handle(command, args);
      self.postMessage({ id, result });
    } catch (error) {
      const fatal = aborted !== null || error instanceof WebAssembly.RuntimeError;
      self.postMessage({ id, error: { message: aborted ?? error.message, kind: error.kind, fatal } });
      if (fatal) self.close();
    }
  });
};
