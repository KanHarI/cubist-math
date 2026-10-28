import createCubical from "./dist/cubical.mjs";
import { WorkbenchSession } from "./cubical-workbench-session.mjs";
import { moduleListing } from "./module-listing.mjs";
import { libraryProvenance } from "./module-resolution.mjs";
import { moduleFault } from "./cubical-kernel.mjs";
let aborted = null;
// A transferred module is the library's when library/ holds that text.
const fromLibrary = libraryProvenance(moduleListing, async path => {
  const response = await fetch(new URL(`./${path}`, import.meta.url), { cache: "no-store" });
  return response.ok ? response.text() : null;
});
const module = await createCubical({ onAbort: reason => { aborted = String(reason); } });
const session = new WorkbenchSession(module, { fromLibrary });
self.postMessage({ ready: true });
let queue = Promise.resolve();
// An instance that failed (KernelFault) is never entered again: the worker
// reports the failure as fatal and closes.
self.onmessage = ({ data: { id, command, args } }) => {
  queue = queue.then(async () => {
    try {
      const result = command === "load"
        ? await session.load(args, progress => self.postMessage({ id, progress }))
        : await session.handle(command, args);
      const fault = moduleFault(module);
      if (fault) throw fault;
      self.postMessage({ id, result });
    } catch (error) {
      const fault = moduleFault(module);
      const fatal = aborted !== null || error instanceof WebAssembly.RuntimeError || fault !== null;
      self.postMessage({ id, error: { message: aborted ?? fault?.message ?? error.message, kind: error.kind, fatal, trace: error.trace } });
      if (fatal) self.close();
    }
  });
};
