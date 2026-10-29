import createCubical from "./dist/cubical.mjs";
import { WorkbenchSession } from "./cubical-workbench-session.mjs";
import { moduleListing } from "./module-listing.mjs";
import { archiveProvenance, libraryProvenance } from "./module-resolution.mjs";
import { moduleFault } from "./cubical-kernel.mjs";
let aborted = null;
// A transferred module is the library's when library/ holds that text, and
// the archive's when the archive does.
const fetchText = async path => {
  const response = await fetch(new URL(`./${path}`, import.meta.url), { cache: "no-store" });
  return response.ok ? response.text() : null;
};
const fromLibrary = libraryProvenance(moduleListing, fetchText), fromArchive = archiveProvenance(moduleListing, fetchText);
const module = await createCubical({ onAbort: reason => { aborted = String(reason); } });
const session = new WorkbenchSession(module, { fromLibrary, fromArchive });
self.postMessage({ ready: true });
let queue = Promise.resolve();
// An instance that failed (KernelFault) is never entered again: the worker
// reports the failure as fatal and closes. A reply is cloned before it is
// sent, as in cubical-worker.mjs, so that nothing it holds reads the kernel
// after this check.
self.onmessage = ({ data: { id, command, args } }) => {
  queue = queue.then(async () => {
    let reply, trapped = false;
    try {
      reply = { id, result: structuredClone(command === "load"
        ? await session.load(args, progress => self.postMessage({ id, progress }))
        : await session.handle(command, args)) };
    } catch (error) {
      trapped = error instanceof WebAssembly.RuntimeError;
      try { reply = { id, error: structuredClone({ message: error.message, kind: error.kind, trace: error.trace }) }; }
      catch { reply = { id, error: { message: String(error?.message ?? error) } }; }
    }
    const fault = moduleFault(module), fatal = aborted !== null || trapped || fault !== null;
    if (fatal) reply = { id, error: { ...reply.error, message: aborted ?? fault?.message ?? reply.error.message, fatal } };
    self.postMessage(reply);
    if (fatal) self.close();
  });
};
