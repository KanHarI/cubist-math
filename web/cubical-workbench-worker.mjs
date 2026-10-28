import createCubical from "./dist/cubical.mjs";
import { WorkbenchSession } from "./cubical-workbench-session.mjs";
import { moduleListing } from "./module-listing.mjs";
import { archiveProvenance, libraryProvenance } from "./module-resolution.mjs";
let aborted = null;
// A transferred module is the library's when library/ holds that text, and
// the archive's when the archive does.
const fetchText = async path => {
  const response = await fetch(new URL(`./${path}`, import.meta.url), { cache: "no-store" });
  return response.ok ? response.text() : null;
};
const fromLibrary = libraryProvenance(moduleListing, fetchText), fromArchive = archiveProvenance(moduleListing, fetchText);
const session = new WorkbenchSession(await createCubical({ onAbort: reason => { aborted = String(reason); } }), { fromLibrary, fromArchive });
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
      self.postMessage({ id, error: { message: aborted ?? error.message, kind: error.kind, fatal, trace: error.trace } });
      if (fatal) self.close();
    }
  });
};
