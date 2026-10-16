import createCubical from "./dist/cubical.mjs";
import { moduleListing } from "./module-listing.mjs";
import { listedReader } from "./module-resolution.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { ReplSession } from "./repl-session.mjs";
import { elaboration } from "./cubical-elaboration.mjs";
import { generatedCubist } from "./generated-cubist.mjs";
const module = await createCubical();
// What import can load, for the REPL's /modules.
const importable = async () => moduleListing;
let program = null;
// Imports resolve as in the CLI (module-resolution.mjs): a proof of the archive
// imports only from the archive; a library proof, the workspace, the REPL and
// reference examples import library-first. Each program has its own reader,
// and a page that loaded its source from a root says so in `place`.
const readSource = (main = null, place = null) => listedReader(moduleListing, async path => {
  const response = await fetch(new URL(`./${path}`, import.meta.url), { cache: "no-store" });
  if (!response.ok) throw new Error(`Native source is not available at ${path}.`);
  return response.text();
}, main, place);
self.postMessage({ ready: true, backend: "cubical" });
// A REPL session runs over the checked proof, or over its own program when
// the page has no proof (the REPL page and the reference pages).
let session = null, sessionProgram = null, programMain = null;
async function repl({ input, fresh }) {
  if (fresh) {
    if (!sessionProgram) {
      sessionProgram = new CubicalProgram(module, readSource(), { collectReferences: false });
      session = new ReplSession(sessionProgram, { modules: importable });
    }
  } else if (!program) throw new Error("Check a proof first.");
  else if (!session) session = new ReplSession(program, { base: programMain, modules: importable });
  // A rechecked proof keeps the session: what extended it is replayed.
  else if (session.program !== program) session = await session.rebase(program, programMain);
  return session.run(input);
}
function resetRepl() {
  sessionProgram?.dispose();
  sessionProgram = null;
  session = null;
}
// Every request observes submission order. A recheck cannot replace the
// program beneath a query, and older checks cannot publish after newer ones.
let queue = Promise.resolve();
async function handle({ data: { id, command, args } }) {
  try {
    let result;
    if (command === "check") {
      const next = new CubicalProgram(module, readSource(args.module, args.place),
        { optimizations: args.optimizations, collectGeneration: true });
      try { result = await next.check(args.source, args.module ?? "current", progress => self.postMessage({ id, progress })); }
      catch (error) { next.dispose(); throw error; }
      program?.dispose(); program = next; programMain = args.module ?? "current";
    } else if (command === "elaborate") {
      // A source of its own, checked apart from the proof: every declaration's
      // steps, terms and native opcode trees.
      const scratch = new CubicalProgram(module, readSource(args.module, args.place));
      try {
        await scratch.check(args.source, args.module ?? "current");
        result = elaboration(scratch, args.module ?? "current");
      } finally { scratch.dispose(); }
    } else if (command === "repl" || command === "repl-reset") {
      result = await (command === "repl" ? repl(args) : resetRepl());
    } else if (!program) throw new Error("Check a proof first.");
    else if (command === "inspect") result = program.inspect(args.binding, args);
    else if (command === "generation") result = generatedCubist(program, args.module ?? programMain);
    // A declared type has no checked definition: its signature and eliminator.
    else if (command === "signature") result = program.signatureView(args.binding);
    else if (command === "export-inspection") result = program.export(args.binding, args.side);
    else if (command === "export") result = program.export();
    else throw new Error("Unsupported cubical command.");
    self.postMessage({ id, result });
  } catch (error) { self.postMessage({ id, error: { message: error.message, offset: error.offset } }); }
}
self.onmessage = event => {
  const run = queue.then(() => handle(event));
  queue = run.catch(() => {});
  return run;
};
