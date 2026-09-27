import { cubicalSourceFile } from "./cubical-sources.mjs";
import createCubical from "./dist/cubical.mjs";
import { sourceModules, cubicalSourceModules, libraryModules } from "./mathscript/modules.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { ReplSession } from "./repl-session.mjs";
import { elaboration } from "./cubical-elaboration.mjs";
const module = await createCubical();
// What import can load, for the REPL's /modules.
const importable = async () => ({ library: libraryModules, archive: [...sourceModules, ...cubicalSourceModules] });
let program = null;
const readSource = async name => {
  if (!/^[A-Za-z_][A-Za-z_0-9]*$/.test(name)) throw new Error("Invalid source module name.");
  const library = libraryModules.includes(name);
  if (!library && ![...sourceModules, ...cubicalSourceModules].includes(name))
    throw new Error(`Native source is not available for ${name}.`);
  const path = library ? `./library/${name}.cubist` : `./archive/first-library/${cubicalSourceFile(name)}`;
  const response = await fetch(new URL(path, import.meta.url), { cache: "no-store" });
  if (!response.ok) throw new Error(`Native source is not available for ${name}.`);
  return response.text();
};
self.postMessage({ ready: true, backend: "cubical" });
// A REPL session runs over the checked proof, or over its own program when
// the page has no proof (the REPL page and the reference pages).
let session = null, sessionProgram = null, programMain = null;
async function repl({ input, fresh }) {
  if (fresh) {
    if (!sessionProgram) {
      sessionProgram = new CubicalProgram(module, readSource, { collectReferences: false });
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
// REPL entries run one at a time, after any check in progress; a check
// waits for the entries already running before it disposes their program.
let checking = Promise.resolve(), replQueue = Promise.resolve();
self.onmessage = async ({ data: { id, command, args } }) => {
  try {
    let result;
    if (command === "check") {
      const replBefore = replQueue;
      const run = (async () => {
        const next = new CubicalProgram(module, readSource, { optimizations: args.optimizations });
        let checked;
        try { checked = await next.check(args.source, args.module ?? "current", progress => self.postMessage({ id, progress })); }
        catch (error) { next.dispose(); throw error; }
        await replBefore;
        program?.dispose(); program = next; programMain = args.module ?? "current";
        return checked;
      })();
      checking = run.catch(() => {});
      result = await run;
    } else if (command === "elaborate") {
      // A source of its own, checked apart from the proof: every declaration's
      // steps, terms and native opcode trees.
      const scratch = new CubicalProgram(module, readSource);
      try {
        await scratch.check(args.source, args.module ?? "current");
        result = elaboration(scratch, args.module ?? "current");
      } finally { scratch.dispose(); }
    } else if (command === "repl" || command === "repl-reset") {
      const run = replQueue.then(async () => {
        await checking;
        return command === "repl" ? repl(args) : resetRepl();
      });
      replQueue = run.catch(() => {});
      result = await run;
    } else if (!program) throw new Error("Check a proof first.");
    else if (command === "inspect") result = program.inspect(args.binding, args);
    else if (command === "export-inspection") result = program.export(args.binding, args.side);
    else if (command === "export") result = program.export();
    else throw new Error("Unsupported cubical command.");
    self.postMessage({ id, result });
  } catch (error) { self.postMessage({ id, error: { message: error.message, offset: error.offset } }); }
};
