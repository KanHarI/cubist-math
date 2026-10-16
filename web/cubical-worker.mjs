import createCubical from "./dist/cubical.mjs";
import { moduleListing } from "./module-listing.mjs";
import { listedReader } from "./module-resolution.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { ReplSession } from "./repl-session.mjs";
import { ContextualSession } from "./contextual-session.mjs";
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
const contexts = new Map();
let contextSerial = 0, contextEpoch = 0;
const contextDescription = ({state,lexical,...point}) => point;
function invalidateContexts() {
  contextEpoch++;
  for (const context of contexts.values()) context.dispose();
  contexts.clear();
  if (program) program.scopeReady = false;
}
function contextual(id) {
  const context = contexts.get(id);
  if (!context) throw new Error("This contextual session is stale or closed. Select a context from the current check.");
  return context;
}
// Checking and queries observe submission order. Capability revocation is
// immediate and does not touch a live kernel handle.
let queue = Promise.resolve();
async function handle({ data: { id, command, args } }, epoch) {
  try {
    let result;
    if (command === "check") {
      const next = new CubicalProgram(module, readSource(args.module, args.place),
        { optimizations: args.optimizations, collectGeneration: true, collectScopes: !!args.collectScopes });
      try { result = await next.check(args.source, args.module ?? "current", progress => self.postMessage({ id, progress })); }
      catch (error) { next.dispose(); throw error; }
      program?.dispose(); program = next; programMain = args.module ?? "current";
      // An edit or a newer submitted check invalidates these contexts even
      // when it arrived while this check was loading an import.
      if (epoch !== contextEpoch) program.scopeReady = false;
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
    } else if (command === "context-run") {
      result = await contextual(args.session).run(args.input);
    } else if (!program) throw new Error("Check a proof first.");
    else if (command === "contexts") {
      if (!program.scopeReady) throw new Error("Check the current source with contextual scopes enabled.");
      const module = args.module ?? programMain;
      result = {revision:program.scopeRevision,points:[...program.scopePoints.values()]
        .filter(point=>point.owner[1]===module||point.origin.module===module).map(contextDescription)};
    } else if (command === "context-open") {
      const context = new ContextualSession(program,args.scope),session = `context-${++contextSerial}`;
      contexts.set(session,context);
      result = {session,point:contextDescription(context.point)};
    }
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
  // This revokes only contextual capabilities, never a live kernel handle.
  // Queries loading asynchronously notice disposal before returning a result.
  const {id,command,args}=event.data;
  if (["check","context-invalidate"].includes(command)) invalidateContexts();
  if (command === "context-close") {
    contexts.get(args.session)?.dispose(); contexts.delete(args.session);
  }
  if (["context-invalidate","context-close"].includes(command)) {
    self.postMessage({id,result:undefined});return;
  }
  const epoch = contextEpoch;
  const run = queue.then(() => handle(event,epoch));
  queue = run.catch(() => {});
  return run;
};
