import createCubical from "./dist/cubical.mjs";
import { moduleListing } from "./module-listing.mjs";
import { listedReader } from "./module-resolution.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { ReplSession } from "./repl-session.mjs";
import { ContextualSession } from "./contextual-session.mjs";
import { elaboration } from "./cubical-elaboration.mjs";
import { generatedCubist } from "./generated-cubist.mjs";
import { moduleFault } from "./cubical-kernel.mjs";
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
  // A rechecked proof keeps the session: what extended it is replayed. A
  // replay its instance fails throws, so no part of it is installed.
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
// A check's program, installed by handle only once its reply is made: a
// check that fails, or whose reply cannot be made, leaves the proof as it
// was, as the page does.
let staged = null;
function install({ next, args, epoch }) {
  program?.dispose(); program = next; programMain = args.module ?? "current";
  // An edit or a newer submitted check invalidates these contexts even
  // when it arrived while this check was loading an import.
  if (epoch !== contextEpoch) program.scopeReady = false;
}
async function run({ data: { id, command, args } }, epoch) {
  if (command === "check") {
    const next = new CubicalProgram(module, readSource(args.module, args.place),
      { optimizations: args.optimizations, collectGeneration: true, collectScopes: !!args.collectScopes });
    try { staged = { next, args, epoch }; return await next.check(args.source, args.module ?? "current", progress => self.postMessage({ id, progress })); }
    catch (error) { staged = null; next.dispose(); throw error; }
  }
  if (command === "elaborate") {
    // A source of its own, checked apart from the proof: every declaration's
    // steps, terms and native opcode trees.
    const scratch = new CubicalProgram(module, readSource(args.module, args.place));
    try {
      await scratch.check(args.source, args.module ?? "current");
      return elaboration(scratch, args.module ?? "current");
    } finally { scratch.dispose(); }
  }
  if (command === "repl" || command === "repl-reset") return command === "repl" ? repl(args) : resetRepl();
  if (command === "context-run") return contextual(args.session).run(args.input);
  if (!program) throw new Error("Check a proof first.");
  if (command === "contexts") {
    if (!program.scopeReady) throw new Error("Check the current source with contextual scopes enabled.");
    const module = args.module ?? programMain;
    return {revision:program.scopeRevision,points:[...program.scopePoints.values()]
      .filter(point=>point.owner[1]===module||point.origin.module===module).map(contextDescription)};
  }
  if (command === "context-open") {
    const context = new ContextualSession(program,args.scope),session = `context-${++contextSerial}`;
    contexts.set(session,context);
    return {session,point:contextDescription(context.point)};
  }
  if (command === "inspect") return program.inspect(args.binding, args);
  if (command === "generation") return generatedCubist(program, args.module ?? programMain);
  // A declared type has no checked definition: its signature and eliminator.
  if (command === "signature") return program.signatureView(args.binding);
  if (command === "export-inspection") return program.export(args.binding, args.side);
  if (command === "export") return program.export();
  throw new Error("Unsupported cubical command.");
}
// Checking and queries observe submission order. Capability revocation is
// immediate and does not touch a live kernel handle.
let queue = Promise.resolve();
// A reply is made here, in full: cloned as postMessage would clone it, so
// that a part read lazily, as a check's steps, reads the kernel inside this
// boundary, and a check's program installed. A kernel instance that failed
// (KernelFault, cubical-kernel.mjs) is never entered again: the request is
// answered with the failure, marked fatal, and the worker stops. Its page
// starts a new worker (WorkerRequests), which rebuilds what the page holds.
async function handle(event, epoch) {
  const { id } = event.data;
  let reply;
  try {
    const result = structuredClone(await run(event, epoch));
    if (staged) install(staged);
    reply = { id, result };
  } catch (error) {
    staged?.next.dispose();
    try { reply = { id, error: structuredClone({ message: error.message, offset: error.offset, diagnostic: error.diagnostic }) }; }
    catch { reply = { id, error: { message: String(error?.message ?? error) } }; }
  }
  staged = null;
  const fault = moduleFault(module);
  if (fault) {
    self.postMessage({ id, error: { message: fault.message, kind: "fault", fatal: true } });
    self.close();
    return;
  }
  self.postMessage(reply);
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
