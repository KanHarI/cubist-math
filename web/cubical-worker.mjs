import createCubical from "./dist/cubical.mjs";
import { moduleListing } from "./module-listing.mjs";
import { listedReader } from "./module-resolution.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { ReplSession, restartNote } from "./repl-session.mjs";
import { ContextualSession } from "./contextual-session.mjs";
import { elaboration } from "./cubical-elaboration.mjs";
import { generatedCubist } from "./generated-cubist.mjs";
import { moduleFault } from "./cubical-kernel.mjs";
// The kernel's instance. One that failed is replaced (recover).
let module = await createCubical();
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
const freshProgram = () => new CubicalProgram(module, readSource(), { collectReferences: false });
async function repl({ input, fresh }) {
  if (fresh) {
    if (!sessionProgram) {
      sessionProgram = freshProgram();
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
// The contexts open on the current program, closed.
function closeContexts() {
  for (const context of contexts.values()) context.dispose();
  contexts.clear();
}
// An edit or a submitted check: the contexts close, and a check already
// running when it came no longer opens its scopes (contextEpoch).
function invalidateContexts() {
  contextEpoch++;
  closeContexts();
  if (program) program.scopeReady = false;
}
function contextual(id) {
  const context = contexts.get(id);
  if (!context) throw new Error("This contextual session is stale or closed. Select a context from the current check.");
  return context;
}
// The proof's check on the current instance, and the last one that
// completed, to check again on a new instance.
let checked = null;
async function checkProof(args, onProgress = () => {}) {
  const next = new CubicalProgram(module, readSource(args.module, args.place),
    { optimizations: args.optimizations, collectGeneration: true, collectScopes: !!args.collectScopes });
  try { return { next, result: await next.check(args.source, args.module ?? "current", onProgress) }; }
  catch (error) { next.dispose(); throw error; }
}
// An instance that failed is never entered again (guardModule in
// cubical-kernel.mjs): what was built on it is dropped, and built again on a
// new instance. The proof is checked again, unless its own check failed, and
// a REPL session replays the entries that extended it, each as the entry it
// was (ReplSession.rebase). The contexts open on the old program close.
// Contextual scopes stay as they were: revoked ones stay revoked, and a
// revocation during the rebuild holds, as during a check; the rebuild is no
// edit, so it revokes nothing itself, not even a check queued behind it. If
// the new instance fails too, nothing is built on it. Returns what was
// restored, and what not, to say (restartNote).
async function recover() {
  const scopes = program?.scopeReady === true;
  closeContexts();
  const epoch = contextEpoch, source = checked ? "The proof" : null;
  const replayed = session, fresh = session !== null && session.program === sessionProgram;
  program = sessionProgram = session = null;
  module = await createCubical();
  let rechecked = null;
  try {
    if (checked) ({ next: program, result: rechecked } = await checkProof(checked));
    if (replayed && fresh) session = await replayed.rebase(sessionProgram = freshProgram());
    else if (replayed && program) session = await replayed.rebase(program, programMain);
  } catch { /* a failure here is the new instance's, read below */ }
  if (moduleFault(module)) {
    program = sessionProgram = session = checked = rechecked = null;
    module = await createCubical();
  }
  if (program) program.scopeReady &&= scopes && epoch === contextEpoch;
  return restartNote({ source, rechecked, replayed: replayed !== null, session });
}
async function run({ data: { id, command, args } }, epoch) {
  if (command === "check") {
    const { next, result } = await checkProof(args, progress => self.postMessage({ id, progress }));
    program?.dispose(); program = next; programMain = args.module ?? "current"; checked = args;
    // An edit or a newer submitted check invalidates these contexts even
    // when it arrived while this check was loading an import.
    if (epoch !== contextEpoch) program.scopeReady = false;
    return result;
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
// A reply is cloned here, as postMessage would clone it: a part read lazily,
// as a check's steps, reads the kernel when it is cloned, and is read inside
// this boundary, where a failure is caught and the instance replaced, never
// by postMessage after it.
async function handle(event, epoch) {
  const { id, command } = event.data, instance = module;
  let reply;
  try { reply = { id, result: structuredClone(await run(event, epoch)) }; }
  catch (error) {
    try { reply = { id, error: structuredClone({ message: error.message, offset: error.offset, diagnostic: error.diagnostic }) }; }
    catch { reply = { id, error: { message: String(error?.message ?? error) } }; }
  }
  const fault = moduleFault(instance);
  if (fault) {
    if (command === "check") checked = null;
    const note = await recover();
    // A REPL entry's results end at the statement that failed, which says
    // so; any other command's result is dropped for the failure. Either way
    // the reply says what the replacement restored.
    if (command === "repl" && reply.result) reply.result = [...reply.result, { kind: "info", text: note }];
    else reply = { id, error: { message: `${fault.message} ${note}` } };
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
