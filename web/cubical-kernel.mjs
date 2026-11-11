// Integer-handle interface to the C kernel, usable in a browser worker or
// Node. Building syntax never certifies it: only an instruction derives a
// judgement (web/cubical-instructions.mjs).
import { EntryNames, UNNAMED, carryBinderNames } from "./cubical-variables.mjs";
// A term kind's name at its number. null marks a retired kind whose number
// stays reserved, the named variable's of ABI 3, Nat's, W's and pushouts'
// (kernel/include/cubical_kernel.h). A variable is Bound, by de Bruijn index,
// or Context, by its entry's id (ABI 4).
export const cubicalKinds = [
  "", "U", null, "Pi", "Lam", "App", "Sigma", "Pair", "Fst", "Snd",
  null, null, null, null, "Unit", "Point", "Path", "PLam", "PApp",
  "Comp", "Tube", "Void", "Abort", null, null, null, "Sum", "Inl", "Inr",
  "SumRec", "UnitRec", "Glue", "GlueSystem", "GlueTerm", "Unglue", "DefRef",
  null, null, null, null, null,
  "HComp", "Trans",
  "LBound", "LConst", "LSucc", "LMax", "LPi", "LLam", "LApp",
  "Sort", "Con", "Elim", "List",
  "Bound", "Context",
];
// The syntax encoding this code is written for (CC_KERNEL_ABI_VERSION in
// kernel/include/cubical_kernel.h). Version 2 keeps a universe's level in a
// level child rather than its payload; version 3 adds the declared-type kinds;
// version 4 refers to a variable by its role, a binder's index or an entry's
// id, and keeps no names.
export const CUBICAL_ABI_VERSION = 4;
// The most kernel steps one query may take, after its budget has doubled from
// the session's (10M by default) on each exhaustion: a hard, declared limit.
export const MAX_QUERY_STEPS = 1280000000n;

// A rejected kernel request. `kind` classifies it, from cc_error_kind, so no
// caller needs to read the message: "mismatch" (a type is not convertible to
// the expected one), "budget", "deadline" or "resource" (no judgement was made), "other".
// A mismatch also carries `mismatch`, the handles of the type found and the
// type expected; they are valid until the next rollback.
const errorKinds = ["none", "mismatch", "budget", "deadline", "other", "resource"];
// A rejection is an answer the search reads, thousands of times a module;
// its message says why, and a stack trace, which each would capture, says
// only where the kernel was asked.
export class KernelError extends Error {
  constructor(message, kind = "other") {
    const limit = Error.stackTraceLimit;
    Error.stackTraceLimit = 0;
    try { super(message); } finally { Error.stackTraceLimit = limit; }
    this.kind = kind;
  }
}

// An exception out of a kernel export is never the kernel's answer, which
// the export returns: the engine ran out of its own stack (a RangeError), or
// the instance trapped (a WebAssembly.RuntimeError). It unwound the kernel's
// C frames without running them to their end, so the instance's memory may
// be half changed, and its stack pointer was not restored. guardModule makes
// the instance's first such failure its last: no call enters it again, and
// each throws this. Whoever owns the module replaces it.
const faultMessage = cause => `The kernel's WebAssembly instance failed (${cause?.message ?? cause}), and is not used again: nothing computed after the failure is kept.`;
export class KernelFault extends Error {
  constructor(cause) {
    super(faultMessage(cause), { cause });
    this.kind = "fault";
  }
}
// Each guarded instance's state, { failed, cause }: whether it failed, and
// with what. One object per instance, shared by everything that holds it.
const instances = new WeakMap();
// The state of a module's instance, for a reader that outlives a call, as a
// runtime query does: it reads `failed` before going on.
export const faultToken = module => instances.get(guardModule(module));
// A KernelFault for the failure that ended a module instance, or null.
export const moduleFault = module => {
  const state = instances.get(module);
  return state?.failed ? new KernelFault(state.cause) : null;
};
// Whether a value reaches the instance as an argument without throwing. The
// bridge's exports take 32-bit integers and doubles (wasm/cubical_bridge.c),
// and converting any primitive but a BigInt or a Symbol to one cannot throw;
// an object's conversion runs its own code. So an exception out of a call
// whose arguments all pass came from the instance, or from the engine
// refusing to enter it for want of stack, and either ends the instance.
const enters = value => {
  const type = typeof value;
  return type !== "bigint" && type !== "symbol" && type !== "function" && (type !== "object" || value === null);
};
// Wrap each export of a module instance, once, so that an exception poisons
// the instance before it reaches any caller. An argument that could not be
// converted is refused before the call, and poisons nothing. Every caller
// calls an export through the module object, as CubicalKernel and the
// instruction graph do.
export function guardModule(module) {
  if (instances.has(module)) return module;
  const state = { failed: false, cause: null };
  instances.set(module, state);
  for (const name of Object.keys(module)) {
    const call = module[name];
    if (!name.startsWith("_cb_") || typeof call !== "function") continue;
    module[name] = (...args) => {
      if (state.failed) throw new KernelFault(state.cause);
      if (!args.every(enters)) throw new TypeError(`The kernel export ${name} takes numbers.`);
      try { return call(...args); }
      catch (error) {
        Object.assign(state, { failed: true, cause: error });
        throw new KernelFault(error);
      }
    };
  }
  return module;
}

function uint32(value, label) {
  if (!Number.isInteger(value) || value < 0 || value > 0xffffffff)
    throw new TypeError(`${label} must be an unsigned 32-bit integer.`);
  return value;
}

// What the driver keeps by node handle, with the handles a declaration made
// noted apart: those from its checkpoint's first node on, which its commit
// moves and its rollback drops (CubicalDeclarationTransaction.finish). So a
// declaration's end walks the handles it made, not all the session holds.
class HandleMap extends Map {
  #from = Infinity;
  #made = new Set();
  set(handle, value) {
    if (handle >= this.#from) this.#made.add(handle);
    return super.set(handle, value);
  }
  // A declaration's checkpoint, whose first node is `from`.
  checkpoint(from) { this.#from = from; this.#made.clear(); }
  // Its end: each handle it made goes, and at a commit comes back where the
  // kernel relocates it (`relocated`, 0 for a node the commit drops), with
  // the same value, unless another value is kept there.
  finish(relocated = null) {
    const moved = [...this.#made].filter(handle => this.has(handle)).map(handle => [handle, this.get(handle)]);
    for (const [handle] of moved) this.delete(handle);
    this.#from = Infinity; this.#made.clear();
    if (relocated) for (const [handle, value] of moved) {
      const kept = relocated(handle);
      if (kept && !this.has(kept)) super.set(kept, value);
    }
  }
}
// The driver's names of binder nodes (web/cubical-variables.mjs, binderName).
// A binder the kernel built goes by UNNAMED, and is shown by it or by a
// variant apart from what it would capture, until an encoding of the same
// node names it, which may come after a decoding showed it. Naming it
// UNNAMED changes no decoding, and naming it by the one name it was shown
// by changes none either, as that name captures nothing where it was shown:
// so each binder shown unnamed is noted with the name it was shown by
// (`shownUnnamed`, SHOWN_APART for more than one), and naming one otherwise
// moves `epoch`, at which the codec drops the decodings it kept that show a
// binder unnamed (CubicalSyntax.decode). A relocated name names a new node,
// none of them shown yet (HandleMap.finish).
const SHOWN_APART = null;
class BinderNames extends HandleMap {
  set(handle, name) {
    const shown = this.shownUnnamed.get(handle);
    if (shown !== undefined) {
      this.shownUnnamed.delete(handle);
      if (name !== UNNAMED && name !== shown) this.epoch++;
    }
    return super.set(handle, name);
  }
  shown(handle, name) {
    if (this.has(handle)) return;
    const before = this.shownUnnamed.get(handle);
    this.shownUnnamed.set(handle, before === undefined || before === name ? name : SHOWN_APART);
  }
  shownUnnamed = new HandleMap();
  epoch = 0;
}

export class CubicalKernel {
  constructor(module) {
    guardModule(module);
    const version = module._cb_abi_version?.();
    if (version !== CUBICAL_ABI_VERSION)
      throw new Error(`The cubical kernel module encodes syntax as ABI version ${version ?? 1}, `
        + `but this code expects version ${CUBICAL_ABI_VERSION}. Rebuild it with \`make wasm\`.`);
    if (!module._cb_generation) throw new Error("This cubical kernel module has no handle generations. Rebuild it with `make wasm`.");
    this.module = module;
    this.handle = module._cb_new();
    if (!this.handle) throw new KernelError("Could not allocate cubical kernel session.", "resource");
    // Names and the numbers the driver keys them by: its own, since the kernel
    // keeps no names (ABI 4).
    this.names = new Map();
    this.symbolNames = new Map();
    // The name each binder node was encoded with, by its handle: the source's
    // name, which decoding shows (web/cubical-syntax.mjs). The first encoding
    // of a handle names it. A declaration's commit relocates them, and its
    // rollback drops those of nodes made since its checkpoint
    // (CubicalDeclarationTransaction.finish).
    this.binderNames = new BinderNames();
    // The name each binder's entries are chosen by, fixed at its first use
    // (web/cubical-variables.mjs, binderKey), and the serial of the keys of
    // binders the kernel built.
    this.binderKeys = new HandleMap();
    this.binderKeySerial = 0;
    // What node(id) read of each node: nodes do not change, but a
    // declaration's commit or rollback moves them, so the transaction that
    // ends one forgets these (forgetNodes).
    this.nodes = new Map(); this.settledNodes = new Map();
    // Handles below this bound keep their places through a declaration's
    // commit or rollback, which compacts or drops only the nodes made after
    // its checkpoint (kernel/src/checkpoint.c): what is read of them is
    // kept from one declaration to the next (forgetNodes).
    this.settled = 0;
    this.nextSymbol = 1;
    this.stepBudget = 10000000n;
    // The most steps one query may grow to (withGrowingBudget).
    this.maxQuerySteps = MAX_QUERY_STEPS;
    this.definitions = new Map();
    // Each definition's name by its index in the kernel's table, the payload
    // of every CC_DEFREF that refers to it, which a commit keeps and a
    // rollback frees (nameDefinition). The kernel's own names are not read.
    this.definitionNames = new Map();
    // Admitted signatures of declared types (H1), by name: each record's
    // kernel index, constructor names and normal form in source terms
    // (web/cubical-signatures.mjs), and the records by index. A rollback
    // removes those it admitted.
    this.signatures = new Map();
    this.signatureRecords = new Map();
    // The names of the context entries the session's drivers make, which
    // outlive any one driver (web/cubical-variables.mjs).
    this.entryNames = new EntryNames(this);
    // Declared types (H1) are on by default since their release, in the
    // kernel and here; setExtensions can switch them off.
    this.extensions = { h1: true };
  }
  assertOpen() {
    if (!this.handle) throw new Error("Cubical kernel session is disposed.");
  }
  setOptimizations({ shareSyntax = true, reuseChecks = true, compactPaths = true } = {}) {
    this.assertOpen();
    this.optimizations = { shareSyntax, reuseChecks, compactPaths };
    // reuseChecks and compactPaths are the translator's; the kernel's switch is shared syntax.
    this.module._cb_optimizations(this.handle, shareSyntax ? 1 : 0);
  }
  // Kernel extensions: { h1 } admits declared types, on by default since
  // H1's release. Switched off, the kernel refuses new declarations.
  setExtensions({ h1 = true } = {}) {
    this.assertOpen();
    this.extensions = { h1 };
    this.module._cb_extensions(this.handle, h1 ? 1 : 0);
  }
  // An admitted or open signature: its classification and constructors, as
  // the kernel records them (cc_kernel_signature). Its names are the
  // driver's, in its record (signatureRecords).
  signature(index) {
    this.assertOpen();
    const m = this.module, h = this.handle, field = f => m._cb_signature(h, index, f) >>> 0;
    const levels = field(3), parameters = field(4), count = field(5);
    // A constructor's type is closed over the admission telescope: the
    // levels, the parameters, the sort and the earlier constructors, index 0
    // the last of them. The level is over the former's prenex.
    const constructor = c => {
      const at = f => m._cb_signature_constructor(h, index, c, f) >>> 0;
      return { data: at(0), positions: at(1), dimensions: at(2), type: at(3), generated: at(4) === 1 };
    };
    return {
      admitted: field(0) === 1, experimental: field(1) === 1, modifier: field(2),
      recorded: field(6), former: field(7), level: field(8), levels, parameters,
      constructors: Array.from({ length: count }, (_, c) => constructor(c)),
    };
  }
  setDeadline(milliseconds = 0) {
    this.assertOpen();
    this.deadlineDuration = milliseconds > 0 ? milliseconds : 0;
    this.deadlineGeneration = (this.deadlineGeneration ?? 0) + 1;
    this.deadline = milliseconds > 0 ? performance.now() + milliseconds : 0;
    this.module._cb_deadline_ms(this.handle, milliseconds);
  }
  checkDeadline() {
    if (this.deadline && performance.now() >= this.deadline)
      throw new KernelError("Declaration time limit exceeded.", "deadline");
  }
  // Apply a native per-operation budget. stepBudget remains the session's
  // baseline, which callers restore after a temporary query budget.
  setStepBudget(steps) {
    this.assertOpen();
    const budget = BigInt(steps);
    this.module._cb_step_budget(this.handle, Number(budget & 0xffffffffn),
      uint32(Number(budget >> 32n), "Step budget high word"));
  }
  // A query that runs out of its step budget is run again with twice the
  // budget, up to maxQuerySteps, and then fails as the kernel's exhaustion
  // ("budget"). The session's budget is restored afterwards, so one query's
  // growth never gives another, or an instruction, more steps: every
  // operation's budget is the same in a fresh session and a reused one.
  withGrowingBudget(operation) {
    let budget = this.stepBudget;
    try {
      for (;;) {
        this.checkDeadline();
        const result = operation();
        if (result || this.errorKind() !== "budget" || budget >= this.maxQuerySteps) return result;
        budget = budget * 2n > this.maxQuerySteps ? this.maxQuerySteps : budget * 2n;
        this.setStepBudget(budget);
      }
    } finally { if (budget !== this.stepBudget) this.setStepBudget(this.stepBudget); }
  }
  // The kernel's cumulative work (cc_kernel_work in
  // kernel/include/cubical_kernel.h): instructions and queries started, their
  // steps of budget, and their failures. The counters only grow, through
  // errors and rollbacks too, so the difference of two readings is the work
  // done in between. A step is the unit of the per-operation step budget.
  work() {
    this.assertOpen();
    if (!this.module._cb_work) throw new Error("This cubical kernel module has no work counters. Rebuild it with `make wasm`.");
    const field = index => this.module._cb_work(this.handle, index);
    return { instructions: field(0), rejected: field(1), instructionSteps: field(2), queries: field(3),
      failedQueries: field(4), querySteps: field(5), exhausted: field(6), deadlines: field(7) };
  }
  // The term arena's size.
  arena() {
    this.assertOpen();
    return { nodes: this.module._cb_arena(this.handle, 0) >>> 0, bytes: this.module._cb_arena(this.handle, 1) >>> 0 };
  }
  error() {
    return this.module.UTF8ToString(this.module._cb_error(this.handle));
  }
  errorKind() {
    return errorKinds[this.module._cb_error_kind(this.handle)] ?? "other";
  }
  // The last rejection as a typed error, and cleared: a caller that catches
  // it, as unification does a head it cannot compute, leaves no error behind
  // to refuse the next instruction. A session-level error has no kernel
  // error kind.
  failure(fallback = "") {
    const kind = this.errorKind();
    const error = new KernelError(this.error() || fallback, kind === "none" ? "other" : kind);
    if (kind === "mismatch") error.mismatch = {
      found: this.module._cb_mismatch(this.handle, 0) >>> 0,
      expected: this.module._cb_mismatch(this.handle, 1) >>> 0,
    };
    this.module._cb_clear_error(this.handle);
    return error;
  }
  // A failed instance is not entered to free a session: it is dropped whole.
  dispose() {
    if (this.handle && !moduleFault(this.module)) this.module._cb_free(this.handle);
    this.handle = 0;
  }
  // A name's number, the driver's own: the kernel keeps no names (ABI 4), so
  // the numbers come from a counter of the driver's and never meet the
  // kernel's.
  symbol(name) {
    this.assertOpen();
    if (typeof name !== "string" || !name) throw new TypeError("A symbol needs a nonempty name.");
    if (!this.names.has(name)) {
      const id = this.nextSymbol++;
      this.names.set(name, id);
      this.symbolNames.set(id, name);
    }
    return this.names.get(name);
  }
  symbolName(id) {
    uint32(id, "Symbol");
    if (!this.symbolNames.has(id)) {
      let name = `native${id}`;
      while (this.names.has(name)) name += "_";
      this.symbolNames.set(id, name);
      this.names.set(name, id);
      this.nextSymbol = Math.max(this.nextSymbol, id + 1);
    }
    return this.symbolNames.get(id);
  }
  term(kind, payload = 0, ...children) {
    this.assertOpen();
    const tag = typeof kind === "string" ? cubicalKinds.indexOf(kind) : -1;
    if (tag < 1) throw new Error(`Unsupported cubical constructor: ${kind}`);
    uint32(payload, "Payload");
    if (children.length > 4) throw new Error("Cubical nodes have at most four children.");
    children.forEach(n => uint32(n, "Child handle"));
    while (children.length < 4) children.push(0);
    const id = this.module._cb_term(this.handle, tag, payload, ...children) >>> 0;
    if (!id) throw this.failure(`Could not construct ${kind}.`);
    return id;
  }
  // A binder's body with its index 0 replaced by an entry, for deriving it
  // under the binder (cc_kernel_instantiate): refused when the body mentions
  // the entry already.
  instantiate(body, entry) {
    this.assertOpen();
    const id = this.module._cb_instantiate(this.handle, uint32(body, "Term handle"), uint32(entry, "Entry")) >>> 0;
    if (!id) throw this.failure("Could not open a binder's body.");
    return id;
  }
  formula(sort, clauses) {
    this.assertOpen();
    if (sort !== "interval" && sort !== "face") throw new TypeError("Expected interval or face formula.");
    const m = this.module, h = this.handle;
    if (!m._cb_formula_begin(h, sort === "face" ? 1 : 0)) throw this.failure();
    for (const [positive, negative] of clauses) {
      if (typeof positive !== "bigint" || typeof negative !== "bigint" ||
          positive < 0n || negative < 0n || positive >> 64n || negative >> 64n)
        throw new TypeError("Formula masks must be unsigned 64-bit BigInts.");
      if (!m._cb_formula_clause(h, Number(positive & 0xffffffffn), Number(positive >> 32n),
        Number(negative & 0xffffffffn), Number(negative >> 32n))) throw this.failure();
    }
    const id = m._cb_formula_end(h) >>> 0;
    if (!id) throw this.failure();
    return id;
  }
  // The normal form of a term an instruction derived: the elaborator records
  // each such handle, and its reduction terminates. Raw syntax is refused.
  normalize(derivedHandle) {
    this.assertOpen();
    uint32(derivedHandle, "Derived handle");
    if (!this.derivedHandles?.has(derivedHandle))
      throw new KernelError("Normalize a term or type an instruction derived.");
    const id = this.withGrowingBudget(() => this.module._cb_normalize(this.handle, derivedHandle)) >>> 0;
    if (!id) throw this.failure();
    return this.named(derivedHandle, id);
  }
  // A term the kernel computed from another: its binders are nodes of their
  // own, which carry no names (ABI 4), and each takes the name of the binder
  // in its place in the term, or in a definition the computation unfolded
  // (web/cubical-variables.mjs, carryBinderNames).
  named(from, to) {
    carryBinderNames(this, from, to, true);
    return to;
  }
  // The folded normal form of a derived term (cc_kernel_normalize_folded).
  normalizeFolded(derivedHandle) {
    this.assertOpen();
    uint32(derivedHandle, "Derived handle");
    if (!this.derivedHandles?.has(derivedHandle))
      throw new KernelError("Normalize a term or type an instruction derived.");
    const id = this.withGrowingBudget(() => this.module._cb_normalize_folded(this.handle, derivedHandle)) >>> 0;
    if (!id) throw this.failure();
    return this.named(derivedHandle, id);
  }
  head(handle) {
    this.assertOpen();
    const id = this.withGrowingBudget(() => this.module._cb_head(this.handle, uint32(handle, "Term handle"))) >>> 0;
    if (!id) throw this.failure();
    return id;
  }
  // A term's application spine: its root node, read, and the handles of
  // the arguments applied to it, in order.
  spine(handle) {
    const args = [];
    let node = this.node(handle);
    while (node.kind === "App") { args.push(node.children[1]); node = this.node(node.children[0]); }
    return { root: node, args: args.reverse() };
  }
  // A checked definition: its name, as the driver registered it, its value
  // and its type.
  definition(reference) {
    this.assertOpen();
    uint32(reference, "Definition handle");
    const values = [0, 1].map(field => this.module._cb_definition(this.handle, reference, field) >>> 0);
    if (!values[0]) throw new Error("Unknown checked cubical definition.");
    return { name: this.definitionNames.get(this.node(reference).payload), value: values[0], type: values[1] };
  }
  // A definition registered under a name: for encoding, by the name, and for
  // decoding, by its index, which every reference to it carries.
  nameDefinition(name, reference) {
    this.definitions.set(name, reference);
    this.definitionNames.set(this.node(reference).payload, name);
  }
  definitionName(reference) {
    const name = this.definitionNames.get(this.node(reference).payload);
    if (name === undefined) throw new Error("A checked definition has no registered name.");
    return name;
  }
  node(id) {
    this.assertOpen();
    return (id < this.settled ? this.settledNodes.get(id) : this.nodes.get(id)) ?? this.readNode(id);
  }
  // A node not read yet, field by field through the bridge (cb_node), and
  // kept. The read itself is returned, frozen: a node is read many times a
  // declaration, and a copy each time was a twentieth of a check's time.
  // Reading builds no array but its children's: ABI 4 reads several times
  // the nodes ABI 3 did, as each opening and step makes new ones.
  readNode(id) {
    uint32(id, "Node handle");
    const { module, handle } = this, field = index => module._cb_node(handle, id, index) >>> 0;
    const kind = field(0);
    if (!kind) throw new Error("Unknown cubical node handle.");
    const read = Object.freeze({ id, kind: cubicalKinds[kind], payload: field(1),
      children: Object.freeze([field(2), field(3), field(4), field(5)]) });
    (id < this.settled ? this.settledNodes : this.nodes).set(id, read);
    return read;
  }
  // Node handles move when a declaration's checkpoint is committed or
  // rolled back.
  // At a declaration's end, after its commit or rollback: the nodes there
  // are now settled until the next checkpoint's commit or rollback.
  forgetNodes() { this.nodes.clear(); this.settled = this.arena().nodes + 1; }
  // A token for the node, definition and signature handles a reader holds
  // now, as a runtime query does across operations (web/cubical-runtime.mjs):
  // handlesHeld(token) says whether they still name what they named. The
  // token is the session's handle generation, kept by the bridge
  // (cb_generation in wasm/cubical_bridge.c), which every rollback and
  // commit moves on, however it is called, and never repeats: it is 0 for
  // a freed session and for one whose generations are spent, and no handle
  // is held in generation 0, so such a session's readers fail closed.
  handleToken() { this.assertOpen(); return this.module._cb_generation(this.handle) >>> 0; }
  handlesHeld(token) {
    const generation = this.handle ? this.module._cb_generation(this.handle) >>> 0 : 0;
    return generation !== 0 && generation === token;
  }
  // Syntactic equality only: no reduction and no typing judgement.
  alphaEqual(left, right) {
    this.assertOpen();
    uint32(left, "Node handle"); uint32(right, "Node handle");
    const result = this.module._cb_alpha_equal(this.handle, left, right);
    if (result < 0) throw this.failure("Unknown cubical node handle.");
    return result !== 0;
  }
  inspectFormula(id) {
    this.assertOpen();
    uint32(id, "Formula handle");
    const get = (clause, field) => this.module._cb_formula_view(this.handle, id, clause, field) >>> 0;
    const length = get(0, 0), sort = get(0, 1) ? "face" : "interval";
    const clauses = Array.from({ length }, (_, c) => [
      BigInt(get(c, 2)) | BigInt(get(c, 3)) << 32n,
      BigInt(get(c, 4)) | BigInt(get(c, 5)) << 32n,
    ]);
    return { sort, clauses };
  }
}
