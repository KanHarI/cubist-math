// EVAL3/EVAL4 execution query. It produces observations of checked values,
// never kernel evidence. Its readback (EVAL5's typed readback, W1 of
// docs/roadmaps/runtime/typed-readback.md) gives a value as a closed kernel
// term, which no verdict consumes; cubical execution remains EVAL8 work.
import { InstructionGraph } from "./cubical-instructions.mjs";
import { KernelFault, faultToken } from "./cubical-kernel.mjs";

export class RuntimeError extends Error {
  constructor(kind, message) { super(message); this.kind = kind; }
}
const fail = (kind, message) => { throw new RuntimeError(kind, message); };
// The constructors this fragment executes are the point constructors of any
// admitted declared type, ordinary, higher or truncated (kernel.signature's
// record): no dimensions, so not a path constructor or the squash, which is
// generated with at least one, and recursive positions whose cube is the
// sort itself. Their eliminator's point clauses compute as the kernel's
// iota does (ck_eliminate with no path application). A constructor of
// either other kind is refused when it is demanded, with these reasons.
const pathConstructorRefused = "Execution of a path constructor is not implemented.";
const cubicalPositionsRefused = "Execution of a constructor with cubical recursive positions is not implemented.";
// The term binders of ck_term_binder: each binds its payload in its second child.
const binders = new Set(["Pi", "Lam", "Sigma", "LPi", "LLam"]);
// Readback's tables (docs/roadmaps/runtime/typed-readback.md, 3.2 to 3.5).
// Data: the values a normal-form readback reads by value outside every
// non-data part.
const data = new Set(["Con", "Pair", "Inl", "Inr", "Point"]);
// The nodes of an application spine (spine_node, kernel/src/term_normalize.c),
// which a closure rebuilds one level so that folding sees definition spines.
const spine = new Set(["App", "LApp", "Fst", "Snd", "PApp"]);
// The children that hold a level.
const levelSlots = { U: [0], LSucc: [0], LMax: [0, 1], LApp: [1] };
// The children rebuilt one level with their node, never read back as
// closures: a list, whose items are terms or levels (null where its parent
// says), a chain of tubes or of Glue system pieces, and an annotation the
// kernel reads by its node kind without reducing it, a path application's
// Path type and an unglue's Glue type (weak) and a constructor's Sort
// instance (admitted_signature, kernel/src/signatures.c).
const rebuiltSlots = {
  Sort: { 0: "term", 1: "level" }, Elim: { 1: "term" },
  Comp: { 1: null }, HComp: { 1: null }, Trans: { 1: null }, GlueTerm: { 2: null }, Tube: { 1: null },
  Glue: { 1: null }, GlueSystem: { 2: null },
  PApp: { 1: null }, Con: { 0: null }, Unglue: { 0: null },
};
const none = new Set();
// The closures memo's key for the empty environment.
const topLevel = Object.freeze({});
const memos = () => Object.fromEntries(["value", "outer", "origin", "level"].map(mode => [mode, { cells: new WeakMap(), closures: new WeakMap() }]));
const first = ([handle]) => handle;
const yieldTask = typeof setImmediate === "function" ? () => new Promise(setImmediate)
  : () => new Promise(resolve => {
    const channel = new MessageChannel();
    channel.port1.onmessage = () => { channel.port1.close(); channel.port2.close(); resolve(); };
    channel.port2.postMessage(null);
  });

class Budget {
  constructor(options) {
    this.maxSteps = options.maxSteps ?? 100000000;
    this.maxCells = options.maxCells ?? 20000000;
    this.slice = options.slice ?? 20000;
    this.milliseconds = options.milliseconds ?? 30000;
    for (const n of [this.maxSteps, this.maxCells, this.slice, this.milliseconds])
      if (!Number.isSafeInteger(n) || n < 1) throw new TypeError("Runtime limits must be positive safe integers.");
    this.stats = { steps: 0, allocatedCells: 0, forces: 0, hits: 0, beta: 0, iota: 0, maxFrames: 0, snapshotNodes: 0,
      snapshotDefinitions: 0 };
  }
  start({ milliseconds = this.milliseconds, signal } = {}) {
    if (!Number.isSafeInteger(milliseconds) || milliseconds < 1)
      throw new TypeError("Runtime limits must be positive safe integers.");
    this.deadline = performance.now() + milliseconds; this.signal = signal;
  }
  finish() { this.deadline = 0; this.signal = undefined; }
  // A stop carries the counters it reached and, at a work or allocation
  // budget, that budget.
  stop(kind, message, limit) { throw Object.assign(new RuntimeError(kind, message), { stats: { ...this.stats }, limit }); }
  check() {
    if (this.signal?.aborted) this.stop("cancelled", "Runtime query cancelled.");
    if (this.deadline && performance.now() >= this.deadline) this.stop("deadline", "Runtime operation deadline exceeded.");
  }
  tick() {
    if (++this.stats.steps > this.maxSteps) this.stop("budget", "Runtime query work budget exhausted.", this.maxSteps);
    if ((this.stats.steps & 1023) === 0) this.check();
  }
  allocate(n = 1) {
    this.tick();
    if (this.stats.allocatedCells + n > this.maxCells) this.stop("resource", "Runtime query allocation budget exhausted.", this.maxCells);
    this.stats.allocatedCells += n;
  }
}

// The query reads the kernel lazily: at first only the judgement, then each
// node, definition and signature when the walk first demands it, so that a
// definition the walk never reaches, as a law's proof in a model it only
// projects an operation from, is never copied. Each read is counted in the
// query's work and cells, as the eager copy's were. What is read is copied:
// runtime cells hold copied syntax and kernel indices, never a kernel
// object. The query reads only while nothing can have moved the handles it
// holds since it was made: no checkpoint's rollback or commit and no
// freeing of the session, however they were called, which the bridge's
// handle generation tells (kernel.handlesHeld, cb_generation). A read after
// any of them fails as "expired" instead of reading another state; what was
// copied and computed before stays observable.
function judged(kernel, judgement, budget) {
  budget.check(); kernel.assertOpen();
  const graph = new InstructionGraph(kernel);
  if (!Number.isInteger(judgement) || judgement <= 0 || judgement >= graph.count)
    fail("input", "Execute an existing typing judgement.");
  const checked = graph.judgement(judgement);
  if (checked.kind !== "typing" || checked.context.length)
    fail("input", "Runtime execution requires a closed, assumption-free typing judgement.");
  return { kernel, held: kernel.handleToken(), nodes: new Map(), signatures: new Map(), scopes: new Map(),
    expression: checked.term, type: checked.type };
}

// A declared type's constructor descriptors, compiled from its admitted
// record when one of its constructors is first demanded.
function descriptors(kernel, index, budget) {
  const read = id => { budget.tick(); return kernel.node(id); };
  budget.tick();
  const s = kernel.signature(index);
  if (!s.admitted) fail("input", "Runtime execution requires an admitted signature.");
  budget.allocate(1 + s.constructors.length);
  return s.constructors.map(c => {
    const count = c.data + c.positions;
    if (c.dimensions || c.generated) return { data: c.data, count, arities: null, refused: pathConstructorRefused };
    const arities = [];
    let type = c.type, refused = null;
    for (let i = 0; i < count; i++) {
      const pi = read(type);
      if (pi.kind !== "Pi") fail("input", "Invalid admitted constructor telescope.");
      if (i >= c.data) {
        let position = read(pi.children[0]), arity = 0;
        while (position.kind === "Pi") { arity++; position = read(position.children[1]); }
        if (position.kind !== "Var" || position.payload !== s.sort) refused = cubicalPositionsRefused;
        arities.push(arity);
      }
      type = pi.children[1];
    }
    return { data: c.data, count, arities: refused ? null : arities, refused };
  });
}

// Public handles are opaque and belong to exactly one query. Applications
// are internal transitions of the checked input, not a public unchecked
// application operation. Observation exposes only fields of that input.
export class RuntimeQuery {
  #image; #budget; #root; #type; #definitions = new Map();
  #handles = new WeakMap(); #wrapped = new WeakMap();
  #running = false; #disposed = false;
  // The kernel instance's fault state (faultToken): a query whose instance
  // failed publishes nothing more, as nothing computed after a failure is
  // kept, though its snapshot was copied before.
  #fault;
  // A query made with { origins: true }, for normal-form readback, keeps
  // each forced cell's code and environment, its origin (3.4); value forms
  // keep none.
  #origins;
  // A query made with { heads: true } keeps the head an observation
  // computed by η, by the cell it was asked of, which keeps the λ, for
  // readback(handle, { head: true }): only the tests of the observed heads
  // read it, so value forms keep none.
  #keepHeads; #heads = new WeakMap();
  // Readback's memo, by mode, of cells and of closures by environment and
  // code (3.5); each readback is an epoch of its own.
  #memo = memos(); #epoch = 0;
  #readStats = { readbacks: 0, writes: 0, hits: 0, cells: 0, rebuilt: 0, bindings: 0 };
  constructor(kernel, judgement, options = {}) {
    this.#budget = new Budget(options);
    this.#origins = options.origins === true; this.#keepHeads = options.heads === true;
    this.#fault = faultToken(kernel.module);
    try {
      this.#budget.start(options);
      this.#image = judged(kernel, judgement, this.#budget);
      this.#root = this.#delay(this.#image.expression, null);
      this.#type = this.#delay(this.#image.type, null);
    } finally { this.#budget.finish(); }
  }
  get stats() { return { ...this.#budget.stats }; }
  get root() { this.#open(); return this.#wrap(this.#root); }
  get type() { this.#open(); return this.#wrap(this.#type); }
  // Every operation starts here, a machine resumes here after each slice,
  // and an observation passes here before it is published.
  #open() {
    if (this.#disposed) fail("disposed", "Runtime query has been disposed.");
    if (this.#fault.failed) throw new KernelFault(this.#fault.cause);
  }
  #cell(value) { this.#budget.allocate(); return value; }
  #delay(code, env) { return this.#cell({ state: 0, operation: "syntax", code, env }); }
  #apply(fn, argument) { return this.#cell({ state: 0, operation: "apply", fn, argument }); }
  #ready(value) { return this.#cell({ state: 2, value }); }
  #value(fields) { return this.#cell(fields); }
  #wrap(cell) {
    if (!this.#wrapped.has(cell)) {
      this.#budget.allocate();
      const handle = Object.freeze({});
      this.#wrapped.set(cell, handle); this.#handles.set(handle, cell);
    }
    return this.#wrapped.get(cell);
  }
  #unwrap(handle) {
    const cell = this.#handles.get(handle);
    if (!cell) fail("input", "The value handle does not belong to this runtime query.");
    return cell;
  }
  // The kernel, while the handles the query holds name what they named when
  // it was made.
  #kernel() {
    const { kernel, held } = this.#image;
    if (!kernel.handlesHeld(held))
      fail("expired", "The kernel has changed since the runtime query was made: what it has not read can no longer be read.");
    return kernel;
  }
  // A node of the checked syntax, copied when first demanded.
  #node(id) {
    const nodes = this.#image.nodes;
    let n = nodes.get(id);
    if (!n) {
      this.#budget.tick();
      const read = this.#kernel().node(id);
      this.#budget.allocate(1 + read.children.length);
      nodes.set(id, n = { kind: read.kind, payload: read.payload, children: [...read.children] });
      this.#budget.stats.snapshotNodes = nodes.size;
    }
    return n;
  }
  #list(code, env) {
    const items = [];
    for (let at = code; at;) {
      this.#budget.tick();
      const n = this.#node(at);
      if (n.kind !== "List") fail("input", "Malformed checked eliminator clauses.");
      this.#budget.allocate(); items.push(this.#delay(n.children[0], env)); at = n.children[1];
    }
    return items;
  }
  #descriptor(signature, index) {
    const signatures = this.#image.signatures;
    if (!signatures.has(signature)) signatures.set(signature, descriptors(this.#kernel(), signature, this.#budget));
    const c = signatures.get(signature)[index];
    if (!c) fail("input", "A constructor requires an admitted signature.");
    if (c.refused) fail("unsupported", c.refused);
    return c;
  }
  // The machine for one demanded cell. It pauses after each slice of work:
  // observe resumes it after yielding to the event loop, observeNow at once.
  // Either way the resumed machine checks disposal, cancellation and its
  // deadline before continuing, so a failure resets its pending cells.
  *#run(root) {
    const budget = this.#budget, stack = [];
    let task = { operation: "force", cell: root }, value, slice = 0;
    const push = frame => {
      budget.allocate(); stack.push(frame);
      budget.stats.maxFrames = Math.max(budget.stats.maxFrames, stack.length);
    };
    const force = cell => { task = { operation: "force", cell }; };
    const returned = result => { value = result; task = null; };
    budget.check();
    try {
      for (;;) {
        this.#open(); budget.tick();
        if (++slice >= budget.slice) {
          slice = 0; yield;
          this.#open(); budget.check();
        }
        if (task?.operation === "lookup") {
          const { env, symbol } = task;
          if (!env) fail("input", "Unbound variable in a closed runtime query.");
          if (env.symbol === symbol) force(env.cell);
          else task = { operation: "lookup", env: env.parent, symbol };
          continue;
        }
        if (task) {
          const cell = task.cell;
          if (cell.state === 2) { budget.stats.hits++; returned(cell.value); continue; }
          if (cell.state === 1) fail("input", "Cyclic runtime demand.");
          push({ operation: "update", cell }); cell.state = 1; budget.stats.forces++;
          if (cell.operation === "apply") {
            push({ operation: "apply", argument: cell.argument }); force(cell.fn); continue;
          }
          const n = this.#node(cell.code), c = n.children, env = cell.env;
          const delay = id => this.#delay(id, env);
          switch (n.kind) {
            case "Var": task = { operation: "lookup", env, symbol: n.payload }; break;
            // A definition's value is read at its first demand: one thunk per
            // definition, however many references name it.
            case "DefRef":
              if (!this.#definitions.has(n.payload)) {
                budget.tick();
                const value = this.#kernel().definition(cell.code).value;
                budget.allocate();
                this.#definitions.set(n.payload, this.#delay(value, null));
                budget.stats.snapshotDefinitions = this.#definitions.size;
              }
              force(this.#definitions.get(n.payload)); break;
            // A function keeps the node it was made from, whose domain a
            // readback telescope binds (3.3).
            case "Lam": case "LLam":
              returned(this.#value({ tag: n.kind, symbol: n.payload, body: c[1], env, domain: delay(c[0]), node: cell.code })); break;
            // A path abstraction is a weak head too, kept with its
            // environment. Applying one, at an interval point, is cubical
            // demand, so nothing here substitutes a dimension.
            case "PLam": returned(this.#value({ tag: "PLam", body: c[1], env, node: cell.code })); break;
            case "App": case "LApp":
              push({ operation: "apply", argument: delay(c[1]), level: n.kind === "LApp" }); force(delay(c[0])); break;
            case "Pair":
              returned(this.#value({ tag: "Pair", type: delay(c[0]), first: delay(c[1]), second: delay(c[2]) })); break;
            case "Fst": case "Snd":
              push({ operation: "project", second: n.kind === "Snd" }); force(delay(c[0])); break;
            case "Point": returned(this.#value({ tag: "Point" })); break;
            case "UnitRec": push({ operation: "unit", body: delay(c[1]) }); force(delay(c[2])); break;
            case "Inl": case "Inr": returned(this.#value({ tag: n.kind, type: delay(c[0]), item: delay(c[1]) })); break;
            case "SumRec":
              push({ operation: "sum", left: delay(c[1]), right: delay(c[2]) }); force(delay(c[3])); break;
            case "Con": {
              const instance = this.#node(c[0]);
              if (instance.kind !== "Sort") fail("input", "A constructor requires a declared instance.");
              this.#descriptor(instance.payload, n.payload);
              returned(this.#value({ tag: "Con", signature: instance.payload, index: n.payload, instance: delay(c[0]), args: [] })); break;
            }
            // An eliminator of any admitted signature is a value; only the
            // clause of the constructor it meets is ever demanded.
            case "Elim":
              returned(this.#value({ tag: "Elim", signature: n.payload, motive: delay(c[0]), clauses: this.#list(c[1], env) })); break;
            // A type former is its own weak head. Its parts stay unevaluated;
            // Glue, which can reduce on its faces, is cubical demand. It
            // keeps its node, which readback reads it from, and of its
            // environment only the bindings the node uses (#pruned).
            case "U": case "Pi": case "Sigma": case "Path": case "Sum": case "Unit": case "Void": case "Sort": case "LPi":
              returned(this.#value({ tag: "Type", node: cell.code, env: this.#pruned(cell.code, env) })); break;
            default: fail("unsupported", `Runtime execution of ${n.kind} is not implemented.`);
          }
          continue;
        }
        if (!stack.length) return value;
        const frame = stack.pop();
        switch (frame.operation) {
          case "update": {
            const cell = frame.cell;
            // Release the suspended syntax/environment after successful
            // forcing, unless they are kept as the cell's origin.
            if (!this.#origins) {
              if (cell.operation === "syntax") cell.code = cell.env = undefined;
              else cell.fn = cell.argument = undefined;
            }
            cell.state = 2; cell.value = value; break;
          }
          case "project":
            if (value.tag !== "Pair") fail("input", "Projection of a non-pair.");
            force(frame.second ? value.second : value.first); break;
          case "unit":
            if (value.tag !== "Point") fail("input", "Unit elimination of a non-unit.");
            force(frame.body); break;
          case "sum":
            if (!["Inl", "Inr"].includes(value.tag)) fail("input", "Sum elimination of a non-sum.");
            force(this.#apply(value.tag === "Inl" ? frame.left : frame.right, value.item)); break;
          case "apply": {
            const argument = frame.argument;
            if (value.tag === (frame.level ? "LLam" : "Lam")) {
              budget.stats.beta++;
              // The frame records the node of the function it applied, whose
              // binder, at its domain, a readback telescope binds (3.3).
              force(this.#delay(value.body, this.#cell({ parent: value.env, symbol: value.symbol, cell: argument, binder: value.node })));
            } else if (!frame.level && value.tag === "Con") {
              const descriptor = this.#descriptor(value.signature, value.index);
              if (value.args.length >= descriptor.count) fail("input", "A constructor received too many arguments.");
              budget.allocate(value.args.length + 1);
              returned(this.#value({ ...value, args: [...value.args, argument] }));
            } else if (!frame.level && value.tag === "Elim") {
              push({ operation: "eliminate", eliminator: value }); force(argument);
            } else if (!frame.level && value.tag === "Lift") {
              const position = this.#apply(value.position, argument);
              if (value.remaining === 1) force(this.#apply(value.eliminator, position));
              else returned(this.#value({ ...value, position, remaining: value.remaining - 1 }));
            } else fail("unsupported", `Runtime application of ${value.tag} is not implemented.`);
            break;
          }
          case "eliminate": {
            const e = frame.eliminator;
            if (value.tag !== "Con" || value.signature !== e.signature)
              fail("input", "An eliminator requires a constructor of its signature.");
            const descriptor = this.#descriptor(e.signature, value.index);
            if (value.args.length !== descriptor.count || !e.clauses[value.index])
              fail("input", "An eliminator requires a fully applied constructor and its clause.");
            budget.stats.iota++;
            let branch = e.clauses[value.index];
            for (const argument of value.args) branch = this.#apply(branch, argument);
            const eliminator = this.#ready(e);
            for (let j = 0; j < descriptor.arities.length; j++) {
              const position = value.args[descriptor.data + j], remaining = descriptor.arities[j];
              const hypothesis = remaining ? this.#ready(this.#value({ tag: "Lift", eliminator, position, remaining }))
                : this.#apply(eliminator, position);
              branch = this.#apply(branch, hypothesis);
            }
            force(branch); break;
          }
          default: fail("input", "Unknown runtime continuation.");
        }
      }
    } catch (error) {
      // No partially forced cell becomes a value. Completed siblings survive;
      // the cumulative work/allocation limits still apply to later operations.
      for (const frame of stack) if (frame.operation === "update") frame.cell.state = 0;
      throw error;
    }
  }
  // The weak head of a cell as the kernel's ck_whnf has it: a lambda whose
  // body applies a function to the lambda's variable, not free in that
  // function, is that function (η, of term and level lambdas alike), whose
  // weak head is then taken in turn. The body is inspected, never evaluated.
  *#head(cell) {
    let value = yield* this.#run(cell);
    for (let f; (f = this.#eta(value));) {
      value = yield* this.#run(this.#delay(f, value.env));
      // η leaves the cell holding the λ: the head is kept for its readback.
      if (this.#keepHeads) this.#heads.set(cell, value);
    }
    return value;
  }
  #eta(value) {
    // The kernel contracts path i => p @ i to p when i is not free in p,
    // which reads dimension formulas this fragment does not interpret.
    if (value.tag === "PLam" && this.#node(value.body).kind === "PApp")
      fail("unsupported", "Runtime η of a path abstraction is not implemented.");
    if (value.tag !== "Lam" && value.tag !== "LLam") return 0;
    const body = this.#node(value.body);
    if (body.kind !== (value.tag === "Lam" ? "App" : "LApp")) return 0;
    const argument = this.#node(body.children[1]);
    return argument.kind === "Var" && argument.payload === value.symbol && !this.#free(body.children[0], value.symbol)
      ? body.children[0] : 0;
  }
  // Whether a variable occurs free in syntax, as ck_term_free decides it:
  // Π, λ, Σ and their level forms bind their payload in their second child.
  #free(code, symbol) {
    const seen = new Set(), pending = [code];
    while (pending.length) {
      this.#budget.tick();
      const id = pending.pop();
      if (!id || seen.has(id)) continue;
      seen.add(id);
      const n = this.#node(id);
      if (n.kind === "Var" && n.payload === symbol) return true;
      const bound = binders.has(n.kind) && n.payload === symbol;
      n.children.forEach((child, i) => { if (!(bound && i === 1)) pending.push(child); });
    }
    return false;
  }
  // An observation is the weak head the kernel computes for the represented
  // term, classified: a constructor applied to all of its arguments or to
  // the first ones (`arity` tells which), a pair, an injection, the point, a
  // term or level function, a path abstraction, or a type. A function's
  // parts and a type's are not exposed. Nothing is published once the query
  // is disposed.
  #observation(value) {
    this.#open(); this.#budget.check();
    const wrap = c => this.#wrap(c);
    switch (value.tag) {
      case "Point": return Object.freeze({ kind: "Point" });
      case "Pair": return Object.freeze({ kind: "Pair", type: wrap(value.type), first: wrap(value.first), second: wrap(value.second) });
      case "Inl": case "Inr": return Object.freeze({ kind: value.tag, type: wrap(value.type), item: wrap(value.item) });
      case "Con":
        return Object.freeze({ kind: "Con", signature: value.signature, index: value.index, instance: wrap(value.instance),
          args: Object.freeze(value.args.map(wrap)), arity: this.#descriptor(value.signature, value.index).count });
      // An unapplied eliminator and a lifted hypothesis, λ y. elim(q(y)) in
      // the kernel, are term functions.
      case "Lam": case "Elim": case "Lift": return Object.freeze({ kind: "Function" });
      case "LLam": return Object.freeze({ kind: "LevelFunction" });
      case "PLam": return Object.freeze({ kind: "PathAbstraction" });
      case "Type": return Object.freeze({ kind: "Type" });
      default: fail("unsupported", `Observation of ${value.tag} is not implemented.`);
    }
  }
  #begin(handle) {
    this.#open();
    if (this.#running) fail("input", "A runtime query already has an active observation.");
    return this.#unwrap(handle);
  }
  // Observe a handle, yielding to the event loop between slices of work.
  async observe(handle = this.root, options = {}) {
    const cell = this.#begin(handle); this.#running = true;
    try {
      this.#budget.start(options);
      const steps = this.#head(cell);
      let step = steps.next();
      while (!step.done) { await yieldTask(); step = steps.next(); }
      // Even a force that never yields returns through an await boundary.
      await null;
      return this.#observation(step.value);
    } finally { this.#budget.finish(); this.#running = false; }
  }
  // Observe a handle synchronously, for a caller that cannot yield, as the
  // translator's evaluation cannot: the same machine, limits and deadline,
  // with nothing else running until it returns or fails. A signal can then
  // only have been aborted before the call.
  observeNow(handle = this.root, options = {}) {
    const cell = this.#begin(handle); this.#running = true;
    try {
      this.#budget.start(options);
      const steps = this.#head(cell);
      let step;
      while (!(step = steps.next()).done);
      return this.#observation(step.value);
    } finally { this.#budget.finish(); this.#running = false; }
  }
  // Retained objects after an observation, separate from cumulative allocation.
  // Snapshot syntax has its own count; this walk follows runtime cells only,
  // and the head kept for a cell, which lives as long as the cell does.
  retainedObjects(options = {}) {
    this.#open();
    if (this.#running) fail("input", "Observe retained memory between runtime operations.");
    try {
      this.#budget.start(options); this.#budget.check();
      const seen = new Set(), stack = [this.#root, this.#type, ...this.#definitions.values()];
      while (stack.length) {
        this.#budget.tick();
        const value = stack.pop();
        if (!value || typeof value !== "object" || seen.has(value)) continue;
        seen.add(value);
        for (const child of Object.values(value)) if (child && typeof child === "object") stack.push(child);
        if (this.#heads.has(value)) stack.push(this.#heads.get(value));
      }
      return { runtimeObjects: seen.size, snapshotNodes: this.#image.nodes.size };
    } finally { this.#budget.finish(); }
  }
  get readbackStats() { return { ...this.#readStats }; }
  // The closed kernel term a handle's cell stands for, R(cell) of
  // docs/roadmaps/runtime/typed-readback.md, internal: no user path reads a
  // value back yet (W1). Read back by value, it is every value the runtime
  // computed, functions included, as the β-redexes its closures stand for,
  // so that the kernel performs every substitution (D2); with { origins },
  // on a query made with them, a normal-form readback: data by its value
  // outside every non-data part, and each non-data part as the computation
  // it was forced from (3.4). With { head }, on a query made with heads, the
  // head an observation of the handle returned after η is read back instead
  // of its cell. No type is
  // consulted. The term is admitted to the normalize queries as derived
  // (D3): the written correspondence, under EVAL8's review, is its
  // justification, and only tests type it by instructions. A readback
  // starts, writes kernel syntax and returns a handle only while the
  // kernel's handles are the query's, and fails as "expired" otherwise,
  // dropping its memo (section 7). Its work and cells are the query's.
  readback(handle = this.root, options = {}) {
    const cell = this.#begin(handle), { origins = false, head = false } = options;
    if (origins && !this.#origins) fail("input", "Read back by origin a query made with origins.");
    if (head && !this.#keepHeads) fail("input", "Read back a head from a query made with heads.");
    this.#running = true;
    try {
      this.#budget.start(options); this.#budget.check();
      this.#kernel();
      this.#epoch++; this.#readStats.readbacks++;
      const mode = origins ? "outer" : "value";
      let start = { kind: "cell", cell, mode };
      if (head) {
        const value = this.#heads.get(cell) ?? (cell.state === 2 ? cell.value : null);
        if (!value) fail("input", "Read back the head of an observed handle.");
        start = { kind: "value", value, mode: mode === "outer" && !data.has(value.tag) ? "origin" : mode };
      }
      const term = this.#readOut(start), kernel = this.#kernel();
      (kernel.derivedHandles ??= new Set()).add(term);
      return term;
    } catch (error) {
      if (error instanceof RuntimeError && error.kind === "expired") this.#memo = memos();
      throw error;
    } finally { this.#budget.finish(); this.#running = false; }
  }
  // Readback's machine, with its own stack, so that a value deeper than the
  // host's stack is refused by the kernel's syntax depth (K344) when its
  // term is built, not by the host. A task is a cell, a closure (code
  // under an environment), a level, a value, or a part rebuilt one level;
  // each gives a handle at once, or a frame that builds one from the
  // handles of its parts. A result is stable when every cell it read was
  // forced and every definition 3.3 read has a forced cell: only a stable
  // memo entry answers a later readback, an unstable one only its own.
  #readOut(start) {
    const budget = this.#budget, stack = [];
    let task = start, result = null;
    for (;;) {
      budget.tick();
      if (task) {
        const next = this.#task(task);
        task = null;
        if (next.parts?.length) { budget.allocate(); stack.push(next); task = next.parts[0]; }
        else result = next.parts ? { handle: next.build([]), stable: next.stable } : next;
        continue;
      }
      if (!stack.length) return result.handle;
      const frame = stack.at(-1);
      frame.results.push(result.handle); frame.stable &&= result.stable;
      if (frame.results.length < frame.parts.length) { task = frame.parts[frame.results.length]; continue; }
      stack.pop();
      result = { handle: frame.build(frame.results), stable: frame.stable };
      if (frame.memo) { budget.allocate(); frame.memo.set(frame.key, { ...result, epoch: this.#epoch }); }
    }
  }
  #task(task) {
    switch (task.kind) {
      case "cell": return this.#cellTask(task.cell, task.mode);
      case "closure": return this.#closureTask(task.code, task.env, task.mode);
      case "level": return this.#levelTask(task.code, task.env);
      case "value": return this.#valueTask(task.value, task.mode);
      default: return this.#partTask(task.code, task.env, task.mode, task.items);
    }
  }
  #recall(entry) {
    if (!entry || !(entry.stable || entry.epoch === this.#epoch)) return null;
    this.#readStats.hits++;
    return entry;
  }
  // R(cell) (3.2): a forced cell by its value, or by its origin, the code
  // and environment it was forced from, where the mode asks: in a
  // normal-form readback ("outer") a non-data cell, and inside an origin
  // ("origin") every cell that has one, data included. An unforced cell is
  // its closure, an application cell the application of its two cells; it
  // can be forced later, so its readback is unstable. A normal-form
  // readback cannot tell an unforced cell's value data, so data reaches it
  // by value only through forced cells: an unforced one, an annotation
  // such as a pair's type among them, is read as inside an origin.
  #cellTask(cell, mode) {
    const memo = this.#memo[mode].cells, known = this.#recall(memo.get(cell));
    if (known) return known;
    this.#readStats.cells++;
    const kept = (inner, stable) => ({ results: [], stable, memo, key: cell, ...cell.operation === "apply"
      ? { parts: [{ kind: "cell", cell: cell.fn, mode: inner }, { kind: "cell", cell: cell.argument, mode: inner }],
        build: ([fn, argument]) => this.#write("App", 0, fn, argument) }
      : { parts: [{ kind: "closure", code: cell.code, env: cell.env, mode: inner }], build: first } });
    if (cell.state !== 2) return kept(mode === "outer" ? "origin" : mode, false);
    const value = cell.value, origin = cell.operation === "syntax" ? cell.code !== undefined : cell.fn !== undefined;
    if (origin && (mode === "origin" || mode === "outer" && !data.has(value.tag))) return kept("origin", true);
    const read = this.#valueTask(value, mode === "outer" && !data.has(value.tag) ? "origin" : mode);
    return read.parts ? Object.assign(read, { memo, key: cell }) : read;
  }
  // A value, from the fields the machine executes (3.2): a constructor's
  // index and instance cell, rebuilt one level into a literal Sort of the
  // value's signature, never the node it was made from; a function's
  // symbol, body and environment; an eliminator's signature, motive and
  // clauses. A node supplies only what a value does not hold: a function's
  // domain, a path abstraction's dimension and family, a type's parts.
  #valueTask(value, mode) {
    const frame = (parts, build) => ({ parts, results: [], stable: true, build });
    const cell = c => ({ kind: "cell", cell: c, mode }), closure = (code, env) => frame([{ kind: "closure", code, env, mode }], first);
    switch (value.tag) {
      case "Point": return { handle: this.#write("Point", 0), stable: true };
      case "Pair": return frame([cell(value.type), cell(value.first), cell(value.second)], ([type, a, b]) => this.#write("Pair", 0, type, a, b));
      case "Inl": case "Inr": return frame([cell(value.type), cell(value.item)], ([type, item]) => this.#write(value.tag, 0, type, item));
      // A constructor's instance is a type, no data: a normal-form readback
      // rebuilds its literal Sort with its parts as inside an origin.
      case "Con": {
        const [code, env] = this.#instance(value);
        return frame([{ kind: "part", code, env, mode: mode === "outer" ? "origin" : mode, items: null }, ...value.args.map(cell)],
          ([instance, ...args]) => args.reduce((fn, argument) => this.#write("App", 0, fn, argument), this.#write("Con", value.index, instance)));
      }
      case "Lam": case "LLam": return closure(this.#made(value.node, value.tag, value.symbol, value.body), value.env);
      case "PLam": return closure(this.#made(value.node, "PLam", this.#node(value.node).payload, value.body), value.env);
      case "Type": return closure(value.node, value.env);
      case "Elim": return frame([cell(value.motive), ...value.clauses.map(cell)], ([motive, ...clauses]) =>
        this.#write("Elim", value.signature, motive, clauses.reduceRight((next, clause) => this.#write("List", 0, clause, next), 0)));
      // Its λ needs the domains of the constructor's field telescope at the
      // instance, the one place readback would need types (3.7).
      case "Lift": return fail("unsupported", "Readback of a higher-order recursive hypothesis is not implemented.");
      default: return fail("input", `Readback of ${value.tag} is not implemented.`);
    }
  }
  // A constructor's instance, from its instance cell: its code and
  // environment, or, forced, those its type value keeps.
  #instance(value) {
    const cell = value.instance, [code, env] = cell.state === 2 ? [cell.value.node, cell.value.env] : [cell.code, cell.env];
    const n = code && this.#node(code);
    if (n?.kind !== "Sort" || n.payload !== value.signature) fail("input", "A constructor's instance must be its own signature's sort.");
    return [code, env];
  }
  // A function as the value holds it: its node where the value's fields are
  // the node's, and otherwise that node's kind and domain with the value's
  // binder and body.
  #made(id, kind, payload, body) {
    const n = this.#node(id);
    return n.kind === kind && n.payload === payload && n.children[1] === body ? id : { kind, payload, children: [n.children[0], body, 0, 0] };
  }
  // closure(code, env) (3.3): a variable is the cell it is bound to; a
  // definition with a forced cell is that cell, except where a normal-form
  // readback keeps the reference, its own origin; a code with no variable
  // bound in env and no forced definition outside its term binders is the
  // code itself; a spine node, or a node referencing a forced definition
  // there, is rebuilt one level; and anything else is the telescope of the
  // frames it needs, applied to their cells. Inside an origin, definitions
  // are kept as written.
  #closureTask(code, env, mode) {
    const memo = typeof code === "number" ? this.#closures(mode, env) : null, known = memo && this.#recall(memo.get(code));
    if (known) return known;
    const n = this.#syntax(code);
    if (n.kind === "Var")
      return { parts: [{ kind: "cell", cell: this.#binding(env, n.payload).cell, mode }], results: [], stable: true, build: first, memo, key: code };
    if (n.kind === "DefRef" && mode !== "origin") {
      const cell = this.#definitions.get(n.payload), forced = cell?.state === 2;
      if (forced && (mode === "value" || data.has(cell.value.tag)))
        return { parts: [{ kind: "cell", cell, mode }], results: [], stable: true, build: first, memo, key: code };
      return { handle: code, stable: forced };
    }
    const { vars, defs } = this.#scope(code), settled = mode === "origin" || !defs.size;
    // A term binder references no definition outside its binders.
    const forced = mode !== "origin" && [...defs].some(d => this.#definitions.get(d)?.state === 2);
    if (!vars.size && !forced) return { handle: this.#handleOf(code), stable: settled };
    if (spine.has(n.kind) || forced) return { ...this.#rebuild(n, env, mode, null), memo, key: code };
    return this.#telescope(code, env, mode, settled, memo, code);
  }
  // A part rebuilt one level with its parent (rebuiltSlots), or itself
  // where nothing in it is bound or forced.
  #partTask(code, env, mode, items) {
    const { vars, defs } = this.#scope(code);
    const forced = mode !== "origin" && [...defs].some(d => this.#definitions.get(d)?.state === 2);
    if (!vars.size && !forced) return { handle: code, stable: mode === "origin" || !defs.size };
    return this.#rebuild(this.#node(code), env, mode, items);
  }
  // One level: the node's kind and payload as written, each child read
  // back under the same environment, a term as its closure, a level as a
  // level, and a list, a tube or system chain or a read annotation rebuilt
  // one level in turn. Only nodes that are no term binder are rebuilt.
  #rebuild(n, env, mode, items) {
    this.#readStats.rebuilt++;
    const at = [], parts = [];
    n.children.forEach((child, i) => {
      if (!child) return;
      at.push(i);
      const rebuilt = n.kind === "List" ? (i === 1 ? items : undefined) : rebuiltSlots[n.kind]?.[i];
      parts.push(rebuilt !== undefined ? { kind: "part", code: child, env, mode, items: rebuilt }
        : (n.kind === "List" ? items === "level" : levelSlots[n.kind]?.includes(i)) ? { kind: "level", code: child, env }
        : { kind: "closure", code: child, env, mode });
    });
    return { parts, results: [], stable: true, build: handles => {
      const children = [...n.children];
      at.forEach((i, j) => { children[i] = handles[j]; });
      return this.#write(n.kind, n.payload, ...children);
    } };
  }
  // The frames a code needs: the nearest binding of each variable free in
  // the code, and, for each, the nearest binding above it of each variable
  // free in its binder's domain, in the environment's order, outermost
  // first.
  #frames(code, env) {
    const needed = new Set(), pending = [[this.#scope(code).vars, env]];
    while (pending.length) {
      const [vars, from] = pending.pop();
      for (const symbol of vars) {
        const frame = this.#binding(from, symbol);
        if (needed.has(frame)) continue;
        this.#budget.allocate(); needed.add(frame);
        pending.push([this.#scope(this.#node(frame.binder).children[0]).vars, frame.parent]);
      }
    }
    const frames = [];
    for (let at = env; at && frames.length < needed.size; at = at.parent) {
      this.#budget.tick();
      if (needed.has(at)) frames.push(at);
    }
    return frames.reverse();
  }
  // An environment kept for a value's readback: its frames a code needs,
  // copied in order, each the parent of the next, so that the value keeps
  // no binding its readback does not read. Lookup in it finds what lookup
  // in the environment found: no frame dropped binds a variable nearer than
  // the one kept for it. A node with no children, such as Unit, needs none.
  #pruned(code, env) {
    if (!env || this.#node(code).children.every(child => !child)) return null;
    return this.#frames(code, env).reduce((parent, frame) =>
      this.#cell({ parent, symbol: frame.symbol, cell: frame.cell, binder: frame.binder }), null);
  }
  // The telescope of the frames a code needs, applied to their cells:
  // App(…App(L1(x1; D1, … Ln(xn; Dn, code)…), R(c1))…, R(cn)). Each Li is
  // the binder the frame's β contracted, a term or level λ, and Di its
  // domain as written, so the domains are closed together, never one by
  // one. A level binding is applied to its level, read back.
  #telescope(code, env, mode, stable, memo, key, then = term => term) {
    const frames = this.#frames(code, env);
    this.#readStats.bindings += frames.length;
    const binder = frame => this.#node(frame.binder), level = frame => binder(frame).kind === "LLam";
    return { parts: frames.map(frame => level(frame) ? { kind: "level", code: frame.cell.code, env: frame.cell.env } : { kind: "cell", cell: frame.cell, mode }),
      results: [], stable, memo, key, build: args => {
        let term = this.#handleOf(code);
        for (let i = frames.length; i-- > 0;) term = this.#write(binder(frames[i]).kind, frames[i].symbol, binder(frames[i]).children[0], term);
        frames.forEach((frame, i) => { term = this.#write(level(frame) ? "LApp" : "App", 0, term, args[i]); });
        return then(term);
      } };
  }
  // A level (3.3, Levels): a variable is the level its frame binds; a level
  // with no variable is itself; and otherwise the universe at the level,
  // closed by its telescope, is asked of the kernel's head query, which
  // substitutes and canonicalizes the levels (ck_level_instantiate), and
  // the level is read off the universe returned. A level cell is never
  // forced, so a level read through one is unstable, as 3.5 has it.
  #levelTask(code, env) {
    const memo = this.#closures("level", env), key = code, known = this.#recall(memo.get(code));
    if (known) return known;
    let n = this.#node(code), stable = true;
    while (n.kind === "Var") {
      const { cell } = this.#binding(env, n.payload);
      if (cell.operation !== "syntax" || cell.state === 2) fail("input", "A level variable is bound to a term.");
      code = cell.code; env = cell.env; n = this.#node(code); stable = false;
    }
    if (!this.#scope(code).vars.size) return { handle: code, stable };
    return this.#telescope({ kind: "U", payload: 0, children: [code, 0, 0, 0] }, env, "value", false, memo, key, term => {
      this.#budget.tick();
      const kernel = this.#kernel(), universe = kernel.node(kernel.head(term));
      if (universe.kind !== "U") fail("input", "A level's universe has another weak head.");
      return universe.children[0];
    });
  }
  // The nearest binding of a symbol in an environment, as the machine's
  // lookup takes it.
  #binding(env, symbol) {
    for (let at = env; at; at = at.parent) {
      this.#budget.tick();
      if (at.symbol === symbol) return at;
    }
    return fail("input", "Unbound variable in a closed runtime query.");
  }
  #closures(mode, env) {
    const byEnvironment = this.#memo[mode].closures, key = env ?? topLevel;
    let codes = byEnvironment.get(key);
    if (!codes) byEnvironment.set(key, codes = new Map());
    return codes;
  }
  // A code is a node of the checked syntax, or a function as its value holds
  // it (#made), written only when it is read back as it is.
  #syntax(code) { return typeof code === "number" ? this.#node(code) : code; }
  #handleOf(code) { return typeof code === "number" ? code : this.#write(code.kind, code.payload, ...code.children); }
  // Kernel syntax, built only while the kernel's handles are the query's.
  #write(kind, payload, ...children) {
    this.#budget.tick(); this.#readStats.writes++;
    return this.#kernel().term(kind, payload, ...children);
  }
  // The variables free in a code, binding as ck_term_free does, and the
  // definitions it references outside its term binders, once per copied
  // node, within the query's budget (3.3). Everything inside a term binder
  // stays as written, so a binder references none.
  #scope(code) {
    if (typeof code !== "number") return this.#scopeOf(code, code.children.map(child => child ? this.#scope(child) : null));
    const scopes = this.#image.scopes;
    if (scopes.has(code)) return scopes.get(code);
    const pending = [code];
    while (pending.length) {
      this.#budget.tick();
      const id = pending.at(-1), n = this.#node(id), missing = n.children.filter(child => child && !scopes.has(child));
      if (missing.length) { pending.push(...missing); continue; }
      pending.pop();
      if (!scopes.has(id)) scopes.set(id, this.#scopeOf(n, n.children.map(child => child ? scopes.get(child) : null)));
    }
    return scopes.get(code);
  }
  #scopeOf(n, children) {
    const union = sets => {
      const some = sets.filter(set => set.size);
      if (some.length < 2) return some[0] ?? none;
      this.#budget.allocate();
      return new Set(some.flatMap(set => [...set]));
    };
    if (n.kind === "Var" || n.kind === "DefRef") {
      this.#budget.allocate();
      const own = new Set([n.payload]);
      return n.kind === "Var" ? { vars: own, defs: none } : { vars: none, defs: own };
    }
    const binder = binders.has(n.kind), parts = children.filter(Boolean);
    const vars = union(children.flatMap((child, i) => {
      if (!child) return [];
      if (!(binder && i === 1 && child.vars.has(n.payload))) return [child.vars];
      this.#budget.allocate();
      return [new Set([...child.vars].filter(symbol => symbol !== n.payload))];
    }));
    return { vars, defs: binder ? none : union(parts.map(child => child.defs)) };
  }
  dispose() {
    this.#disposed = true; this.#image = this.#root = this.#type = null;
    this.#definitions.clear(); this.#handles = new WeakMap(); this.#wrapped = new WeakMap();
    this.#memo = memos(); this.#heads = new WeakMap();
  }
}
