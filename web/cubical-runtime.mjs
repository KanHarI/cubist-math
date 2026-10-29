// EVAL3/EVAL4 execution query. It produces observations of checked values,
// never kernel evidence or a full typed normal form. Cubical execution and
// complete typed readback remain separate EVAL8 integration work.
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
  return { kernel, held: kernel.handleToken(), nodes: new Map(), signatures: new Map(),
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
  constructor(kernel, judgement, options = {}) {
    this.#budget = new Budget(options);
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
            case "Lam": case "LLam":
              returned(this.#value({ tag: n.kind, symbol: n.payload, body: c[1], env, domain: delay(c[0]) })); break;
            // A path abstraction is a weak head too, kept with its
            // environment. Applying one, at an interval point, is cubical
            // demand, so nothing here substitutes a dimension.
            case "PLam": returned(this.#value({ tag: "PLam", body: c[1], env })); break;
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
            // Glue, which can reduce on its faces, is cubical demand.
            case "U": case "Pi": case "Sigma": case "Path": case "Sum": case "Unit": case "Void": case "Sort": case "LPi":
              returned(this.#value({ tag: "Type" })); break;
            default: fail("unsupported", `Runtime execution of ${n.kind} is not implemented.`);
          }
          continue;
        }
        if (!stack.length) return value;
        const frame = stack.pop();
        switch (frame.operation) {
          case "update": {
            const cell = frame.cell;
            // Release the suspended syntax/environment after successful forcing.
            if (cell.operation === "syntax") cell.code = cell.env = undefined;
            else cell.fn = cell.argument = undefined;
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
              force(this.#delay(value.body, this.#cell({ parent: value.env, symbol: value.symbol, cell: argument })));
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
    for (let f; (f = this.#eta(value));) value = yield* this.#run(this.#delay(f, value.env));
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
  // Snapshot syntax has its own count; this walk follows runtime cells only.
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
      }
      return { runtimeObjects: seen.size, snapshotNodes: this.#image.nodes.size };
    } finally { this.#budget.finish(); }
  }
  dispose() {
    this.#disposed = true; this.#image = this.#root = this.#type = null;
    this.#definitions.clear(); this.#handles = new WeakMap(); this.#wrapped = new WeakMap();
  }
}
