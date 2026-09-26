// Integer-handle interface to the independent C checker, usable in a browser
// worker or Node. Building syntax never certifies it; check() does that in C.
const traceKinds = ["", "infer", "inferred", "reused", "extend", "convert", "reduce"];
export const cubicalKinds = [
  "", "U", "Var", "Pi", "Lam", "App", "Sigma", "Pair", "Fst", "Snd",
  "Nat", "Zero", "Succ", "NatRec", "Unit", "Point", "Path", "PLam", "PApp",
  "Comp", "Tube", "Void", "Abort", "W", "Sup", "WRec", "Sum", "Inl", "Inr",
  "SumRec", "UnitRec", "Glue", "GlueSystem", "GlueTerm", "Unglue", "DefRef",
  "Pushout", "PushLeft", "PushRight", "PushPath", "PushElim",
  "HComp", "Trans",
];

// A rejected kernel request. `kind` classifies it, from cc_error_kind, so no
// caller needs to read the message: "mismatch" (a type is not convertible to
// the expected one), "budget" or "deadline" (no judgement was made), "other".
// A mismatch also carries `mismatch`, the handles of the type found and the
// type expected; they are valid until the next rollback.
const errorKinds = ["none", "mismatch", "budget", "deadline", "other"];
export class KernelError extends Error {
  constructor(message, kind = "other") { super(message); this.kind = kind; }
}

function uint32(value, label) {
  if (!Number.isInteger(value) || value < 0 || value > 0xffffffff)
    throw new TypeError(`${label} must be an unsigned 32-bit integer.`);
  return value;
}

export class CubicalKernel {
  constructor(module) {
    this.module = module;
    this.handle = module._cb_new();
    if (!this.handle) throw new Error("Could not allocate cubical kernel session.");
    this.names = new Map();
    this.symbolNames = new Map();
    this.nextSymbol = 1;
    this.stepBudget = 10000000n;
    this.unfoldingHints = [];
    this.definitions = new Map();
  }
  assertOpen() {
    if (!this.handle) throw new Error("Cubical kernel session is disposed.");
  }
  setOptimizations({ shareSyntax = true, reuseChecks = true, compactPaths = true } = {}) {
    this.assertOpen();
    this.optimizations = { shareSyntax, reuseChecks, compactPaths };
    this.module._cb_optimizations(this.handle, (shareSyntax ? 1 : 0) | (reuseChecks ? 2 : 0));
  }
  setDeadline(milliseconds = 0) {
    this.assertOpen();
    this.deadline = milliseconds > 0 ? performance.now() + milliseconds : 0;
    this.module._cb_deadline_ms(this.handle, milliseconds);
  }
  // Run an operation with the checker's trace on, and return the rules it
  // applied, as events (kernel/include/cubical_kernel.h). The trace changes
  // no result; events past the capacity are counted as dropped.
  traced(operation, capacity = 4000) {
    this.assertOpen();
    if (!this.module._cb_trace(this.handle, capacity)) throw new Error("Could not start a kernel trace.");
    try {
      const value = operation();
      const count = this.module._cb_trace_count(this.handle) >>> 0, kept = Math.min(count, capacity);
      const field = (index, which) => this.module._cb_trace_event(this.handle, index, which) >>> 0;
      const events = Array.from({ length: kept }, (_, index) => ({ kind: traceKinds[field(index, 0)],
        depth: field(index, 1), a: field(index, 2), b: field(index, 3), c: field(index, 4) }));
      return { value, events, dropped: count - kept };
    } finally { this.module._cb_trace(this.handle, 0); }
  }
  checkDeadline() {
    if (this.deadline && performance.now() >= this.deadline)
      throw new KernelError("Declaration time limit exceeded.", "deadline");
  }
  setUnfoldingHints(names = []) {
    this.assertOpen();
    const unique = [...new Set(names)];
    const references = unique.map(name => {
      const reference = this.definitions.get(name);
      if (!reference) throw new Error(`An unfolding hint needs a checked definition: ${name}`);
      return reference;
    });
    if (!this.module._cb_unfolding_clear(this.handle)) throw this.failure();
    this.unfoldingHints = [];
    for (let i = 0; i < references.length; i++) {
      if (!this.module._cb_unfolding_add(this.handle, references[i])) throw this.failure();
      this.unfoldingHints.push(unique[i]);
    }
  }
  withUnfoldingHints(names, operation) {
    const previous = this.unfoldingHints;
    this.setUnfoldingHints(names);
    try { return operation(); } finally { this.setUnfoldingHints(previous); }
  }
  withGrowingBudget(operation) {
    for (;;) {
      this.checkDeadline();
      const result = operation();
      if (result || this.errorKind() !== "budget") return result;
      const largest = (1n << 64n) - 1n;
      if (this.stepBudget === largest) return result;
      this.stepBudget = this.stepBudget > largest / 2n ? largest : this.stepBudget * 2n;
      this.module._cb_step_budget(this.handle, Number(this.stepBudget & 0xffffffffn), Number(this.stepBudget >> 32n));
    }
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
  // The last rejection as a typed error. A session-level error has no kernel
  // error kind.
  failure(fallback = "") {
    const kind = this.errorKind();
    const error = new KernelError(this.error() || fallback, kind === "none" ? "other" : kind);
    if (kind === "mismatch") error.mismatch = {
      found: this.module._cb_mismatch(this.handle, 0) >>> 0,
      expected: this.module._cb_mismatch(this.handle, 1) >>> 0,
    };
    return error;
  }
  dispose() {
    if (this.handle) this.module._cb_free(this.handle);
    this.handle = 0;
  }
  symbol(name) {
    this.assertOpen();
    if (typeof name !== "string" || !name) throw new TypeError("A symbol needs a nonempty name.");
    if (!this.names.has(name)) {
      // The kernel allocates the id: its own fresh names come from the same
      // counter, so a page name and a kernel name never share one.
      const id = uint32(this.module._cb_fresh_symbol(this.handle) >>> 0, "Symbol");
      if (!id) throw this.failure("Could not allocate a symbol.");
      this.nextSymbol = Math.max(this.nextSymbol, id + 1);
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
    const tag = cubicalKinds.indexOf(kind);
    if (tag < 1) throw new Error(`Unsupported cubical constructor: ${kind}`);
    uint32(payload, "Payload");
    if (children.length > 4) throw new Error("Cubical nodes have at most four children.");
    children.forEach(n => uint32(n, "Child handle"));
    while (children.length < 4) children.push(0);
    const id = this.module._cb_term(this.handle, tag, payload, ...children) >>> 0;
    if (!id) throw this.failure(`Could not construct ${kind}.`);
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
  check(expression, expected = 0, context = [], dimensions = 0n) {
    this.assertOpen();
    uint32(expression, "Expression handle");
    uint32(expected, "Type handle");
    if (typeof dimensions !== "bigint" || dimensions < 0n || dimensions >> 64n)
      throw new TypeError("Dimensions must be an unsigned 64-bit BigInt mask.");
    const m = this.module, h = this.handle;
    m._cb_context_clear(h);
    for (const [symbol, type] of context) {
      uint32(symbol, "Context symbol");
      uint32(type, "Context type");
      if (!m._cb_context_add(h, symbol, type)) throw this.failure();
    }
    if (!this.withGrowingBudget(() => m._cb_check_in_cube(h, expression, expected,
      Number(dimensions & 0xffffffffn), Number(dimensions >> 32n)))) throw this.failure();
    const fields = ["expression", "type", "normal", "checkingSteps", "reductionSteps", "arenaNodes", "arenaBytes"];
    return Object.freeze(Object.fromEntries(fields.map((key, i) => [key, m._cb_result(h, i)])));
  }
  normalize(checkedHandle) {
    this.assertOpen();
    uint32(checkedHandle, "Checked handle");
    // A handle the instruction kernel derived is well typed as well.
    const derived = this.derivedHandles?.has(checkedHandle);
    const id = this.withGrowingBudget(() => derived ? this.module._cb_normalize_derived(this.handle, checkedHandle)
      : this.module._cb_normalize(this.handle, checkedHandle)) >>> 0;
    if (!id) throw this.failure("Normalize an expression or type from the most recent successful check.");
    return id;
  }
  head(handle) {
    this.assertOpen();
    const id = this.withGrowingBudget(() => this.module._cb_head(this.handle, uint32(handle, "Term handle"))) >>> 0;
    if (!id) throw this.failure();
    return id;
  }
  define(name, value, expected = 0) {
    this.assertOpen();
    const id = this.withGrowingBudget(() => this.module._cb_define(this.handle, this.symbol(name), uint32(value, "Definition body"),
      uint32(expected, "Definition type"))) >>> 0;
    if (!id) throw this.failure();
    this.definitions.set(name, id);
    return id;
  }
  definition(reference) {
    this.assertOpen();
    uint32(reference, "Definition handle");
    const values = [0, 1, 2].map(field => this.module._cb_definition(this.handle, reference, field) >>> 0);
    if (!values[0]) throw new Error("Unknown checked cubical definition.");
    return { name: this.symbolName(values[0]), value: values[1], type: values[2] };
  }
  node(id) {
    this.assertOpen();
    uint32(id, "Node handle");
    const values = Array.from({ length: 6 }, (_, field) => this.module._cb_node(this.handle, id, field) >>> 0);
    if (!values[0]) throw new Error("Unknown cubical node handle.");
    return { id, kind: cubicalKinds[values[0]], payload: values[1], children: values.slice(2),
      name: this.symbolNames.get(values[1]) };
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
