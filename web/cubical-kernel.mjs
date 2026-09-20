// Integer-handle interface to the independent C checker, usable in a browser
// worker or Node. Building syntax never certifies it; check() does that in C.
export const cubicalKinds = [
  "", "U", "Var", "Pi", "Lam", "App", "Sigma", "Pair", "Fst", "Snd",
  "Nat", "Zero", "Succ", "NatRec", "Unit", "Point", "Path", "PLam", "PApp",
  "Comp", "Tube", "Void", "Abort", "W", "Sup", "WRec", "Sum", "Inl", "Inr",
  "SumRec", "UnitRec", "Glue", "GlueSystem", "GlueTerm", "Unglue", "DefRef",
];

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
    this.definitions = new Map();
  }
  assertOpen() {
    if (!this.handle) throw new Error("Cubical kernel session is disposed.");
  }
  error() {
    return this.module.UTF8ToString(this.module._cb_error(this.handle));
  }
  dispose() {
    if (this.handle) this.module._cb_free(this.handle);
    this.handle = 0;
  }
  symbol(name) {
    this.assertOpen();
    if (typeof name !== "string" || !name) throw new TypeError("A symbol needs a nonempty name.");
    if (!this.names.has(name)) {
      const id = uint32(this.nextSymbol++, "Symbol");
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
    if (!id) throw new Error(this.error() || `Could not construct ${kind}.`);
    return id;
  }
  formula(sort, clauses) {
    this.assertOpen();
    if (sort !== "interval" && sort !== "face") throw new TypeError("Expected interval or face formula.");
    const m = this.module, h = this.handle;
    if (!m._cb_formula_begin(h, sort === "face" ? 1 : 0)) throw new Error(this.error());
    for (const [positive, negative] of clauses) {
      if (typeof positive !== "bigint" || typeof negative !== "bigint" ||
          positive < 0n || negative < 0n || positive >> 64n || negative >> 64n)
        throw new TypeError("Formula masks must be unsigned 64-bit BigInts.");
      if (!m._cb_formula_clause(h, Number(positive & 0xffffffffn), Number(positive >> 32n),
        Number(negative & 0xffffffffn), Number(negative >> 32n))) throw new Error(this.error());
    }
    const id = m._cb_formula_end(h) >>> 0;
    if (!id) throw new Error(this.error());
    return id;
  }
  check(expression, expected = 0, context = []) {
    this.assertOpen();
    uint32(expression, "Expression handle");
    uint32(expected, "Type handle");
    const m = this.module, h = this.handle;
    m._cb_context_clear(h);
    for (const [symbol, type] of context) {
      uint32(symbol, "Context symbol");
      uint32(type, "Context type");
      if (!m._cb_context_add(h, symbol, type)) throw new Error(this.error());
    }
    if (!m._cb_check(h, expression, expected)) throw new Error(this.error());
    const fields = ["expression", "type", "normal", "checkingSteps", "reductionSteps", "arenaNodes", "arenaBytes"];
    return Object.freeze(Object.fromEntries(fields.map((key, i) => [key, m._cb_result(h, i)])));
  }
  normalize(checkedHandle) {
    this.assertOpen();
    uint32(checkedHandle, "Checked handle");
    const id = this.module._cb_normalize(this.handle, checkedHandle) >>> 0;
    if (!id) throw new Error(this.error() || "Normalize an expression or type from the most recent successful check.");
    return id;
  }
  head(handle) {
    this.assertOpen();
    const id = this.module._cb_head(this.handle, uint32(handle, "Term handle")) >>> 0;
    if (!id) throw new Error(this.error());
    return id;
  }
  define(name, value, expected = 0) {
    this.assertOpen();
    const id = this.module._cb_define(this.handle, this.symbol(name), uint32(value, "Definition body"),
      uint32(expected, "Definition type")) >>> 0;
    if (!id) throw new Error(this.error());
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
