import { bindDimensions } from "./dist/cubical-runtime/dimension-slots.mjs";
import { dimensionContextKey } from "./dist/cubical-runtime/syntax-graph.mjs";
// Lossless syntax transport between named cubical ASTs and C arena handles.
// This layer never decides typing or equality. Every checked result comes
// from CubicalKernel.check; shared input objects retain shared arena nodes.
// The dimensions free in a node, as a bit mask, memoized in `memo`. A path
// application's kernel annotation is not counted: neither decoding nor the
// driver's alpha equality reads it.
export function freeDimensionMask(kernel, id, memo) {
  if (!id) return 0n;
  let mask = memo.get(id);
  if (mask !== undefined) return mask;
  const { kind: tag, payload, children: c } = kernel.node(id);
  const free = child => freeDimensionMask(kernel, child, memo);
  const bound = child => free(child) & ~(1n << BigInt(payload));
  const formula = f => kernel.inspectFormula(f).clauses.reduce((m, [p, n]) => m | p | n, 0n);
  // A list of faces, each with the parts it guards.
  const system = (chain, parts) => {
    let m = 0n;
    for (let link = chain; link;) {
      const n = kernel.node(link);
      m |= formula(n.payload) | parts(n.children);
      link = n.children[tag === "Glue" ? 2 : 1];
    }
    return m;
  };
  switch (tag) {
    case "Path": mask = bound(c[0]) | free(c[1]) | free(c[2]); break;
    case "PLam": mask = bound(c[0]) | bound(c[1]); break;
    case "PApp": mask = formula(payload) | free(c[0]); break;
    case "Trans": mask = bound(c[0]) | formula(kernel.node(c[1]).payload) | free(c[2]); break;
    case "Comp": case "HComp":
      mask = (tag === "HComp" ? free(c[0]) : bound(c[0])) | system(c[1], ([body]) => bound(body)) | free(c[2]); break;
    case "Glue": mask = free(c[0]) | system(c[1], ([type, equiv]) => free(type) | free(equiv)); break;
    case "GlueTerm": mask = free(c[0]) | free(c[1]) | system(c[2], ([term]) => free(term)); break;
    default: mask = c.reduce((m, child) => m | free(child), 0n);
  }
  memo.set(id, mask);
  return mask;
}
export class CubicalSyntax {
  constructor(kernel) {
    this.kernel = kernel;
    this.reset();
  }
  // Handles move when a checkpoint is committed or rolled back: the caches
  // keyed by them are dropped then.
  reset() {
    this.encoded = new WeakMap();
    this.decoded = new Map();
    this.free = new Map();
  }
  // The dimensions free in a node, as a bit mask (freeDimensionMask).
  freeDimensions(id) { return freeDimensionMask(this.kernel, id, this.free); }
  formula(value, sort, dimensions) {
    const clauses = value.map(clause => {
      let positive = 0n, negative = 0n;
      for (const literal of clause) {
        if (typeof literal !== "string" || !/:[01]$/.test(literal)) throw new Error("Invalid dimension literal.");
        const name = literal.slice(0, -2);
        if (!dimensions.has(name)) throw new Error(`Unbound cubical dimension: ${name}`);
        const bit = 1n << BigInt(dimensions.get(name));
        if (literal.endsWith("1")) positive |= bit; else negative |= bit;
      }
      return [positive, negative];
    });
    value.forEach(Object.freeze);
    Object.freeze(value);
    return this.kernel.formula(sort, clauses);
  }
  encode(term, dimensions = new Map()) {
    if (!term || typeof term !== "object") throw new TypeError("Expected cubical syntax.");
    const key = dimensionContextKey(dimensions);
    const cached = this.encoded.get(term)?.get(key);
    if (cached) return cached;
    const k = this.kernel, child = t => this.encode(t, dimensions);
    const node = (payload = 0, ...children) => k.term(term.tag, payload, ...children);
    let result;
    switch (term.tag) {
      case "DefRef":
        result = k.definitions.get(term.name);
        if (!result) throw new Error(`Unknown checked cubical definition: ${term.name}`);
        break;
      case "U": result = node(0, this.encodeLevel(term.level)); break;
      case "Var": result = node(k.symbol(term.name)); break;
      case "Unit": case "Point": case "Void": result = node(); break;
      case "Pi": case "Lam": case "Sigma":
        result = node(k.symbol(term.name), child(term.domain), child(term.body)); break;
      case "App": result = node(0, child(term.fn), child(term.arg)); break;
      case "Pair": result = node(0, child(term.as), child(term.first), child(term.second)); break;
      case "Fst": case "Snd": result = node(0, child(term.pair)); break;
      case "Path": case "PLam": case "Comp": case "HComp": case "Trans": {
        const { dim, inner } = bindDimensions(term, dimensions);
        const family = this.encode(term.family, term.tag === "HComp" ? dimensions : inner);
        if (term.tag === "Path") result = node(dim, family, child(term.left), child(term.right));
        else if (term.tag === "PLam") result = node(dim, family, this.encode(term.body, inner));
        else if (term.tag === "Trans") {
          const base = child(term.base);
          const descriptor = k.term("Tube", this.formula(term.face, "face", dimensions), base, 0);
          result = node(dim, family, descriptor, base);
        } else {
          let tubes = 0;
          for (const part of [...term.system].reverse())
            tubes = k.term("Tube", this.formula(part.face, "face", dimensions), this.encode(part.term, inner), tubes);
          result = node(dim, family, tubes, child(term.base));
        }
        break;
      }
      case "PApp": result = node(this.formula(term.arg, "interval", dimensions), child(term.path)); break;
      case "Abort": result = node(0, child(term.as), child(term.impossible)); break;
      case "Sum": result = node(0, child(term.left), child(term.right)); break;
      case "Inl": case "Inr": result = node(0, child(term.as), child(term.value)); break;
      case "SumRec": result = node(0, child(term.motive), child(term.left), child(term.right), child(term.value)); break;
      case "UnitRec": result = node(0, child(term.motive), child(term.point), child(term.value)); break;
      case "Glue": {
        let system = 0;
        for (const part of [...term.system].reverse())
          system = k.term("GlueSystem", this.formula(part.face, "face", dimensions), child(part.type), child(part.equiv), system);
        result = node(0, child(term.base), system); break;
      }
      case "GlueTerm": {
        let system = 0;
        for (const part of [...term.system].reverse())
          system = k.term("Tube", this.formula(part.face, "face", dimensions), child(part.term), system);
        result = node(0, child(term.as), child(term.base), system); break;
      }
      case "Unglue": result = node(0, child(term.as), child(term.value)); break;
      // Level quantification (G0): Π (x < ω). B, λ (x < ω). t and f {ℓ}. The
      // bound is always ω, LBound(1), in this version.
      case "LPi": case "LLam": result = node(k.symbol(term.name), k.term("LBound", 1), child(term.body)); break;
      case "LApp": result = node(0, child(term.fn), this.encodeLevel(term.level)); break;
      // A universe variable's bound, as the type of its context entry.
      case "LBound": result = node(term.tier ?? 1); break;
      // Declared types (H1): an instance S{ls}(as) of an admitted signature,
      // named as its declaration registered it (web/cubical-signatures.mjs);
      // constructor number `index` of an instance; an eliminator with its
      // motive and one clause per constructor, the squash's included.
      case "Sort":
        result = node(this.signatureIndex(term.signature), this.list(term.parameters ?? [], child),
          this.list(term.levels ?? [], level => this.encodeLevel(level)));
        break;
      case "Con":
        if (!Number.isInteger(term.index) || term.index < 0) throw new Error("A constructor needs its number.");
        result = node(term.index, child(term.sort));
        break;
      case "Elim":
        result = node(this.signatureIndex(term.signature), child(term.motive), this.list(term.clauses, child));
        break;
      default: throw new Error(`Unsupported cubical syntax: ${term.tag}`);
    }
    if (!this.encoded.has(term)) this.encoded.set(term, new Map());
    this.encoded.get(term).set(key, result);
    // Cache keys are immutable syntax, so a later mutation cannot accidentally
    // display new text while reusing the earlier checked term.
    if (term.system) { term.system.forEach(Object.freeze); Object.freeze(term.system); }
    for (const items of [term.parameters, term.levels, term.clauses]) if (Array.isArray(items)) Object.freeze(items);
    Object.freeze(term);
    return result;
  }
  // The kernel's List cells for a sequence, in order.
  list(items, encode) {
    let list = 0;
    for (const item of [...items].reverse()) list = this.kernel.term("List", 0, encode(item), list);
    return list;
  }
  items(list) {
    const out = [];
    for (let cell = list; cell; cell = this.kernel.node(cell).children[1]) out.push(this.kernel.node(cell).children[0]);
    return out;
  }
  // An admitted signature's kernel index, by the name its declaration gave it.
  signatureIndex(name) {
    const record = this.kernel.signatures.get(name);
    if (!record) throw new Error(`Unknown declared type: ${name}`);
    return record.index;
  }
  // The registered record of the signature at a kernel index: its name and
  // constructor names. A signature admitted without one is named by its
  // kernel symbols.
  signatureRecord(index) {
    for (const record of this.kernel.signatures.values()) if (record.index === index) return record;
    const info = this.kernel.signature(index), name = this.kernel.symbolName(info.sort);
    return { name, index, constructors: info.constructors.map(c => c.generated ? "squash" : this.kernel.symbolName(c.symbol)) };
  }
  // A universe's level (web/cubical-levels.mjs): a number is a tier-0
  // constant. The kernel takes it to normal form; this only encodes it.
  encodeLevel(level) {
    const k = this.kernel;
    if (typeof level === "number") {
      if (!Number.isInteger(level) || level < 0 || level > 0xffff) throw new Error(`Invalid universe level: ${level}`);
      return k.term("LConst", level);
    }
    switch (level?.tag) {
      case "LConst":
        if (![level.tier, level.value].every(n => Number.isInteger(n) && n >= 0 && n <= 0xffff))
          throw new Error("Invalid universe level constant.");
        return k.term("LConst", level.tier * 0x10000 + level.value);
      case "LSucc": return k.term("LSucc", level.count, this.encodeLevel(level.level));
      case "LMax": return k.term("LMax", 0, this.encodeLevel(level.left), this.encodeLevel(level.right));
      case "Var": return k.term("Var", k.symbol(level.name));
      default: throw new Error("Expected a universe level.");
    }
  }
  decodeLevel(id) {
    const { kind, payload, children } = this.kernel.node(id);
    switch (kind) {
      case "LConst": return payload <= 0xffff ? payload : { tag: "LConst", tier: payload >>> 16, value: payload & 0xffff };
      case "LSucc": return { tag: "LSucc", count: payload, level: this.decodeLevel(children[0]) };
      case "LMax": return { tag: "LMax", left: this.decodeLevel(children[0]), right: this.decodeLevel(children[1]) };
      case "Var": return { tag: "Var", name: this.kernel.symbolName(payload) };
      default: throw new Error(`Expected a universe level, not ${kind}.`);
    }
  }
  decodeFormula(id, dimensions = new Map()) {
    const names = new Map([...dimensions].map(([name, index]) => [index, name]));
    return this.kernel.inspectFormula(id).clauses.map(([positive, negative]) => {
      const clause = [];
      for (let dim = 0; dim < 64; dim++) {
        const bit = 1n << BigInt(dim);
        if (positive & bit) clause.push(`${names.get(dim) ?? `d${dim}`}:1`);
        if (negative & bit) clause.push(`${names.get(dim) ?? `d${dim}`}:0`);
      }
      return clause;
    });
  }
  decode(id, dimensions = new Map()) {
    // A node's decoding depends only on the names of its free dimensions, so
    // it is decoded, and cached, under those alone. A binder inside may then
    // reuse the name of a dimension the node does not mention.
    const free = this.freeDimensions(id);
    if ([...dimensions.values()].some(index => !(free & 1n << BigInt(index))))
      dimensions = new Map([...dimensions].filter(([, index]) => free & 1n << BigInt(index)));
    const cacheKey = JSON.stringify([id,dimensionContextKey(dimensions)]);
    if (this.decoded.has(cacheKey)) return this.decoded.get(cacheKey);
    const { kind: tag, payload, children: c } = this.kernel.node(id);
    const child = i => this.decode(c[i], dimensions);
    let dim = `d${payload}`;
    while (dimensions.has(dim)) dim += "_";
    const inner = new Map(dimensions).set(dim, payload);
    const boundChild = i => this.decode(c[i], inner);
    let result = { tag };
    switch (tag) {
      case "DefRef": result.name = this.kernel.definition(id).name; break;
      case "U": result.level = this.decodeLevel(c[0]); break;
      case "LPi": case "LLam": Object.assign(result, { name: this.kernel.symbolName(payload), body: child(1) }); break;
      case "LApp": Object.assign(result, { fn: child(0), level: this.decodeLevel(c[1]) }); break;
      case "LBound": result.tier = payload; break;
      case "Var": result.name = this.kernel.symbolName(payload); break;
      case "Unit": case "Point": case "Void": break;
      case "Pi": case "Lam": case "Sigma":
        Object.assign(result, { name: this.kernel.symbolName(payload), domain: child(0), body: child(1) }); break;
      case "App": Object.assign(result, { fn: child(0), arg: child(1) }); break;
      case "Pair": Object.assign(result, { as: child(0), first: child(1), second: child(2) }); break;
      case "Fst": case "Snd": result.pair = child(0); break;
      case "Path": Object.assign(result, { dim, family: boundChild(0), left: child(1), right: child(2) }); break;
      case "PLam": Object.assign(result, { dim, family: boundChild(0), body: boundChild(1) }); break;
      case "PApp": Object.assign(result, { path: child(0), arg: this.decodeFormula(payload, dimensions) }); break;
      case "Trans": {
        const descriptor = this.kernel.node(c[1]);
        if (descriptor.kind !== "Tube" || descriptor.children[1]) throw new Error("Invalid transport face descriptor.");
        Object.assign(result, { dim, family: boundChild(0), face: this.decodeFormula(descriptor.payload, dimensions), base: child(2) });
        break;
      }
      case "Comp": case "HComp": {
        const system = [];
        for (let tube = c[1]; tube;) {
          const n = this.kernel.node(tube);
          if (n.kind !== "Tube") throw new Error("Invalid cubical tube list.");
          system.push({ face: this.decodeFormula(n.payload, dimensions), term: this.decode(n.children[0], inner) });
          tube = n.children[1];
        }
        Object.assign(result, { dim, family: tag === "HComp" ? child(0) : boundChild(0), system, base: child(2) }); break;
      }
      case "Abort": Object.assign(result, { as: child(0), impossible: child(1) }); break;
      case "Sum": Object.assign(result, { left: child(0), right: child(1) }); break;
      case "Inl": case "Inr": Object.assign(result, { as: child(0), value: child(1) }); break;
      case "SumRec": Object.assign(result, { motive: child(0), left: child(1), right: child(2), value: child(3) }); break;
      case "UnitRec": Object.assign(result, { motive: child(0), point: child(1), value: child(2) }); break;
      case "Glue": case "GlueTerm": {
        const system = [];
        for (let part = c[tag === "Glue" ? 1 : 2]; part;) {
          const n = this.kernel.node(part), face = this.decodeFormula(n.payload, dimensions);
          if (tag === "Glue") {
            if (n.kind !== "GlueSystem") throw new Error("Invalid cubical Glue system.");
            system.push({ face, type: this.decode(n.children[0], dimensions), equiv: this.decode(n.children[1], dimensions) });
            part = n.children[2];
          } else {
            if (n.kind !== "Tube") throw new Error("Invalid cubical Glue element system.");
            system.push({ face, term: this.decode(n.children[0], dimensions) }); part = n.children[1];
          }
        }
        Object.assign(result, tag === "Glue" ? { base: child(0), system } : { as: child(0), base: child(1), system }); break;
      }
      case "Unglue": Object.assign(result, { as: child(0), value: child(1) }); break;
      case "Sort":
        Object.assign(result, { signature: this.signatureRecord(payload).name,
          parameters: this.items(c[0]).map(item => this.decode(item, dimensions)),
          levels: this.items(c[1]).map(level => this.decodeLevel(level)) });
        break;
      case "Con": {
        const sort = this.kernel.node(c[0]);
        const name = sort.kind === "Sort" ? this.signatureRecord(sort.payload).constructors[payload] : undefined;
        Object.assign(result, { index: payload, ...(name ? { name } : {}), sort: child(0) });
        break;
      }
      case "Elim":
        Object.assign(result, { signature: this.signatureRecord(payload).name, motive: child(0),
          clauses: this.items(c[1]).map(item => this.decode(item, dimensions)) });
        break;
      default: throw new Error(`Unsupported cubical node: ${tag}`);
    }
    // Preserve the native node on a round trip. In particular a checked PApp
    // carries a kernel-owned type annotation that JSON deliberately omits.
    // The immutable object is the cache key; copied or edited syntax is checked
    // anew and cannot supply such an annotation.
    const freeze = value => {
      if (value && typeof value === "object" && !Object.isFrozen(value)) {
        Object.values(value).forEach(freeze); Object.freeze(value);
      }
    };
    freeze(result);
    this.encoded.set(result, new Map([[dimensionContextKey(dimensions), id]]));
    this.decoded.set(cacheKey, result);
    return result;
  }}
