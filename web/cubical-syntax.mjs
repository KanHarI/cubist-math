import { bindDimensions } from "./dist/cubical-runtime/dimension-slots.mjs";
import { dimensionContextKey } from "./dist/cubical-runtime/syntax-graph.mjs";
// Lossless syntax transport between named cubical ASTs and C arena handles.
// This layer never decides typing or equality. Every checked result comes
// from CubicalKernel.check; shared input objects retain shared arena nodes.
export class CubicalSyntax {
  constructor(kernel) {
    this.kernel = kernel;
    this.encoded = new WeakMap();
    this.decoded = new Map();
  }
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
      case "U": result = node(term.level); break;
      case "Var": result = node(k.symbol(term.name)); break;
      case "Nat": case "Zero": case "Unit": case "Point": case "Void": result = node(); break;
      case "Pi": case "Lam": case "Sigma": case "W":
        result = node(k.symbol(term.name), child(term.domain), child(term.body)); break;
      case "App": result = node(0, child(term.fn), child(term.arg)); break;
      case "Pair": result = node(0, child(term.as), child(term.first), child(term.second)); break;
      case "Fst": case "Snd": result = node(0, child(term.pair)); break;
      case "Succ": result = node(0, child(term.value)); break;
      case "NatRec": result = node(0, child(term.motive), child(term.zero), child(term.step), child(term.value)); break;
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
      case "Sup": result = node(0, child(term.as), child(term.label), child(term.children)); break;
      case "WRec": result = node(0, child(term.motive), child(term.step), child(term.value)); break;
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
      case "Pushout": result = node(0, child(term.center), child(term.left), child(term.right), child(term.maps)); break;
      case "PushLeft": case "PushRight": result = node(0, child(term.as), child(term.value)); break;
      case "PushPath": result = node(this.formula(term.arg, "interval", dimensions), child(term.as), child(term.value)); break;
      case "PushElim": result = node(0, child(term.motive), child(term.left), child(term.right), child(term.bridge)); break;
      default: throw new Error(`Unsupported cubical syntax: ${term.tag}`);
    }
    if (!this.encoded.has(term)) this.encoded.set(term, new Map());
    this.encoded.get(term).set(key, result);
    // Cache keys are immutable syntax, so a later mutation cannot accidentally
    // display new text while reusing the earlier checked term.
    if (term.system) { term.system.forEach(Object.freeze); Object.freeze(term.system); }
    Object.freeze(term);
    return result;
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
      case "U": result.level = payload; break;
      case "Var": result.name = this.kernel.symbolName(payload); break;
      case "Nat": case "Zero": case "Unit": case "Point": case "Void": break;
      case "Pi": case "Lam": case "Sigma": case "W":
        Object.assign(result, { name: this.kernel.symbolName(payload), domain: child(0), body: child(1) }); break;
      case "App": Object.assign(result, { fn: child(0), arg: child(1) }); break;
      case "Pair": Object.assign(result, { as: child(0), first: child(1), second: child(2) }); break;
      case "Fst": case "Snd": result.pair = child(0); break;
      case "Succ": result.value = child(0); break;
      case "NatRec": Object.assign(result, { motive: child(0), zero: child(1), step: child(2), value: child(3) }); break;
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
      case "Sup": Object.assign(result, { as: child(0), label: child(1), children: child(2) }); break;
      case "WRec": Object.assign(result, { motive: child(0), step: child(1), value: child(2) }); break;
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
      case "Pushout": Object.assign(result, { center: child(0), left: child(1), right: child(2), maps: child(3) }); break;
      case "PushLeft": case "PushRight": Object.assign(result, { as: child(0), value: child(1) }); break;
      case "PushPath": Object.assign(result, { as: child(0), value: child(1), arg: this.decodeFormula(payload, dimensions) }); break;
      case "PushElim": Object.assign(result, { motive: child(0), left: child(1), right: child(2), bridge: child(3) }); break;
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
  }
  check(term, expected = null, assumptions = [], dimensions = new Map()) {
    let mask = 0n;
    for (const [name, index] of dimensions) {
      if (typeof name !== "string" || !Number.isInteger(index) || index < 0 || index >= 64)
        throw new Error("Invalid cubical dimension binding.");
      const bit = 1n << BigInt(index);
      if (mask & bit) throw new Error("Cubical dimension indices must be distinct.");
      mask |= bit;
    }
    const context = assumptions.map(([name, type]) => [this.kernel.symbol(name), this.encode(type, dimensions)]);
    const result = this.kernel.check(this.encode(term, dimensions), expected ? this.encode(expected, dimensions) : 0, context, mask);
    return { ...result, term: this.decode(result.expression, dimensions), type: this.decode(result.type, dimensions) };
  }
}
