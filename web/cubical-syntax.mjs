import { bindDimensions } from "./translator/dimension-slots.mjs";
import { dimensionContextKey } from "./translator/syntax-graph.mjs";
import { freeNames, isTerm } from "./translator/core.mjs";
import { binderName, binderTerm, binders, boundSymbol, pushName, referenceSymbol, variableName, variableTerm } from "./cubical-variables.mjs";
// The scope of no context: what is encoded against it is closed.
export const EMPTY_SCOPE = Object.freeze(new Map());
// Lossless syntax transport between named cubical ASTs and C arena handles.
// This layer never decides typing or equality. Every checked result comes
// from CubicalKernel.check; shared input objects retain shared arena nodes.
// The dimensions free in a node, as a bit mask, memoized in `memo`. A path
// application's kernel annotation is not counted, unless `annotated`:
// neither decoding nor the driver's alpha equality reads it.
export function freeDimensionMask(kernel, id, memo, annotated = false) {
  if (!id) return 0n;
  let mask = memo.get(id);
  if (mask !== undefined) return mask;
  const { kind: tag, payload, children: c } = kernel.node(id);
  const free = child => freeDimensionMask(kernel, child, memo, annotated);
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
    case "PApp": mask = formula(payload) | free(c[0]) | (annotated ? free(c[1]) : 0n); break;
    case "Trans": mask = bound(c[0]) | formula(kernel.node(c[1]).payload) | free(c[2]); break;
    case "Comp": case "HComp":
      mask = (tag === "HComp" ? free(c[0]) : bound(c[0])) | system(c[1], ([body]) => bound(body)) | free(c[2]); break;
    case "Glue": mask = free(c[0]) | system(c[1], ([type, equiv]) => free(type) | free(equiv)); break;
    case "GlueTerm": mask = free(c[0]) | free(c[1]) | system(c[2], ([term]) => free(term)); break;
    // A system's link, read alone, as the driver's alpha equality reads
    // each node: its face, its parts and the links after it.
    case "Tube": case "GlueSystem": mask = c.reduce((m, child) => m | free(child), formula(payload)); break;
    default: mask = c.reduce((m, child) => m | free(child), 0n);
  }
  memo.set(id, mask);
  return mask;
}
// A cache of what reads nodes, in two tiers by whether the handles it holds
// are settled (CubicalKernel.settled): those a declaration's commit or
// rollback leaves where they are. The settled tier is kept from one
// declaration to the next, and the rest dropped (CubicalSyntax.reset). An
// entry is settled when every handle in it is: `id` is the largest.
class NodeCache {
  constructor(kernel, weak = false) {
    Object.assign(this, { kernel, weak, settled: weak ? new WeakMap() : new Map() });
    this.drop();
  }
  drop() { this.recent = this.weak ? new WeakMap() : new Map(); }
  get(key) { return this.recent.get(key) ?? this.settled.get(key); }
  has(key) { return this.recent.has(key) || this.settled.has(key); }
  set(key, value, id = key) { (id < this.kernel.settled ? this.settled : this.recent).set(key, value); return this; }
  // A node by a term and its key, for encode. An encoding against a scope
  // is kept for the declaration only, as its scope is.
  node(term, key) { return this.recent.get(term)?.get(key) ?? this.settled.get(term)?.get(key); }
  setNode(term, key, id, scoped = false) {
    const tier = id < this.kernel.settled && !scoped ? this.settled : this.recent;
    if (!tier.has(term)) tier.set(term, new Map());
    tier.get(term).set(key, id);
  }
}
export class CubicalSyntax {
  constructor(kernel) {
    this.kernel = kernel;
    this.encoded = new NodeCache(kernel, true);
    this.decoded = new NodeCache(kernel);
    this.free = new NodeCache(kernel);
    // Each term's head normal form, by its node (cubical-elaborator.mjs).
    this.heads = new NodeCache(kernel);
    // The scopes and the chains of binders open encodings are kept by.
    this.scopeNumbers = new WeakMap(); this.scopes = 0; this.chains = new Map();
    // A decoded term whose node mentions a variable, by that node: encoded
    // again as the node, so that a checked term keeps what its syntax omits
    // (a path application's annotation), where every variable the node
    // mentions, the annotation's included, is the scope's or the term's
    // own (encodeAt, keep).
    this.roundTrips = new NodeCache(kernel, true);
    // What each node mentions, its annotations included (references,
    // annotatedDimensions).
    this.symbolsIn = new NodeCache(kernel);
    this.annotatedFree = new NodeCache(kernel);
  }
  // Handles made since a checkpoint move when it is committed or rolled
  // back: what was read of them is dropped then.
  reset() {
    for (const cache of [this.encoded, this.roundTrips, this.decoded, this.free, this.heads, this.symbolsIn, this.annotatedFree]) cache.drop();
  }
  // The dimensions free in a node, as a bit mask (freeDimensionMask), and
  // those with its annotations'.
  freeDimensions(id) { return freeDimensionMask(this.kernel, id, this.free); }
  annotatedDimensions(id) { return freeDimensionMask(this.kernel, id, this.annotatedFree, true); }
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
  // A term as kernel syntax, against `scope`: the driver's map from the
  // symbols of a context's variables to their entries, made before the term
  // is encoded (scope first; InstructionDriver.scopeOf). A variable must be
  // bound by a binder of the term around it or be an entry of the scope
  // (web/cubical-variables.mjs, variableTerm). `dimensions` names the
  // interval dimensions in scope.
  encode(term, dimensions = new Map(), scope = EMPTY_SCOPE) {
    return this.encodeAt(term, dimensions, dimensionContextKey(dimensions), scope, null);
  }
  // `key` is the dimensions' context key, the same for each part encoded in
  // the same dimensions, so computed once for them; `binders` the chain of
  // the term's own binders around the part. A part with no free variable
  // encodes alike in every scope and under any binders, and is kept by its
  // dimensions alone, from one declaration to the next; an open one is kept
  // by its scope and its binders too, for the declaration.
  encodeAt(term, dimensions, key, scope, binders) {
    if (!term || typeof term !== "object") throw new TypeError("Expected cubical syntax.");
    const open = !this.closed(term), at = open ? `${key}|${this.scopeNumber(scope)}|${binders?.id ?? 0}` : key;
    const cached = this.encoded.node(term, at);
    if (cached) return cached;
    // A decoded object encodes back to its own node only where every
    // variable the node mentions, those only its annotations mention
    // included, is bound by the term around it or is an entry of the scope;
    // elsewhere it is encoded from its syntax, which refuses a variable its
    // syntax names that is neither.
    const k = this.kernel, decoded = this.roundTrips.node(term, key);
    if (decoded && [...this.references(decoded)].every(symbol =>
      this.binds(binders, k.symbolName(symbol)) || typeof scope.get(symbol) === "number")) return decoded;
    const child = t => this.encodeAt(t, dimensions, key, scope, binders);
    const node = (payload = 0, ...children) => k.term(term.tag, payload, ...children);
    const level = l => this.encodeLevel(l, scope, binders);
    // A binder's body, under one more binder of the term's own.
    const body = t => this.encodeAt(t, dimensions, key, scope, this.binder(term.name, binders));
    let result;
    switch (term.tag) {
      case "DefRef":
        result = k.definitions.get(term.name);
        if (!result) throw new Error(`Unknown checked cubical definition: ${term.name}`);
        break;
      case "U": result = node(0, level(term.level)); break;
      case "Var": result = variableTerm(k, term.name, this.binds(binders, term.name), scope); break;
      case "Unit": case "Point": case "Void": result = node(); break;
      case "Pi": case "Lam": case "Sigma":
        result = binderTerm(k, term.tag, term.name, child(term.domain), body(term.body)); break;
      case "App": result = node(0, child(term.fn), child(term.arg)); break;
      case "Pair": result = node(0, child(term.as), child(term.first), child(term.second)); break;
      case "Fst": case "Snd": result = node(0, child(term.pair)); break;
      case "Path": case "PLam": case "Comp": case "HComp": case "Trans": {
        const { dim, inner } = bindDimensions(term, dimensions), innerKey = dimensionContextKey(inner);
        const within = t => this.encodeAt(t, inner, innerKey, scope, binders);
        const family = term.tag === "HComp" ? child(term.family) : within(term.family);
        if (term.tag === "Path") result = node(dim, family, child(term.left), child(term.right));
        else if (term.tag === "PLam") result = node(dim, family, within(term.body));
        else if (term.tag === "Trans") {
          const base = child(term.base);
          const descriptor = k.term("Tube", this.formula(term.face, "face", dimensions), base, 0);
          result = node(dim, family, descriptor, base);
        } else {
          let tubes = 0;
          for (const part of [...term.system].reverse())
            tubes = k.term("Tube", this.formula(part.face, "face", dimensions), within(part.term), tubes);
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
      case "LPi": case "LLam": result = binderTerm(k, term.tag, term.name, k.term("LBound", 1), body(term.body)); break;
      case "LApp": result = node(0, child(term.fn), level(term.level)); break;
      // A universe variable's bound, as the type of its context entry.
      case "LBound": result = node(term.tier ?? 1); break;
      // Declared types (H1): an instance S{ls}(as) of an admitted signature,
      // named as its declaration registered it (web/cubical-signatures.mjs);
      // constructor number `index` of an instance; an eliminator with its
      // motive and one clause per constructor, the squash's included.
      case "Sort":
        result = node(this.signatureIndex(term.signature), this.list(term.parameters ?? [], child), this.list(term.levels ?? [], level));
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
    this.encoded.setNode(term, at, result, open);
    // Cache keys are immutable syntax, so a later mutation cannot accidentally
    // display new text while reusing the earlier checked term.
    if (term.system) { term.system.forEach(Object.freeze); Object.freeze(term.system); }
    for (const items of [term.parameters, term.levels, term.clauses]) if (Array.isArray(items)) Object.freeze(items);
    Object.freeze(term);
    return result;
  }
  // A scope's number, for the encoding cache's keys: a scope is made once
  // and never changes (InstructionDriver.extendScope).
  scopeNumber(scope) {
    let number = this.scopeNumbers.get(scope);
    if (number === undefined) this.scopeNumbers.set(scope, number = ++this.scopes);
    return number;
  }
  // The chain of binders around a part with one more, innermost: one object
  // for each chain, so that its id keys the encoding cache.
  binder(name, next) {
    const key = `${next?.id ?? 0} ${name}`;
    let chain = this.chains.get(key);
    if (!chain) this.chains.set(key, chain = { name, next, id: this.chains.size + 1 });
    return chain;
  }
  binds(binders, name) {
    for (let binder = binders; binder; binder = binder.next) if (binder.name === name) return true;
    return false;
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
  // constructor names, as its declaration gave them. The kernel's own
  // symbols for them are not read.
  signatureRecord(index) {
    const record = this.kernel.signatureRecords.get(index);
    if (!record) throw new Error(`No declared type is registered at signature ${index}.`);
    return record;
  }
  // A universe's level (web/cubical-levels.mjs): a number is a tier-0
  // constant. The kernel takes it to normal form; this only encodes it. Its
  // variables are bound by the term's level binders or entries of `scope`.
  encodeLevel(level, scope = EMPTY_SCOPE, binders = null) {
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
      case "LSucc": return k.term("LSucc", level.count, this.encodeLevel(level.level, scope, binders));
      case "LMax": return k.term("LMax", 0, this.encodeLevel(level.left, scope, binders), this.encodeLevel(level.right, scope, binders));
      case "Var": return variableTerm(k, level.name, this.binds(binders, level.name), scope);
      default: throw new Error("Expected a universe level.");
    }
  }
  decodeLevel(id, names = null) {
    const node = this.kernel.node(id), { kind, payload, children } = node;
    switch (kind) {
      case "LConst": return payload <= 0xffff ? payload : { tag: "LConst", tier: payload >>> 16, value: payload & 0xffff };
      case "LSucc": return { tag: "LSucc", count: payload, level: this.decodeLevel(children[0], names) };
      case "LMax": return { tag: "LMax", left: this.decodeLevel(children[0], names), right: this.decodeLevel(children[1], names) };
      case "Var": return { tag: "Var", name: variableName(this.kernel, node, names) };
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
  // `names` are the binders around the node, which name its bound variables
  // (web/cubical-variables.mjs, variableName).
  decode(id, dimensions = new Map(), names = null) {
    const encodingKey = dimensionContextKey(dimensions);
    // A node's decoding depends only on the names of its free dimensions, so
    // it is decoded, and cached, under those alone. A binder inside may then
    // reuse the name of a dimension the node does not mention. On ABI 3 a
    // variable is named by its symbol wherever it is bound, so the binders
    // around a node do not change its decoding either.
    const free = this.freeDimensions(id);
    const assigned = [...dimensions.values()].reduce((mask, index) => mask | 1n << BigInt(index), 0n);
    // The node is kept for the encoder in this context when the context
    // names every dimension it mentions, its annotations' too; under the
    // dimensions its syntax mentions alone only when its annotations
    // mention no other (keep).
    const annotated = this.annotatedDimensions(id), completeContext = (annotated & ~assigned) === 0n;
    if ([...dimensions.values()].some(index => !(free & 1n << BigInt(index))))
      dimensions = new Map([...dimensions].filter(([, index]) => free & 1n << BigInt(index)));
    // In no dimension context, as most nodes are, the node alone.
    const cacheKey = dimensions.size ? JSON.stringify([id,dimensionContextKey(dimensions)]) : id;
    if (this.decoded.has(cacheKey)) {
      const result = this.decoded.get(cacheKey);
      if (completeContext) this.keep(result, id, encodingKey);
      return result;
    }
    const node = this.kernel.node(id), { kind: tag, payload, children: c } = node;
    const child = i => this.decode(c[i], dimensions, names), body = i => this.decode(c[i], dimensions, pushName(this.kernel, node, names));
    let dim = `d${payload}`;
    while (dimensions.has(dim)) dim += "_";
    const inner = new Map(dimensions).set(dim, payload);
    const boundChild = i => this.decode(c[i], inner, names);
    let result = { tag };
    switch (tag) {
      case "DefRef": result.name = this.kernel.definitionName(id); break;
      case "U": result.level = this.decodeLevel(c[0], names); break;
      case "LPi": case "LLam": Object.assign(result, { name: binderName(this.kernel, node), body: body(1) }); break;
      case "LApp": Object.assign(result, { fn: child(0), level: this.decodeLevel(c[1], names) }); break;
      case "LBound": result.tier = payload; break;
      case "Var": result.name = variableName(this.kernel, node, names); break;
      case "Unit": case "Point": case "Void": break;
      case "Pi": case "Lam": case "Sigma":
        Object.assign(result, { name: binderName(this.kernel, node), domain: child(0), body: body(1) }); break;
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
          system.push({ face: this.decodeFormula(n.payload, dimensions), term: this.decode(n.children[0], inner, names) });
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
            system.push({ face, type: this.decode(n.children[0], dimensions, names), equiv: this.decode(n.children[1], dimensions, names) });
            part = n.children[2];
          } else {
            if (n.kind !== "Tube") throw new Error("Invalid cubical Glue element system.");
            system.push({ face, term: this.decode(n.children[0], dimensions, names) }); part = n.children[1];
          }
        }
        Object.assign(result, tag === "Glue" ? { base: child(0), system } : { as: child(0), base: child(1), system }); break;
      }
      case "Unglue": Object.assign(result, { as: child(0), value: child(1) }); break;
      case "Sort":
        Object.assign(result, { signature: this.signatureRecord(payload).name,
          parameters: this.items(c[0]).map(item => this.decode(item, dimensions, names)),
          levels: this.items(c[1]).map(level => this.decodeLevel(level, names)) });
        break;
      case "Con": {
        const sort = this.kernel.node(c[0]);
        const name = sort.kind === "Sort" ? this.signatureRecord(sort.payload).constructors[payload] : undefined;
        Object.assign(result, { index: payload, ...(name ? { name } : {}), sort: child(0) });
        break;
      }
      case "Elim":
        Object.assign(result, { signature: this.signatureRecord(payload).name, motive: child(0),
          clauses: this.items(c[1]).map(item => this.decode(item, dimensions, names)) });
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
    if (annotated === free) this.keep(result, id, dimensionContextKey(dimensions));
    // Encoding uses the caller's full context. Decoding ignores unused
    // dimensions for sharing, but must also preserve the checked node in
    // that original context, including when a later decode hits the cache.
    // An inspection context can omit indices and use fallback names; those
    // names need not encode back to the original slots. New binder contexts
    // likewise still require derivation before head queries.
    if (completeContext) this.keep(result, id, encodingKey);
    this.decoded.set(cacheKey, result, id);
    return result;
  }
  // A decoded object kept for the encoder, to encode back to its own node in
  // the dimension context `key`: with the closed syntax, by its dimensions
  // alone, when neither it nor its node mentions a variable; otherwise as a
  // round trip, which the encoder checks against the scope it encodes in,
  // kept for the declaration only, as its variables' entries are.
  keep(result, id, key) {
    if (this.closed(result) && !this.references(id).size) this.encoded.setNode(result, key, id);
    else this.roundTrips.setNode(result, key, id, true);
  }
  // Whether syntax has no free variable, and so encodes alike in every scope.
  closed(term) { return !isTerm(term) || !freeNames(term).size; }
  // The term and level symbols a node mentions that no binder in it binds,
  // its annotations' included: a checked path application's type, which
  // its syntax omits, may mention a variable the syntax does not.
  references(id) {
    let symbols = this.symbolsIn.get(id);
    if (symbols) return symbols;
    const node = this.kernel.node(id);
    symbols = new Set(node.kind === "Var" ? [referenceSymbol(node)] : []);
    node.children.forEach((child, i) => {
      if (child) for (const symbol of this.references(child))
        if (!(i === 1 && binders.has(node.kind) && symbol === boundSymbol(node))) symbols.add(symbol);
    });
    this.symbolsIn.set(id, symbols, id);
    return symbols;
  }}
