import { bindDimensions } from "./translator/dimension-slots.mjs";
import { dimensionContextKey } from "./translator/syntax-graph.mjs";
import { freeNames, isTerm } from "./translator/core.mjs";
import { termParts } from "./translator/term-shape.mjs";
import { binderTerm, binders as BINDERS, pushName, shownBinderName, variableName, variableTerm } from "./cubical-variables.mjs";
// The scope of no context: what is encoded against it is closed.
export const EMPTY_SCOPE = Object.freeze(new Map());
// Lossless syntax transport between named cubical ASTs and C arena handles.
// This layer never decides typing or equality. Every checked result comes
// from CubicalKernel.check; shared input objects retain shared arena nodes.
// The dimensions free in a node, as a bit mask, memoized in `memo`. A path
// application's kernel annotation is counted only when `annotated`: its
// decoding carries the annotation, and the driver's alpha equality does not
// read it.
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
// What a decoding's names depend on, each given by its caller: an argument
// left out is an error, not a default.
function required(decoder, args) {
  for (const [name, value] of Object.entries(args))
    if (value === undefined) throw new TypeError(`${decoder} takes ${name}: null for none, never left out.`);
}
// What a node is decoded in: the names its dimensions take (`dimensions`,
// and `key`, their context key), those of the binders around it (`names`,
// a chain {name, next} innermost first, one object for each chain:
// CubicalSyntax.binder) and those its entries take (`naming`). What is
// decoded in it is kept by the node alone, and so are the contexts its
// parts are decoded in, each made once from this one: so a part met again
// is found without reading its names again. Contexts hold node handles,
// and are dropped with the decodings (CubicalSyntax.reset and decode).
class DecodingContext {
  constructor(syntax, dimensions, key, names, naming) {
    Object.assign(this, { syntax, dimensions, key, names, naming });
    this.assigned = [...dimensions.values()].reduce((mask, index) => mask | 1n << BigInt(index), 0n);
    this.decodings = new Map();
    this.restrictions = new Map(); this.bodies = new Map(); this.dimensionBinders = new Map();
  }
  // The context with only the dimensions in `free`, a node's free mask.
  restrictedTo(free) {
    if (!(this.assigned & ~free)) return this;
    const kept = this.assigned & free;
    let context = this.restrictions.get(kept);
    if (!context) {
      const dimensions = new Map([...this.dimensions].filter(([, index]) => free & 1n << BigInt(index)));
      this.restrictions.set(kept, context = new DecodingContext(this.syntax, dimensions, dimensionContextKey(dimensions), this.names, this.naming));
    }
    return context;
  }
  // A binder's body: one more binder around it, shown as `name`.
  under(name) {
    let context = this.bodies.get(name);
    if (!context) this.bodies.set(name, context = new DecodingContext(this.syntax, this.dimensions, this.key, this.syntax.binder(name, this.names), this.naming));
    return context;
  }
  // A dimension binder's: the name it shows dimension `index` by, d`index`
  // apart from the names in scope, and the context of its parts.
  dimensionBinder(index) {
    let binder = this.dimensionBinders.get(index);
    if (!binder) {
      let name = `d${index}`;
      while (this.dimensions.has(name)) name += "_";
      const dimensions = new Map(this.dimensions).set(name, index);
      binder = { name, context: new DecodingContext(this.syntax, dimensions, dimensionContextKey(dimensions), this.names, this.naming) };
      this.dimensionBinders.set(index, binder);
    }
    return binder;
  }
}
export class CubicalSyntax {
  constructor(kernel) {
    this.kernel = kernel;
    this.encoded = new NodeCache(kernel, true);
    this.decoded = new NodeCache(kernel);
    this.namesEpoch = kernel.binderNames.epoch;
    // The contexts decodings start in, by their naming (NO_NAMING for none),
    // their dimensions and their binders (contextOf); the names each set of
    // entries a naming meets takes there (shownEntries).
    this.contexts = new WeakMap(); this.entryNamings = new WeakMap();
    this.free = new NodeCache(kernel);
    // Each term's head normal form, by its node (cubical-elaborator.mjs).
    this.heads = new NodeCache(kernel);
    // Each node's loose range (one more than its greatest loose index), and
    // the entries it mentions: what its decoding depends on.
    this.loose = new NodeCache(kernel);
    this.mentioned = new NodeCache(kernel);
    // The scopes and the chains of binders open encodings are kept by.
    this.scopeNumbers = new WeakMap(); this.scopes = 0; this.chains = new Map();
  }
  // Handles made since a checkpoint move when it is committed or rolled
  // back: what was read of them is dropped then.
  reset() {
    for (const cache of [this.encoded, this.decoded, this.free, this.heads, this.loose, this.mentioned]) cache.drop();
    this.contexts = new WeakMap(); this.entryNamings = new WeakMap();
  }
  // A node's loose range, as the kernel's `loose` (term_internal.h): one
  // more than its greatest loose Bound index, 0 when locally closed.
  looseOf(id) {
    if (!id) return 0;
    let known = this.loose.get(id);
    if (known !== undefined) return known;
    const node = this.kernel.node(id);
    known = node.kind === "Bound" ? node.payload + 1 : 0;
    node.children.forEach((child, i) => {
      if (!child) return;
      const inner = this.looseOf(child), reach = i === 1 && BINDERS.has(node.kind) && inner ? inner - 1 : inner;
      if (reach > known) known = reach;
    });
    this.loose.set(id, known);
    return known;
  }
  // The entries a node mentions (Context), as a set shared where it can be.
  entriesOf(id) {
    if (!id) return NONE;
    let known = this.mentioned.get(id);
    if (known) return known;
    const node = this.kernel.node(id);
    if (node.kind === "Context") known = new Set([node.payload]);
    else {
      const parts = node.children.filter(Boolean).map(child => this.entriesOf(child)).filter(set => set.size);
      known = !parts.length ? NONE : parts.length === 1 ? parts[0] : new Set(parts.flatMap(set => [...set]));
    }
    this.mentioned.set(id, known);
    return known;
  }
  // The dimensions free in a node, as a bit mask (freeDimensionMask), a path
  // application's annotation included: its decoding carries the annotation.
  freeDimensions(id) { return freeDimensionMask(this.kernel, id, this.free, true); }
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
  // bound by a binder of the term around it, and is then Bound by its depth,
  // or be an entry of the scope, Context of it (web/cubical-variables.mjs,
  // variableTerm). `dimensions` names the interval dimensions in scope.
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
    const k = this.kernel, child = t => this.encodeAt(t, dimensions, key, scope, binders);
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
      case "Var": result = variableTerm(k, term.name, binders, scope); break;
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
      // A checked application keeps its path's type, the kernel's annotation.
      case "PApp": result = node(this.formula(term.arg, "interval", dimensions), child(term.path), term.pathType ? child(term.pathType) : 0); break;
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
  // for each chain, so that its id keys the encoding cache, and the
  // decoding's (prefix).
  binder(name, next) {
    const key = `${next?.id ?? 0} ${name}`;
    let chain = this.chains.get(key);
    if (!chain) this.chains.set(key, chain = { name, next, id: this.chains.size + 1, length: (next?.length ?? 0) + 1 });
    return chain;
  }
  // A chain {name, next} as the one object for it (binder).
  interned(names) {
    if (!names) return null;
    const key = `${names.next?.id ?? 0} ${names.name}`;
    return this.chains.get(key) === names ? names : this.binder(names.name, this.interned(names.next));
  }
  // The innermost `length` binders of a chain, as a chain: what names a
  // node's loose indices, when `length` is its loose range.
  prefix(chain, length) {
    if (!chain || !length) return null;
    if (chain.length <= length) return chain;
    let prefix = (chain.prefixes ??= new Map()).get(length);
    if (prefix === undefined) chain.prefixes.set(length, prefix = this.binder(chain.name, this.prefix(chain.next, length - 1)));
    return prefix;
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
      case "Var": return variableTerm(k, level.name, binders, scope);
      default: throw new Error("Expected a universe level.");
    }
  }
  // A level, under the binders `names` and with its entries named by
  // `naming`, both required, as decode's.
  decodeLevel(id, names, naming) {
    required("decodeLevel", { names, naming });
    const node = this.kernel.node(id), { kind, payload, children } = node;
    switch (kind) {
      case "LConst": return payload <= 0xffff ? payload : { tag: "LConst", tier: payload >>> 16, value: payload & 0xffff };
      case "LSucc": return { tag: "LSucc", count: payload, level: this.decodeLevel(children[0], names, naming) };
      case "LMax": return { tag: "LMax", left: this.decodeLevel(children[0], names, naming), right: this.decodeLevel(children[1], names, naming) };
      case "Bound": case "Context": return { tag: "Var", name: variableName(this.kernel, node, names, naming) };
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
  // A term closed over a telescope, as a signature's constructor types are,
  // decoded with the telescope's names, `telescope` outermost first.
  decodeOver(id, telescope, dimensions, naming) {
    required("decodeOver", { dimensions, naming });
    let names = null;
    for (const name of telescope) names = pushName(name, names);
    return this.decode(id, dimensions, names, naming);
  }
  // The name a binder node shows under the binders `names`, its entries
  // named by `naming`: its own (binderName), unless that would capture a
  // variable its body refers to otherwise, an outer binder's, by the body's
  // loose indices past its own, or an entry's. The one source of binder
  // names: decode names binders by it, and so does every traversal that
  // names the binders above a subterm (kernelOccurrence, the graph view's
  // highlights, the workbench's operands), so that a subterm's variables
  // read as the whole term's do.
  binderShownName(id, names, naming) {
    required("binderShownName", { names, naming });
    const body = this.kernel.node(id).children[1], avoid = new Set();
    let binder = names;
    for (let i = 0; i < this.looseOf(body) - 1 && binder; i++, binder = binder.next) avoid.add(binder.name);
    for (const entry of this.entriesOf(body)) avoid.add(variableName(this.kernel, { kind: "Context", payload: entry }, null, naming));
    this.kernel.binderNames.shown(id);
    return shownBinderName(this.kernel, id, avoid);
  }
  // `names` are the binders around the node, a chain {name, next} innermost
  // first, which name its loose indices, and `naming` the names a view
  // shows entries by, a map from entries to names, each other entry shown by
  // its spelling (web/cubical-variables.mjs, variableName). Each is
  // required: a caller says null for no binders around, and null for the
  // session's spellings, as a closed term or a term in no view takes, so
  // that one decoding an open term without its view's naming is found
  // (required).
  decode(id, dimensions, names, naming) {
    required("decode", { dimensions, names, naming });
    // A binder shown unnamed has since been named: no decoding kept shows it.
    const { epoch } = this.kernel.binderNames;
    if (epoch !== this.namesEpoch) {
      this.decoded = new NodeCache(this.kernel);
      this.contexts = new WeakMap();
      this.namesEpoch = epoch;
    }
    return this.decodeIn(id, this.contextOf(dimensions, names, naming));
  }
  // The context a decoding starts in (DecodingContext): one for each
  // naming, binders and dimensions in their order.
  contextOf(dimensions, names, naming) {
    const chain = this.interned(names);
    if (!this.contexts.has(naming ?? NO_NAMING)) this.contexts.set(naming ?? NO_NAMING, new Map());
    const contexts = this.contexts.get(naming ?? NO_NAMING), key = `${chain?.id ?? 0} ${JSON.stringify([...dimensions])}`;
    let context = contexts.get(key);
    if (!context) contexts.set(key, context = new DecodingContext(this, new Map(dimensions), dimensionContextKey(dimensions), chain, naming));
    return context;
  }
  // The names a set of entries takes in `naming`, in the entries' order, as
  // one key: read once for each set a naming meets, as entriesOf shares
  // them.
  shownEntries(entries, naming) {
    if (!this.entryNamings.has(naming ?? NO_NAMING)) this.entryNamings.set(naming ?? NO_NAMING, new WeakMap());
    const known = this.entryNamings.get(naming ?? NO_NAMING);
    let shown = known.get(entries);
    if (shown === undefined) {
      shown = [...entries].sort((a, b) => a - b).map(entry => variableName(this.kernel, { kind: "Context", payload: entry }, null, naming)).join("\0");
      known.set(entries, shown);
    }
    return shown;
  }
  // A node decoded in a context: found by the node there, or decoded.
  decodeIn(id, context) {
    let result = context.decodings.get(id);
    if (result === undefined) context.decodings.set(id, result = this.decodeNode(id, context));
    return result;
  }
  decodeNode(id, context) {
    // A node's decoding depends on the names of its free dimensions, on the
    // names its loose indices take and on those its entries take, so it is
    // decoded, and cached, under those alone. A binder
    // inside may then reuse the name of a dimension the node does not
    // mention.
    const free = this.freeDimensions(id), completeContext = (free & ~context.assigned) === 0n;
    const within = context.restrictedTo(free), { dimensions, names, naming } = within;
    const loose = this.looseOf(id), entries = this.entriesOf(id);
    // In no dimension context, as most nodes are, and closed, the node alone;
    // otherwise also the names its loose indices take (the binders around it
    // that name them) and those its entries take.
    const cacheKey = dimensions.size || loose || entries.size
      ? `${id}\0${within.key}\0${this.prefix(names, loose)?.id ?? 0}\0${this.shownEntries(entries, naming)}` : id;
    const known = this.decoded.get(cacheKey);
    if (known !== undefined) {
      if (completeContext && this.closed(known)) this.encoded.setNode(known, context.key, id);
      return known;
    }
    const node = this.kernel.node(id), { kind: tag, payload, children: c } = node;
    // A part of the node, decoded in the context it is under.
    const part = (handle, inner) => this.decodeIn(handle, inner);
    const child = i => part(c[i], within);
    // A binder's own name, unless it would capture a variable its body refers
    // to otherwise: an outer binder's, by the body's loose indices past its
    // own, or an entry's.
    const binder = () => this.binderShownName(id, names, naming);
    let bound;
    const body = i => part(c[i], within.under(bound));
    // A dimension binder's dimension, and its parts.
    const dimensionBinder = () => within.dimensionBinder(payload);
    const boundChild = i => part(c[i], dimensionBinder().context);
    let result = { tag };
    switch (tag) {
      case "DefRef": result.name = this.kernel.definitionName(id); break;
      case "U": result.level = this.decodeLevel(c[0], names, naming); break;
      case "LPi": case "LLam": bound = binder(); Object.assign(result, { name: bound, body: body(1) }); break;
      case "LApp": Object.assign(result, { fn: child(0), level: this.decodeLevel(c[1], names, naming) }); break;
      case "LBound": result.tier = payload; break;
      // A variable, bound or an entry, is a Var of the name it goes by here.
      case "Bound": case "Context": result = { tag: "Var", name: variableName(this.kernel, node, names, naming) }; break;
      case "Unit": case "Point": case "Void": break;
      case "Pi": case "Lam": case "Sigma":
        bound = binder(); Object.assign(result, { name: bound, domain: child(0), body: body(1) }); break;
      case "App": Object.assign(result, { fn: child(0), arg: child(1) }); break;
      case "Pair": Object.assign(result, { as: child(0), first: child(1), second: child(2) }); break;
      case "Fst": case "Snd": result.pair = child(0); break;
      case "Path": Object.assign(result, { dim: dimensionBinder().name, family: boundChild(0), left: child(1), right: child(2) }); break;
      case "PLam": Object.assign(result, { dim: dimensionBinder().name, family: boundChild(0), body: boundChild(1) }); break;
      case "PApp": Object.assign(result, { path: child(0), arg: this.decodeFormula(payload, dimensions), ...c[1] ? { pathType: child(1) } : {} }); break;
      case "Trans": {
        const descriptor = this.kernel.node(c[1]);
        if (descriptor.kind !== "Tube" || descriptor.children[1]) throw new Error("Invalid transport face descriptor.");
        Object.assign(result, { dim: dimensionBinder().name, family: boundChild(0), face: this.decodeFormula(descriptor.payload, dimensions), base: child(2) });
        break;
      }
      case "Comp": case "HComp": {
        const system = [];
        for (let tube = c[1]; tube;) {
          const n = this.kernel.node(tube);
          if (n.kind !== "Tube") throw new Error("Invalid cubical tube list.");
          system.push({ face: this.decodeFormula(n.payload, dimensions), term: part(n.children[0], dimensionBinder().context) });
          tube = n.children[1];
        }
        Object.assign(result, { dim: dimensionBinder().name, family: tag === "HComp" ? child(0) : boundChild(0), system, base: child(2) }); break;
      }
      case "Abort": Object.assign(result, { as: child(0), impossible: child(1) }); break;
      case "Sum": Object.assign(result, { left: child(0), right: child(1) }); break;
      case "Inl": case "Inr": Object.assign(result, { as: child(0), value: child(1) }); break;
      case "SumRec": Object.assign(result, { motive: child(0), left: child(1), right: child(2), value: child(3) }); break;
      case "UnitRec": Object.assign(result, { motive: child(0), point: child(1), value: child(2) }); break;
      case "Glue": case "GlueTerm": {
        const system = [];
        for (let link = c[tag === "Glue" ? 1 : 2]; link;) {
          const n = this.kernel.node(link), face = this.decodeFormula(n.payload, dimensions);
          if (tag === "Glue") {
            if (n.kind !== "GlueSystem") throw new Error("Invalid cubical Glue system.");
            system.push({ face, type: part(n.children[0], within), equiv: part(n.children[1], within) });
            link = n.children[2];
          } else {
            if (n.kind !== "Tube") throw new Error("Invalid cubical Glue element system.");
            system.push({ face, term: part(n.children[0], within) }); link = n.children[1];
          }
        }
        Object.assign(result, tag === "Glue" ? { base: child(0), system } : { as: child(0), base: child(1), system }); break;
      }
      case "Unglue": Object.assign(result, { as: child(0), value: child(1) }); break;
      case "Sort":
        Object.assign(result, { signature: this.signatureRecord(payload).name,
          parameters: this.items(c[0]).map(item => part(item, within)),
          levels: this.items(c[1]).map(level => this.decodeLevel(level, names, naming)) });
        break;
      case "Con": {
        const sort = this.kernel.node(c[0]);
        const name = sort.kind === "Sort" ? this.signatureRecord(sort.payload).constructors[payload] : undefined;
        Object.assign(result, { index: payload, ...(name ? { name } : {}), sort: child(0) });
        break;
      }
      case "Elim":
        Object.assign(result, { signature: this.signatureRecord(payload).name, motive: child(0),
          clauses: this.items(c[1]).map(item => part(item, within)) });
        break;
      default: throw new Error(`Unsupported cubical node: ${tag}`);
    }
    // The decoded object is immutable: shared parts stay shared, and what is
    // known of a part, as its free names, stays known. A checked path
    // application's annotation is syntax of its own (pathType), so the
    // object alone encodes back to its node, wherever what it names is.
    const freeze = value => {
      if (value && typeof value === "object" && !Object.isFrozen(value)) {
        termParts(value).forEach(freeze); Object.freeze(value);
      }
    };
    freeze(result);
    // A closed object encodes alike in every scope: it is kept for the
    // encoder by the dimensions it mentions and by the caller's full
    // context, which encoding uses, also when a later decode hits the cache.
    // An inspection context can omit indices and use fallback names; those
    // names need not encode back to the original slots.
    if (this.closed(result)) {
      this.encoded.setNode(result, within.key, id);
      if (completeContext) this.encoded.setNode(result, context.key, id);
    }
    this.decoded.set(cacheKey, result, id);
    return result;
  }
  // Whether syntax has no free variable, and so encodes alike in every scope.
  closed(term) { return !isTerm(term) || !freeNames(term).size; }}
const NONE = Object.freeze(new Set());
// The key of no naming, in the maps kept by naming.
const NO_NAMING = Object.freeze({});
