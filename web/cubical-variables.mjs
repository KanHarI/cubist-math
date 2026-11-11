// Variables and binders, read and built in one place
// (docs/roadmaps/kernel/locally-nameless-kernel.md, sections 5 and 7). The
// driver reads a term or level binder here, opens its body with an entry,
// builds a binder over an entry, names a variable's role and keys a level
// variable by it; the decoder names variables through a stack of binders;
// signature admission passes its entries here; and EntryNames gives each
// entry the driver makes its name.
//
// The kernel keeps no names (ABI 4). A term or level binder carries no name
// and binds index 0 of its body; a variable is Bound(i), the variable of the
// i-th enclosing binder, 0 the innermost, or Context(e), a reference to the
// context entry e. Every name the driver shows is its own: a binder's is the
// one it was encoded with (kernel.binderNames), or one made up.

import { assumptionMark } from "./translator/names.mjs";
export const termBinders = new Set(["Pi", "Lam", "Sigma"]);
export const levelBinders = new Set(["LPi", "LLam"]);
// Term and level binders form one chain of indices.
export const binders = new Set([...termBinders, ...levelBinders]);
// The kinds of a variable: a bound one, by index, and an entry, by its id.
export const variables = new Set(["Bound", "Context"]);

// A variable's role: bound, by its index, or a context reference, by its
// entry. Two variables at the same depth are the same exactly when their
// roles are, so a bound variable never meets an entry with the same number.
export const role = node => node.kind === "Bound" ? `bound ${node.payload}` : `context ${node.payload}`;
// Whether two variables, read at the same depth, have one role.
export const sameReference = (left, right) => left.kind === right.kind && left.payload === right.payload;
// A level variable's key in a level normal form (web/cubical-levels.mjs).
export const levelKey = node => role(node);

// A scope is the driver's map from the symbols of the variables it shows to
// their entries. Under this key, the entries of variables it holds but does
// not show, in increasing order: one shadowed by a later variable of the
// same symbol, and one a derivation's narrowed scope leaves out while a
// binder of the term could take it. A binder takes none of them, nor an
// entry shown: two variables are never one (section 3.6).
export const HIDDEN = "hidden";
export const hiddenIn = scope => scope?.get(HIDDEN) ?? [];
// A scope with `symbol`'s variable at `entry`: a variable it shadows is
// hidden, not forgotten.
export function withEntry(scope, symbol, entry) {
  const extended = new Map(scope).set(symbol, entry), shadowed = scope?.get(symbol);
  if (typeof shadowed === "number") extended.set(HIDDEN, [...new Set([...hiddenIn(scope), shadowed])].sort((a, b) => a - b));
  return extended;
}

// The name a binder node's variable goes by in the driver: the name it was
// encoded with, or, for a binder the kernel built, the stem x.
export const UNNAMED = "x";
export const binderName = (kernel, handle) => kernel.binderNames.get(handle) ?? UNNAMED;
// The name a binder's variable is bound by in the driver's scopes: its own,
// or for a binder the kernel built, which has none, a name of its node,
// x@n, as the kernel's fresh symbols were on ABI 3. Its entries are then its
// own: a term met under it never binds that name again, so a narrowed scope
// never holds them for it (InstructionDriver.narrow), however many binders
// the kernel built around it. They are spelled as x (spelledAs).
//
// A binder's key is fixed the first time it is asked for: a source encoding
// that names the node later names it for display only. Otherwise the scopes,
// the narrowings and the derivations memoized under the old key would
// disagree with the new one, and a binder could take an entry its narrowed
// scope no longer held. The keys live with the names, relocated at a commit
// and dropped at a rollback (CubicalDeclarationTransaction.finish).
export function binderKey(kernel, handle) {
  let key = kernel.binderKeys.get(handle);
  if (key === undefined) kernel.binderKeys.set(handle, key = kernel.binderNames.get(handle) ?? `${UNNAMED}@${++kernel.binderKeySerial}`);
  return key;
}
// The name an entry made for a binder's key is spelled from.
export const spelledAs = name => name.includes("@") ? UNNAMED : name;

// A binder's body opened with an entry, to derive it there: the body with
// index 0 the entry (cc_kernel_instantiate, which refuses an entry the body
// already mentions), and the scope in which the binder's name is that entry.
export function openBinder(graph, node, entry, scope) {
  const symbol = graph.kernel.symbol(binderKey(graph.kernel, node.id));
  return { body: openBody(graph.kernel, node.children[1], entry), scope: withEntry(scope, symbol, entry) };
}
// A body opened with an entry. Opening rebuilds the nodes that mention the
// binder's variable, binders among them, as new handles: each takes the name
// its original was encoded with, so that a binder inside keeps its source's
// name once opened.
export function openBody(kernel, body, entry) {
  const opened = kernel.instantiate(body, entry);
  carryBinderNames(kernel, body, opened);
  return opened;
}
// The names of `from`'s binders given to the binders of `to` in the same
// places, where `to` is `from` with some of its leaves replaced, as an
// opening's result is: only the parts that differ are walked, each once.
// With `unfold`, a definition of `from` is read as its value where `to` has
// something else there, as a normal form unfolds it: the names its binders
// had where a normal form keeps the shape of what it computed, for display.
// Two terms that only share kinds, as a computed value and the definitions
// that computed it may, pair up node by node without end: names are for
// display, so the walk stops after `budget` pairs.
export function carryBinderNames(kernel, from, to, unfold = false, budget = 100000) {
  const names = kernel.binderNames, seen = new Set(), pending = [from, to];
  while (pending.length && seen.size < budget) {
    const b = pending.pop();
    let a = pending.pop();
    if (a === b || !a || !b || seen.has(`${a},${b}`)) continue;
    seen.add(`${a},${b}`);
    let na = kernel.node(a);
    const nb = kernel.node(b);
    for (let guard = 0; unfold && na.kind === "DefRef" && nb.kind !== "DefRef" && guard < 64; guard++) {
      a = kernel.definition(a).value;
      na = kernel.node(a);
    }
    // A β-redex the computation contracted, as an ascription's
    // (λ (a : A). a)(t) is: its result is in the λ's body or in the argument.
    if (unfold && na.kind !== nb.kind && (na.kind === "App" || na.kind === "LApp")) {
      let fn = na.children[0], nf = kernel.node(fn);
      for (let guard = 0; nf.kind === "DefRef" && guard < 64; guard++) { fn = kernel.definition(fn).value; nf = kernel.node(fn); }
      if (nf.kind === "Lam" || nf.kind === "LLam") pending.push(nf.children[1], b);
      if (na.kind === "App") pending.push(na.children[1], b);
      continue;
    }
    if (na.kind !== nb.kind) continue;
    if (binders.has(na.kind) && names.has(a) && !names.has(b)) names.set(b, names.get(a));
    for (let i = 0; i < 4; i++) if (na.children[i] !== nb.children[i]) pending.push(na.children[i], nb.children[i]);
  }
}
// A binder over an entry: the instruction that discharges it from a body's
// or a codomain's judgement, abstracting it. A binder it builds that has no
// name yet, its term's and a λ's type's, goes by the entry's name, as on
// ABI 3 it went by the entry's symbol.
export function buildBinder(graph, kind, entry, body) {
  let judgement;
  switch (kind) {
    case "Pi": judgement = graph.pi(entry, body); break;
    case "Sigma": judgement = graph.sigma(entry, body); break;
    case "Lam": judgement = graph.lambda(entry, body); break;
    case "LPi": judgement = graph.levelPi(entry, body); break;
    case "LLam": judgement = graph.levelLambda(entry, body); break;
    default: throw new TypeError(`${kind} binds no variable.`);
  }
  // Abstracting the entry rebuilt the binders of the body that mention it:
  // each takes the name of the binder in its place in the body. An entry
  // made for a binder the kernel built names nothing (binderKey).
  const kernel = graph.kernel, name = kernel.entryNames.name(entry), named = !name.includes("@");
  const read = (id, field) => kernel.module._cb_judgement(kernel.handle, id, field) >>> 0;
  for (const field of kind === "Lam" || kind === "LLam" ? [1, 3] : [1]) {
    const handle = read(judgement, field);
    if (!handle) continue;
    if (named && !kernel.binderNames.has(handle)) kernel.binderNames.set(handle, name);
    carryBinderNames(kernel, read(body, field), kernel.node(handle).children[1]);
  }
  return judgement;
}

// Raw syntax as the encoder builds it from named syntax
// (web/cubical-syntax.mjs), against a scope: the driver's map from the
// symbols of a context's variables to their entries, made first (scope
// first, section 5.3). A variable is bound by one of the term's own binders
// around it, `binders`, a chain {name, next} innermost first, and is then
// Bound at that binder's depth; or it is an entry of the scope, Context of
// that entry; any other is refused, as the kernel's syntax refers to a
// context variable only as an entry that exists.
export function variableTerm(kernel, name, binders, scope) {
  let index = 0;
  for (let binder = binders; binder; binder = binder.next, index++)
    if (binder.name === name) return kernel.term("Bound", index);
  const entry = scope.get(kernel.symbol(name));
  if (typeof entry !== "number") throw unboundVariable(name);
  return kernel.term("Context", entry);
}
// A binder over its children, which carries no name: the name it was
// written with is the driver's record of the handle, the first one given.
export function binderTerm(kernel, kind, name, ...children) {
  const handle = kernel.term(kind, 0, ...children);
  if (!kernel.binderNames.has(handle)) kernel.binderNames.set(handle, name);
  return handle;
}
// The driver's own message for a variable no entry stands for, marked so
// that a derivation refuses it as deriving the variable did.
const unboundVariable = name => Object.assign(new Error(`Unbound variable ${name}.`), { unbound: name });

// Decoding. `names` is the stack of the binders around a node, a chain
// {name, next} innermost first, and `naming` maps an entry to the name a
// view shows it by (a scope's, NamesOfScope), every other entry shown by its
// spelling (EntryNames). A bound variable is named by its binder.
export function variableName(kernel, node, names = null, naming = null) {
  if (node.kind === "Bound") {
    let binder = names;
    for (let i = 0; binder && i < node.payload; i++) binder = binder.next;
    if (!binder) throw new Error(`A bound variable has no binder around it (index ${node.payload}).`);
    return binder.name;
  }
  return naming?.get(node.payload) ?? kernel.entryNames.spelled(node.payload);
}
export const pushName = (name, names) => ({ name, next: names });
// The name a decoded binder shows: its own (binderName), unless that would
// capture a variable its body refers to otherwise, an outer binder's or an
// entry's, `avoid`; then the first numbered name, x1, x2, …, that would not,
// numbered as a generated name is (web/translator/names.mjs, NameSupply), so
// that the display shows it by its stem where it can and the printed text
// parses. Of what the session records it reads only its own name's stem
// (EntryNames.stemOf), which never changes once read: so it is the same
// however often it is asked.
export function shownBinderName(kernel, handle, avoid) {
  const own = binderName(kernel, handle);
  if (!avoid.has(own)) return own;
  const stem = kernel.entryNames.stemOf(own);
  const base = /[0-9]$/.test(stem) || /^U+$/.test(stem) ? `${stem}_` : stem;
  for (let suffix = 1; ; suffix++) {
    const variant = `${base}${suffix}`;
    if (avoid.has(variant)) continue;
    kernel.entryNames.variantOf(variant, stem);
    return variant;
  }
}

// Signature admission over entries (the H1 specification's 6.1, section 3.4
// of the design): the parameters' entries and the sort's begin it, and each
// constructor's entry names the constructor in the later ones' types.
export const signatureBegin = (graph, former, modifier, parameters, sort, recorded = 0) =>
  graph.signatureBegin(former, modifier, parameters, sort, recorded);
export const signatureConstructor = (graph, signature, type, entry) =>
  graph.signatureConstructor(signature, type, entry);

// A level entry's place in the records below, where a term entry has its
// type's handle.
export const LEVEL = "level";
// The children alpha-equality compares as syntax: none of a universe's, and
// only the first of a path application (not its annotation), of a level
// instantiation (not its level) and of an instance (not its recorded levels).
const partsCompared = kind => kind === "U" ? 0 : kind === "PApp" || kind === "LApp" || kind === "Sort" ? 1 : 4;
// The names of the term and level entries a session makes, kept by the kernel
// wrapper beside its definitions (section 5.3): a driver is dropped more often
// than entries die. Each entry has the name it was made for and a spelling,
// the name where no live entry is spelled so, and a variant, x'1, otherwise,
// by which it is shown where no scope names it. An entry is found again by
// its name and its type up to alpha-equality, so that judgements derived
// under one binder are shared; never one the caller excludes, an entry the
// scope being extended holds, which would make two variables one (section
// 3.6). Of the entries made for a name at alpha-equal types, the first made
// that is not excluded is found: which entry a variable is depends on its
// name, its type and the scope it is bound in, not on the entries made since,
// so a variable bound again after a driver reset is the entry the judgements
// kept from before it use.
// A variant's spelling names its entry too: binding it again finds the entry.
// The kernel truncates entries to a checkpoint's count at its commit or
// rollback, and the transaction truncates these records with them
// (CubicalDeclarationTransaction.finish).
export class EntryNames {
  constructor(kernel) {
    this.kernel = kernel;
    // entry → { entry, name, symbol, type, keys }: symbol is the spelling's.
    this.records = new Map();
    // Each name's entries, grouped by type up to alpha-equality: name →
    // { groups: [{ type, likeness, entries }], known }, a group's entries in
    // the order they were made, and `known` each type handle met for the
    // name: its group, or how many groups it was compared with and found
    // unlike. The names whose known handles a truncation could move (touched).
    this.named = new Map();
    this.touched = new Set();
    // The live entry spelled by a symbol.
    this.holders = new Map();
    // The last variant number of each name: a spelling is never made again, so
    // a variant names one stem for ever, as its display reads it (stems).
    this.variants = new Map();
    // Each variant's stem, as the elaborator's display renaming reads it
    // (cubical-elaborator.mjs, SourceNames): the record #354 kept, where a
    // variant made again records the stem it was made from last. What the
    // renaming shows so depends on what was made before it, as on #354; the
    // display-names follow-up settles that.
    this.stems = new Map();
    // The stems binders' variants read (stemOf), fixed at a name's first
    // use: each variant's, recorded once, and the names read as their own.
    this.binderStems = new Map();
    this.ownStems = new Set();
    this.likenesses = new Map();
  }
  // The stem a binder's variant reads for a name: a variant's, recorded
  // when it was made (variantOf), and otherwise the name itself. It is fixed
  // at the name's first use, as a binder's key is (binderKey): once read as
  // its own, the name is never recorded as a variant, and a variant's stem
  // is recorded once. So a binder's variant, which reads it
  // (shownBinderName), is the same whatever is made after it, as
  // CubicalSyntax.decode keeps it.
  stemOf(name) {
    const stem = this.binderStems.get(name);
    if (stem !== undefined) return stem;
    this.ownStems.add(name);
    return name;
  }
  // A variant `name` made from `stem`: in the elaborator's record, as made,
  // and in the binders', unless the name was used there before.
  variantOf(name, stem) {
    this.stems.set(name, stem);
    if (!this.binderStems.has(name) && !this.ownStems.has(name)) this.binderStems.set(name, stem);
  }
  // A live entry made for `name` at `type`, a type's term handle or LEVEL,
  // that `excluded` does not refuse: the first made of those at a type
  // alpha-equal to `type`; 0 when there is none.
  find(name, type, excluded = () => false) {
    for (const entry of this.group(name, type)?.entries ?? []) if (!excluded(entry)) return entry;
    return 0;
  }
  // The group of `name`'s entries at types alpha-equal to `type`, or null:
  // found by the type's handle once met, and otherwise by comparing the type
  // with one entry's of each group not compared with yet. Only types alike
  // are compared up to alpha-equality: one name bound at many types, as a
  // binder of a type that mentions each of a search's fresh variables in
  // turn, would otherwise compare each new type with every earlier one.
  group(name, type) {
    const named = this.named.get(name);
    if (!named) return null;
    const known = named.known.get(type) ?? 0;
    if (typeof known === "object") return known;
    if (type === LEVEL) return null;
    const likeness = this.likeness(type);
    const group = named.groups.slice(known).find(other => other.likeness === likeness && this.kernel.alphaEqual(other.type, type));
    named.known.set(type, group ?? named.groups.length);
    this.touched.add(name);
    return group ?? null;
  }
  // What two alpha-equal types share: the root's kind, and the entries the
  // parts alpha-equality compares as syntax mention (a universe's level, an
  // instantiation's, an instance's recorded levels, compared by normal form,
  // and a path application's annotation, not compared, left out). A bound
  // variable is an index, the same on both sides.
  likeness(type) {
    const free = handle => {
      let known = this.likenesses.get(handle);
      if (known) return known;
      const node = this.kernel.node(handle), children = node.children.slice(0, partsCompared(node.kind));
      known = new Set();
      if (node.kind === "Context") known.add(node.payload);
      for (const child of children) if (child) for (const entry of free(child)) known.add(entry);
      this.likenesses.set(handle, known);
      return known;
    };
    return `${this.kernel.node(type).kind} ${[...free(type)].sort((a, b) => a - b).join(",")}`;
  }
  // The spelling of a new entry for `name`: the name itself where no live
  // entry is spelled so, unless the entry is to be `fresh`, and otherwise the
  // next variant, `stem'n` for a term entry and `stem'level n` for a level
  // entry. A variant of an assumption's name, the name of a binder that
  // closed over it, drops the assumption mark, which only assumptions' names
  // carry (web/translator/names.mjs, assumptionMark).
  spelling(name, { level = false, fresh = false } = {}) {
    if (!fresh && !this.holders.has(this.kernel.symbol(name))) return name;
    const stem = name.replaceAll(assumptionMark, ""), key = level ? `${stem}'level` : `${stem}'`;
    for (let suffix = (this.variants.get(key) ?? 0) + 1; ; suffix++) {
      const variant = `${key}${suffix}`;
      if (this.holders.has(this.kernel.symbol(variant))) continue;
      this.variants.set(key, suffix);
      this.variantOf(variant, name);
      return variant;
    }
  }
  // An entry the kernel made, for `name`, spelled `spelling`. A fresh entry
  // is found again by its spelling only, as a binder of its name never
  // takes it.
  record(entry, name, spelling, type, fresh = false) {
    if (this.records.has(entry)) return;
    const record = { entry, name, symbol: this.kernel.symbol(spelling), type, keys: fresh ? [spelling] : [...new Set([name, spelling])] };
    this.records.set(entry, record);
    for (const key of record.keys) {
      if (!this.named.has(key)) this.named.set(key, { groups: [], known: new Map() });
      const named = this.named.get(key);
      let group = this.group(key, type);
      if (!group) named.groups.push(group = { type, likeness: type === LEVEL ? LEVEL : this.likeness(type), entries: [] });
      named.known.set(type, group);
      group.entries.push(entry);
      this.touched.add(key);
    }
    this.holders.set(record.symbol, entry);
  }
  // The symbol an entry's spelling is, and the spelling.
  symbol(entry) {
    const record = this.records.get(entry);
    if (!record) throw new Error(`The driver made no context entry ${entry}.`);
    return record.symbol;
  }
  spelled(entry) { return this.kernel.symbolName(this.symbol(entry)); }
  // The name an entry was made for.
  name(entry) {
    const record = this.records.get(entry);
    if (!record) throw new Error(`The driver made no context entry ${entry}.`);
    return record.name;
  }
  // Entries from `count` on are gone: the kernel truncated them, and moved
  // the handles made with them, which the likenesses read, so each name
  // touched since knows again only its entries' types, which are older.
  truncate(count) {
    this.likenesses.clear();
    for (const [entry, record] of this.records) {
      if (entry < count) continue;
      this.records.delete(entry);
      if (this.holders.get(record.symbol) === entry) this.holders.delete(record.symbol);
      for (const key of record.keys) this.touched.add(key);
    }
    for (const key of this.touched) {
      const named = this.named.get(key);
      named.groups = named.groups.filter(group => (group.entries = group.entries.filter(entry => entry < count)).length);
      if (!named.groups.length) { this.named.delete(key); continue; }
      named.known = new Map(named.groups.flatMap(group => group.entries.map(entry => [this.records.get(entry).type, group])));
    }
    this.touched.clear();
  }
}
