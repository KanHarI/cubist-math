// Variables and binders, read and built in one place
// (docs/roadmaps/kernel/locally-nameless-kernel.md, section 7, PR 1). The
// driver reads a term or level binder here, opens its body with an entry,
// builds a binder over an entry, names a variable's role and keys a level
// variable by it; the decoder names variables through a stack of binders;
// signature admission names its entries here; and EntryNames gives each entry
// the driver makes its name. When the kernel refers to a bound variable by
// index and to a context entry by its id (ABI 4), this module changes and its
// callers do not.
//
// On ABI 3 a binder's payload is the symbol it binds, and a variable is
// Var(symbol): bound by the nearest enclosing binder of that symbol, and
// otherwise a reference to the context entry the symbol names. The kernel
// still keeps those symbols; every name the driver reads is its own.

export const termBinders = new Set(["Pi", "Lam", "Sigma"]);
export const levelBinders = new Set(["LPi", "LLam"]);
// Term and level binders form one chain, as their variables share one space
// of names.
export const binders = new Set([...termBinders, ...levelBinders]);

// The symbol a binder binds, by which a renaming pairs two binders and a
// variable finds its binder.
export const boundSymbol = node => node.payload;
// The symbol a variable refers by: its binder's, or its entry's.
export const referenceSymbol = node => node.payload;

// A variable's role under a renaming of binders, a chain {left, right, next}
// innermost first, read on its left or right side: bound, by the depth of
// the binder that binds it, or a context reference, by its symbol. Two
// variables are the same exactly when their roles are, so a bound variable
// never meets an entry with the same number.
export function role(symbol, bindings = null, right = false) {
  let depth = 0;
  for (let binding = bindings; binding; binding = binding.next, depth++)
    if ((right ? binding.right : binding.left) === symbol) return `bound ${depth}`;
  return `context ${symbol}`;
}
// Whether two variables, read on the left and on the right of a renaming,
// have one role, as `role` gives them: without building either.
export function sameReference(left, right, bindings = null) {
  for (let binding = bindings; binding; binding = binding.next)
    if (binding.left === left || binding.right === right) return binding.left === left && binding.right === right;
  return left === right;
}
// A level variable's key in a level normal form (web/cubical-levels.mjs).
export const levelKey = (node, bindings = null, right = false) => role(referenceSymbol(node), bindings, right);

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

// A binder's body opened with an entry, to derive it there: the body, and
// the scope in which the binder's variable is that entry. A level binder's
// body is renamed to the entry's symbol where the two differ, as the kernel
// finds a level's entries by its symbols (ABI 3).
export function openBinder(graph, node, entry, scope) {
  const symbol = boundSymbol(node), own = graph.kernel.entryNames.symbol(entry);
  if (!levelBinders.has(node.kind) || own === symbol) return { body: node.children[1], scope: withEntry(scope, symbol, entry) };
  return { body: graph.rename(node.children[1], false, symbol, own), scope: withEntry(scope, own, entry) };
}
// A binder over an entry: the instruction that discharges it from a body's
// or a codomain's judgement.
export function buildBinder(graph, kind, entry, body) {
  switch (kind) {
    case "Pi": return graph.pi(entry, body);
    case "Sigma": return graph.sigma(entry, body);
    case "Lam": return graph.lambda(entry, body);
    case "LPi": return graph.levelPi(entry, body);
    case "LLam": return graph.levelLambda(entry, body);
    default: throw new TypeError(`${kind} binds no variable.`);
  }
}
// Raw syntax of a binder with its variable renamed apart from every name in
// use, a symbol the kernel allocates now, which no entry holds (ABI 3); its
// body, so renamed, is given to `rebuild` too.
export function freshBinder(graph, node, rebuild = body => body) {
  const kernel = graph.kernel, fresh = kernel.freshSymbol();
  return kernel.term(node.kind, fresh, node.children[0], rebuild(graph.rename(node.children[1], false, boundSymbol(node), fresh)));
}

// The name a decoder shows a binder's variable by, and pushes on its stack.
export const binderName = (kernel, node) => kernel.symbolName(boundSymbol(node));
// The name a decoder shows a variable by, with `names` the binders around
// it, a chain {symbol, name, next} innermost first: its binder's name where
// one binds it, and otherwise its entry's. On ABI 3 both are its symbol's
// name, so a decoding does not depend on the stack.
export function variableName(kernel, node, names = null) {
  const symbol = referenceSymbol(node);
  for (let binder = names; binder; binder = binder.next) if (binder.symbol === symbol) return binder.name;
  return kernel.symbolName(symbol);
}
export const pushName = (kernel, node, names) => ({ symbol: boundSymbol(node), name: binderName(kernel, node), next: names });

// Signature admission over entries (the H1 specification's 6.1): the sort's
// entry begins it, and each constructor's entry names the constructor in the
// later ones' types. On ABI 3 the kernel takes the entries' symbols.
export const signatureBegin = (graph, former, modifier, sort, recorded = 0) =>
  graph.issue("signatureBegin", former, modifier, graph.kernel.entryNames.symbol(sort), recorded);
export const signatureConstructor = (graph, signature, type, entry) =>
  graph.issue("signatureConstructor", signature, type, graph.kernel.entryNames.symbol(entry));

// A level entry's place in the records below, where a term entry has its
// type's handle.
export const LEVEL = "level";
// The names of the term and level entries a session makes, kept by the kernel
// wrapper beside its definitions (section 5.3): a driver is dropped more often
// than entries die. Each entry has the name it was made for and the symbol it
// holds (ABI 3), spelled as the name where no live entry held that, and as a
// variant, x'1, otherwise. An entry is found again by its name and its type
// up to alpha-equality, as cc_instr_extend's reuse by symbol found it, so
// that judgements derived under one binder are shared; never one the caller
// excludes, an entry the scope being extended holds, which would make two
// variables one (section 3.6). Of the entries made for a name at alpha-equal
// types, the first made that is not excluded is found: which entry a
// variable is depends on its name, its type and the scope it is bound in,
// not on the entries made since, so a variable bound again after a driver
// reset is the entry the judgements kept from before it use.
// A variant's spelling names its entry too: a term derived under it binds
// it by that spelling (ABI 3), and binding it again finds the entry.
// The kernel truncates entries to a checkpoint's count at its commit or
// rollback, and the transaction truncates these records with them
// (CubicalDeclarationTransaction.finish).
export class EntryNames {
  constructor(kernel) {
    this.kernel = kernel;
    // entry → { entry, name, symbol, type, keys }.
    this.records = new Map();
    // Each name's entries, grouped by type up to alpha-equality: name →
    // { groups: [{ type, entries }], known }, a group's entries in the order
    // they were made, and `known` each type handle met for the name: its
    // group, or how many groups it was compared with and found unlike. The
    // names whose known handles a truncation could move (touched).
    this.named = new Map();
    this.touched = new Set();
    // The live entry that holds a symbol.
    this.holders = new Map();
    // The last variant number of each name: a spelling is never made again, so
    // a variant names one stem for ever, as its display reads it (stems).
    this.variants = new Map();
    this.stems = new Map();
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
  // with one entry's of each group not compared with yet.
  group(name, type) {
    const named = this.named.get(name);
    if (!named) return null;
    const known = named.known.get(type) ?? 0;
    if (typeof known === "object") return known;
    if (type === LEVEL) return null;
    const group = named.groups.slice(known).find(other => other.type !== LEVEL && this.kernel.alphaEqual(other.type, type));
    named.known.set(type, group ?? named.groups.length);
    this.touched.add(name);
    return group ?? null;
  }
  // The spelling of a new entry's symbol for `name`: the name itself where
  // no live entry holds its symbol, unless the entry is to be `fresh`, and
  // otherwise the next variant, `stem'n` for a term entry and `stem'level n`
  // for a level entry.
  spelling(name, { level = false, fresh = false } = {}) {
    if (!fresh && !this.holders.has(this.kernel.symbol(name))) return name;
    const key = level ? `${name}'level` : `${name}'`;
    for (let suffix = (this.variants.get(key) ?? 0) + 1; ; suffix++) {
      const variant = `${key}${suffix}`;
      if (this.holders.has(this.kernel.symbol(variant))) continue;
      this.variants.set(key, suffix);
      this.stems.set(variant, name);
      return variant;
    }
  }
  // An entry the kernel made, for `name`, holding the symbol `spelling` names.
  // A fresh entry is found again by its spelling only, as a binder of its
  // name never takes it.
  record(entry, name, spelling, type, fresh = false) {
    if (this.records.has(entry)) return;
    const record = { entry, name, symbol: this.kernel.symbol(spelling), type, keys: fresh ? [spelling] : [...new Set([name, spelling])] };
    this.records.set(entry, record);
    for (const key of record.keys) {
      if (!this.named.has(key)) this.named.set(key, { groups: [], known: new Map() });
      const named = this.named.get(key);
      let group = this.group(key, type);
      if (!group) named.groups.push(group = { type, entries: [] });
      named.known.set(type, group);
      group.entries.push(entry);
      this.touched.add(key);
    }
    this.holders.set(record.symbol, entry);
  }
  // The symbol an entry holds, and the name its symbol spells.
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
  // the handles made with them, so each name touched since knows again only
  // its entries' types, which are older.
  truncate(count) {
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
