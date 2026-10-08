// Where the source syntax binds names. For each kind of node: the names it
// binds and the children they are in scope in. Every traversal that collects,
// renames or substitutes free names reads its scopes here, so that a binding
// form is described once and no substitution captures a name or misses an
// occurrence (tests/scopes.test.mjs checks that every kind of node the parser
// and the translator build is described here).

// A binder is a token, { text }, or, in a statement's pattern, a name node.
export const binderName = binder => binder?.text ?? binder?.name ?? null;
const present = binders => binders.filter(binder => binderName(binder) !== null);

// A pattern's arguments, nested patterns included, and its alternatives'.
// A bare argument may name a constructor, not a variable: it is in scope
// either way, so that a name of its spelling in the clause is never read as
// an outer one, but it is never renamed.
function patternArguments(pattern) {
  const args = (pattern.args ?? []).flatMap(arg => arg?.kind === "pattern" ? [...patternArguments(arg), ...present(arg.binders ?? []), ...present(arg.coordinates ?? [])] : [arg]);
  return present([...args, ...(pattern.more ?? []).flatMap(more => [...patternArguments(more), ...present(more.binders ?? []), ...present(more.coordinates ?? [])])]);
}
// A declaration's parameters, each in scope in the declaration's types,
// values and bodies.
const parameters = node => present((node.params ?? []).map(p => p.name));

// The scopes a node opens, each { binders, keys, renamable }: the binders, in
// scope in the children under `keys`; `renamable` when a substitution may
// rename them apart.
const SCOPES = {
  lambda: n => [{ binders: present([n.name]), keys: ["body"], renamable: true }],
  forall: n => [{ binders: present([n.name]), keys: ["body"], renamable: true }],
  exists: n => [{ binders: present([n.name]), keys: ["body"], renamable: true }],
  binderGroup: n => [{ binders: present(n.names), keys: ["body"], renamable: true }],
  pathLambda: n => [{ binders: present([n.dimension]), keys: ["body"], renamable: true }],
  // induction n as k return P(k) { zero => …; succ h => …; }: the index in
  // the motive and, as the predecessor, in the step; the hypothesis in the
  // step. A general induction's motive name is in its motive only, and its
  // clauses bind their own names.
  induction: n => [{ binders: present([n.index]), keys: ["type", "step"], renamable: true },
    { binders: present([n.motiveName]), keys: ["type"], renamable: true },
    { binders: present([n.hypothesis]), keys: ["step"], renamable: true }],
  // match s as k return P(k) { left x => …; right y => …; }, or clauses.
  match: n => [{ binders: present([n.motiveName]), keys: ["type"], renamable: true },
    { binders: present([n.left]), keys: ["leftBody"], renamable: true },
    { binders: present([n.right]), keys: ["rightBody"], renamable: true }],
  // A clause's own names, a sum's side and a path constructor's
  // coordinates, are variables; its patterns' arguments may be constructors.
  clause: n => [{ binders: present([...(n.binders ?? []), ...(n.coordinates ?? [])]), keys: ["body", "obligation"], renamable: true },
    { binders: patternArguments(n), keys: ["body", "obligation"], renamable: false }],
  unpack: n => [{ binders: present([n.left, n.right]), keys: ["body"], renamable: true }],
  // Declarations and a theory's items: their parameters.
  def: n => [{ binders: parameters(n), keys: ["type", "body", "value", "params"], renamable: false }],
  derived: n => [{ binders: parameters(n), keys: ["type", "value", "params"], renamable: false }],
  law: n => [{ binders: parameters(n), keys: ["type", "params"], renamable: false }],
  operation: n => [{ binders: parameters(n), keys: ["type", "params"], renamable: false }],
  sort: n => [{ binders: parameters(n), keys: ["params"], renamable: false }],
  constructor: n => [{ binders: parameters(n), keys: ["type", "params"], renamable: false }],
  inductive: n => [{ binders: parameters(n), keys: ["result", "constructors", "params"], renamable: false }],
  // A notation's numeral or literal rule: its parameter, in its value.
  numeral: n => [{ binders: present([n.param]), keys: ["value"], renamable: false }],
  literal: n => [{ binders: present([n.param]), keys: ["value"], renamable: false }],
};
// Statements that bind names for the statements after them, in a block.
const STATEMENTS = {
  let: n => targetNames(n.target),
  obtain: n => targetNames(n.target),
  intro: n => present([n.name]),
  ext: n => present([n.variable]),
  simpOnly: n => present([n.as]),
};
const targetNames = target => !target ? [] : target.kind === "name" ? [target]
  : target.kind === "pair" ? [...targetNames(target.left), ...targetNames(target.right)] : [];
// Every other kind binds nothing.
export const UNBINDING = new Set([
  "along", "binary", "binaryNumber", "block", "calc", "call", "evaluate", "exact", "free", "hlevel", "hlevel_rule",
  "initial", "matchStatement", "member", "name", "namedArgument", "negation", "notation", "number", "operatorOf", "over",
  "pair", "pathApply", "pattern", "print", "projection", "prop", "rfl", "rw", "select", "set", "simp_rule", "simp_set",
  "simpaOnly", "tactic", "term", "theory", "trunc", "unary", "use", "withUnfolding",
  // Built by the translator and the theory expansion.
  "useScope", "notationScope", "sectionScope", "scoped", "instantiated", "typed",
  // Not syntax: a theory's field records and the shapes of a homomorphism's
  // types, which carry syntax but are never walked as it.
  "evidence", "morphism", "fixed", "carrier", "arrow", "other",
]);
export const BINDING = new Set([...Object.keys(SCOPES), ...Object.keys(STATEMENTS)]);

export const scopesOf = node => SCOPES[node.kind]?.(node) ?? [];
export const statementBinders = node => STATEMENTS[node.kind]?.(node) ?? [];
const root = name => name.split(".")[0];
const isToken = value => typeof value?.text === "string" && !value.kind;
// Captured elaboration values are not source syntax: neither core binders
// nor a notation rule's closed aliases participate in syntax substitution.
const captured = (node, key) => node.kind === "instantiated" && key === "value"
  || node.kind === "notationScope" && key === "aliases";

// A copy of a syntax tree with `rewrite(node, bound)` applied to each node,
// outermost first; `bound` holds the names bound there. A node `rewrite`
// returns in place of another is not entered.
export function rewritten(node, rewrite, bound = new Set()) {
  if (Array.isArray(node)) {
    // In a block, a statement binds names for the statements after it.
    let inner = bound;
    return node.map(item => {
      const out = rewritten(item, rewrite, inner);
      const names = item?.kind ? statementBinders(item).map(binderName) : [];
      if (names.length) inner = new Set([...inner, ...names]);
      return out;
    });
  }
  if (!node || typeof node !== "object" || isToken(node)) return node;
  if (node.kind) {
    const replaced = rewrite(node, bound);
    if (replaced !== node) return replaced;
  }
  const scopes = node.kind ? scopesOf(node) : [];
  const copy = {};
  for (const [key, value] of Object.entries(node)) {
    if (captured(node, key)) { copy[key] = value; continue; }
    // A statement's target is where it binds, not a use.
    if (key === "target" && STATEMENTS[node.kind]) { copy[key] = value; continue; }
    const names = scopes.filter(scope => scope.keys.includes(key)).flatMap(scope => scope.binders.map(binderName));
    copy[key] = rewritten(value, rewrite, names.length ? new Set([...bound, ...names]) : bound);
  }
  return copy;
}

// The names a syntax tree mentions free; a qualified name, m.f, by its root.
export function freeNames(node, bound = new Set()) {
  const free = new Set();
  rewritten(node, (n, inner) => {
    if (n.kind === "name" && !inner.has(root(n.name))) free.add(root(n.name));
    return n;
  }, bound);
  return free;
}

// A copy with each free name that `rename` maps, by its root, renamed:
// rename(root) gives the new root or null.
export const renamedFree = (node, rename) => rewritten(node, (n, bound) => {
  if (n.kind !== "name" || bound.has(root(n.name))) return n;
  const renamed = rename(root(n.name));
  return renamed ? { ...n, name: renamed + n.name.slice(root(n.name).length) } : n;
});

// `node` with each free name that `args` maps replaced by its syntax (a
// qualified name's root too, as R.M becomes a member of R's argument), and a
// binder that would capture a free name of an argument substituted under it
// renamed first, apart from every name either mentions. A binder that may not
// be renamed (a pattern's or a parameter's) and would capture one is refused
// with the error `refuse(name)` gives.
export function substituted(node, args, refuse) {
  const freeIn = new Map([...args].map(([name, arg]) => [name, freeNames(arg)]));
  const free = new Set([...freeIn.values()].flatMap(names => [...names]));
  const taken = new Set([...free, ...allNames(node)]);
  const fresh = stem => freshName(stem, taken);
  const go = (tree, bound) => rewritten(tree, (n, inner) => {
    if (n.kind === "name" && !inner.has(root(n.name))) {
      if (args.has(n.name)) return args.get(n.name);
      const [head, ...fields] = n.name.split(".");
      if (args.has(head)) {
        const dots = n.qualifiedDots ?? (n.qualifiedDot ? [n.qualifiedDot] : []);
        let value = args.get(head), end = n.start + head.length;
        for (const [index, text] of fields.entries()) {
          const start = dots[index]?.end ?? end + 1;
          end = start + text.length;
          value = { kind: "member", value, field: { text, start, end }, start: n.start, end };
        }
        return value;
      }
    }
    // A binder captures when an argument substituted under it names it.
    const captures = (scope, binder) => [...args.keys()].some(name => freeIn.get(name).has(binderName(binder)) && occursFree(n, scope, name));
    const scopes = scopesOf(n), clashing = new Set(scopes.filter(scope => scope.binders.some(binder => captures(scope, binder))));
    if (!clashing.size) return n;
    for (const scope of clashing) if (!scope.renamable)
      throw refuse(binderName(scope.binders.find(binder => captures(scope, binder))));
    return go(apart(n, scopes, clashing, free, fresh), inner);
  }, bound);
  return go(node, new Set());
}
// Whether `name` occurs free in a scope's children, where a substitution
// would put an argument under its binders.
const occursFree = (node, scope, name) => scope.keys.some(key => freeNames(node[key] ?? null).has(name));
// The node with each scope's binders that `free` holds renamed fresh, in the
// binder and in the children that scope covers only: a match's left side's
// binder is renamed in its left branch, never in the right. A node's scopes
// are listed outermost first, and in a child that a later scope also covers,
// a name that scope binds again is that scope's, not an earlier one's: in
// induction n as z … { succ z => z; }, the step's z is the hypothesis.
function apart(node, scopes, clashing, free, fresh) {
  const tokens = new Map(), copy = { ...node };
  for (const [index, scope] of scopes.entries()) {
    if (!clashing.has(scope)) continue;
    const renaming = new Map();
    for (const binder of scope.binders) if (free.has(binderName(binder))) {
      const other = renaming.get(binderName(binder)) ?? fresh(binderName(binder));
      renaming.set(binderName(binder), other);
      tokens.set(binder, { ...binder, text: other });
    }
    if (renaming.size) for (const key of scope.keys) if (key in copy) {
      const inner = scopes.slice(index + 1).filter(later => later.keys.includes(key))
        .flatMap(later => later.binders.map(binderName));
      copy[key] = renamedFree(copy[key], name => inner.includes(name) ? null : renaming.get(name) ?? null);
    }
  }
  const swap = value => tokens.get(value) ?? (Array.isArray(value) ? value.map(swap) : value);
  for (const [key, value] of Object.entries(copy)) copy[key] = swap(value);
  return copy;
}
// A name for generated syntax that `taken` does not hold, added to it: the
// stem, or the stem numbered from 1. A stem of U's, or one ending in a
// digit, takes a separator, U_1: U1 and UU0 spell universe constants, and a1
// numbered 1 would be a11, which a numbered 11 is too.
export function freshName(stem, taken) {
  const numbered = k => /^U+$/.test(stem) || /[0-9]$/.test(stem) ? `${stem}_${k}` : `${stem}${k}`;
  let name = stem;
  for (let k = 1; taken.has(name); k++) name = numbered(k);
  taken.add(name);
  return name;
}

// The names a tree binds where a substitution may not rename them apart: a
// pattern's arguments and a declaration's parameters.
export function fixedBinders(node) {
  const names = new Set();
  rewritten(node, n => {
    for (const scope of scopesOf(n)) if (!scope.renamable) for (const binder of scope.binders) names.add(binderName(binder));
    return n;
  });
  return names;
}

// Every name a tree uses, bound or free.
export function allNames(node, names = new Set()) {
  if (Array.isArray(node)) { for (const item of node) allNames(item, names); return names; }
  if (!node || typeof node !== "object") return names;
  if (node.kind === "name") names.add(root(node.name));
  if (typeof node.text === "string") names.add(node.text);
  for (const [key, value] of Object.entries(node))
    if (!captured(node, key) && value && typeof value === "object") allNames(value, names);
  return names;
}

// Inherited or generated syntax belongs to its expansion site, including
// operator and punctuation spans used by diagnostics and source links. With
// `at.synthetic`, each node is marked as written by no one there, so that it
// links nowhere in the source.
export function relocated(node, at) {
  if (Array.isArray(node)) return node.map(item => relocated(item, at));
  if (!node || typeof node !== "object") return node;
  return Object.fromEntries([...Object.entries(node).map(([key, value]) => [key,
    captured(node, key) ? value
      : typeof value === "number" && (key === "start" || key.endsWith("Start")) ? at.start
      : typeof value === "number" && (key === "end" || key.endsWith("End")) ? at.end : relocated(value, at)]),
    ...(at.synthetic ? [["synthetic", true]] : [])]);
}

// A copy of written syntax that a later generated declaration reads again:
// it keeps its positions, for diagnostics, but is synthetic, so that it links
// nowhere; the declaration that reads it first links it.
export function unlinked(node) {
  if (Array.isArray(node)) return node.map(unlinked);
  if (!node || typeof node !== "object") return node;
  return Object.fromEntries([...Object.entries(node).map(([key, value]) => [key, captured(node, key) ? value : unlinked(value)]),
    ...(Number.isInteger(node.start) ? [["synthetic", true]] : [])]);
}
