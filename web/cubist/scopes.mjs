// Where the source syntax binds names. For each kind of node: the names it
// binds and the children they are in scope in. Every traversal that collects,
// renames or substitutes free names reads its scopes here, so that a binding
// form is described once and no substitution captures a name or misses an
// occurrence (tests/scopes.test.mjs checks that every kind of node the parser
// and the translator build is described here).
import {parameterGroups,clauseTelescope} from "./telescopes.mjs";
import {sourceMetadata,syntaxValue} from "./source-syntax.mjs";

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
const barePattern = pattern => !pattern.args && !pattern.binders?.length && !pattern.coordinates?.length;
function patternScopes(pattern) {
  const groups=[];
  const add=(binders,role)=>groups.push({binders:present(binders),role,keys:["body","obligation"],renamable:role!=="pattern"});
  if(barePattern(pattern)&&pattern.kind!=="pattern")add([pattern.constructor],"pattern");
  for(const {tokens,role} of clauseTelescope(pattern))for(const token of tokens) {
    if(token.kind==="pattern")groups.push(...patternScopes(token));
    else add([token],role);
  }
  for(const more of pattern.more??[])groups.push(...patternScopes(more));
  return groups;
}
// Parameters form a telescope. Each group's domain is outside that group's
// binders, and every subsequent group is inside them.
const parameterScopes = (node, keys) => {
  return parameterGroups(node.params ?? []).map(({parameters, after, bound}) => ({
    binders: present(parameters.map(p => p.name)), keys, paramsAfter: after, renamable: false,
    role: bound ? "universe" : "parameter"}));
};

// The scopes a node opens, each { binders, keys, renamable }: the binders, in
// scope in the children under `keys`; `renamable` when a substitution may
// rename them apart.
const SCOPES = {
  lambda: n => [{ binders: present([n.name]), keys: ["body"], renamable: true }],
  forall: n => [{ binders: present([n.name]), keys: ["body"], renamable: true }],
  exists: n => [{ binders: present([n.name]), keys: ["body"], renamable: true }],
  binderGroup: n => [{ binders: present(n.names), keys: ["body"], renamable: true }],
  pathLambda: n => [{ binders: present([n.dimension]), keys: ["body"], renamable: true, role: "dimension" }],
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
  clause: n => [{ binders: present([...(n.binders ?? []), ...(n.coordinates ?? []), ...(n.hypotheses ?? [])]),
    keys: ["body", "obligation"], renamable: true },
    // `binders` is the nominal substitution contract until CB3 migrates its
    // consumers. Identity resolution also retains a bare head's candidate.
    { binders: patternArguments(n), keys: ["body", "obligation"], renamable: false, role: "pattern" }],
  unpack: n => [{ binders: present([n.left, n.right]), keys: ["body"], renamable: true }],
  // Declarations and a theory's items: their parameters.
  def: n => parameterScopes(n, ["type", "body", "value"]),
  derived: n => parameterScopes(n, ["type", "value"]),
  law: n => parameterScopes(n, ["type"]),
  operation: n => parameterScopes(n, ["type"]),
  sort: n => parameterScopes(n, []),
  constructor: n => parameterScopes(n, ["type"]),
  inductive: n => parameterScopes(n, ["result", "constructors"]),
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
  "transport", "lift", "binary", "binaryNumber", "block", "calc", "call", "evaluate", "exact", "free", "hlevel", "hlevel_rule",
  "initial", "matchStatement", "member", "name", "namedArgument", "negation", "notation", "number", "operatorOf", "over",
  "pair", "pathApply", "pattern", "print", "projection", "prop", "reference", "bindingReference", "rfl", "rw", "select", "set", "simp_rule", "simp_set",
  "simpaOnly", "tactic", "term", "theory", "trunc", "unary", "use", "withUnfolding",
  // Built by the translator and the theory expansion.
  "useScope", "notationScope", "sectionScope", "scoped", "instantiated", "typed", "recursiveCall",
  // Not syntax: a theory's field records and the shapes of a homomorphism's
  // types, which carry syntax but are never walked as it.
  "evidence", "morphism", "fixed", "carrier", "arrow", "other",
]);
export const BINDING = new Set([...Object.keys(SCOPES), ...Object.keys(STATEMENTS)]);

const sequenceScope = (node, index, binders) => ({binders, renamable: false,
  // Most traversals need only the ordered boundary. Materialize the region
  // keys only for clients which ask for them, such as nominal substitution.
  after: index + 1, get keys() {return node.slice(index + 1).map((_, k) => index + 1 + k);}});
export const scopesOf = (node,{deferred=false}={}) => {
  // A sequence has scopes too: each statement binds in its later siblings,
  // never in its own initializer. Until elaboration fixes tactic/pattern
  // roles, these binders may not be renamed by syntax substitution.
  if (Array.isArray(node)) return node.flatMap((item, index) => {
    const binders = item?.kind ? statementBinders(item) : [];
    return binders.length ? [sequenceScope(node, index, binders)] : [];
  });
  if (!BINDING.has(node.kind) && !UNBINDING.has(node.kind))
    throw new TypeError("Unregistered syntax kind in scope traversal: " + node.kind);
  return deferred&&node.kind==="clause"?patternScopes(node):SCOPES[node.kind]?.(node)??[];
};
export const statementBinders = node => Object.hasOwn(STATEMENTS, node.kind) ? STATEMENTS[node.kind](node) : [];
// Binding roles follow the same schema as visibility. They describe syntax
// ownership; a pattern role remains a candidate until elaboration decides.
export function bindingRole(node, scope, binder) {
  if (scope.role) return scope.role;
  if (node.bound) return "universe";
  if (node.domain?.kind === "name" && node.domain.name === "Interval") return "dimension";
  const coordinate = pattern => (pattern.coordinates ?? []).includes(binder)
    || (pattern.args ?? []).some(arg => arg.kind === "pattern" && coordinate(arg))
    || (pattern.more ?? []).some(coordinate);
  return node.kind === "clause" && coordinate(node) ? "dimension" : "local";
}
const root = name => name.split(".")[0];
const isToken = value => typeof value?.text === "string" && !value.kind;
// Captured elaboration values are not source syntax: neither core binders
// nor a notation rule's closed aliases participate in syntax substitution.
const captured = (node, key) => sourceMetadata(key,node[key]) || node.kind === "instantiated" && key === "value"
  || node.kind === "notationScope" && key === "aliases"
  || node.kind === "scoped" && ["node", "scope"].includes(key)
  || node.kind === "bindingReference" && ["resolution", "origin", "substitutions"].includes(key);

// Plain tokens can be references too. Their namespace is explicit rather
// than guessed from spelling. Identity migration must implement these
// namespaces before opting a family into binding-syntax's allowlist.
const simplificationReferences = {witnesses:"local",without:"simp-rule-or-set",at:"local"};
export const referenceFields = Object.freeze({
  simpOnly:Object.freeze(simplificationReferences),
  simpaOnly:Object.freeze({...simplificationReferences}),
  withUnfolding:Object.freeze({hints:"lexical"}),
  simp_rule:Object.freeze({rule:"lexical"}),
  hlevel_rule:Object.freeze({rule:"lexical"}),
  simp_set:Object.freeze({rules:"lexical"}),
});

// A copy of a syntax tree with `rewrite(node, bound)` applied to each node
// and sequence, outermost first; `bound` holds the names bound there. A node `rewrite`
// returns in place of another is not entered.
export function rewritten(node, rewrite, bound = new Set()) {
  return scopeMapped(node, {
    enter: rewrite,
    extend: (outer, binders) => new Set([...outer, ...binders.map(binderName)]),
  }, bound);
}

// The shared traversal also supports identity resolution: allocate each
// binder once, replace its declaration token, and extend only its schema
// regions. Neither this walker nor its clients rediscover binding forms.
// `bind` returns a binder token; `extend` adds a group's mapped binders to
// an immutable context. A replacement returned by `enter` is not entered.
export function scopeMapped(node, {enter = n => n, bind = n => n, reference = n => n, extend, deferred = false}, context) {
  const walk = (node, outer, replacements) => {
    if (!node || typeof node !== "object") return node;
    if (replacements.has(node)) return replacements.get(node);
    if (isToken(node)) return node;
    if (node.kind || Array.isArray(node)) {
      const replaced = enter(node, outer);
      if (replaced !== node) return replaced;
    }
    if (Array.isArray(node)) {
      let inner = outer, tokens = replacements;
      return node.map((item, index) => {
        const binders = item?.kind ? statementBinders(item) : [];
        const scope = sequenceScope(node, index, binders);
        if (binders.length) tokens = new Map(tokens);
        const mapped = binders.map(binder => {
          if (!tokens.has(binder)) tokens.set(binder, bind(binder, node, scope, inner));
          return tokens.get(binder);
        });
        const out = walk(item, inner, tokens);
        if (mapped.length) inner = extend(inner, mapped, node, scope);
        return out;
      });
    }
    const scopes = node.kind ? scopesOf(node,{deferred}) : [];
    const tokens = scopes.length ? new Map(replacements) : replacements;
    const regions = scopes.map(scope => ({...scope, binders: scope.binders.map(binder => {
      if (!tokens.has(binder)) tokens.set(binder, bind(binder, node, scope, outer));
      return tokens.get(binder);
    })}));
    const inside = predicate => regions.filter(predicate).reduce((at, scope) => extend(at, scope.binders, node, scope), outer);
    const copy = {};
    for (const [key, value] of Object.entries(node)) {
      if (captured(node, key)) {copy[key] = value; continue;}
      const namespace=Object.hasOwn(referenceFields,node.kind)?referenceFields[node.kind][key]:null;
      if(namespace) {
        const use=token=>token?reference(token,{namespace,node,key},outer):token;
        copy[key]=Array.isArray(value)?value.map(use):use(value);
        continue;
      }
      // A statement target is a binder, never a reference. Identity clients
      // replace its individual tokens, including within pair targets.
      if (key === "target" && Object.hasOwn(STATEMENTS, node.kind)) {
        const target = n => tokens.get(n) ?? (n?.kind === "pair" ? {...n, left: target(n.left), right: target(n.right)} : n);
        copy[key] = target(value); continue;
      }
      if (key === "params" && Array.isArray(value)) {
        copy[key] = parameterGroups(value).flatMap(({parameters,after,bound})=>{
          const at=inside(scope=>scope.paramsAfter<=after-parameters.length);
          const field=bound?"bound":"type",first=parameters[0][field];
          if(parameters.some(param=>param[field]!==first&&syntaxValue(param[field])!==syntaxValue(first)))
            throw new TypeError("Grouped parameters must share one domain.");
          const domain=walk(first,at,tokens);
          return parameters.map(param=>{
            const rest={...param};delete rest[field];
            return {...walk(rest,at,tokens),[field]:domain};
          });
        });
        continue;
      }
      copy[key] = walk(value, inside(scope => scope.keys.includes(key)), tokens);
    }
    return copy;
  };
  return walk(node, context, new Map());
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
    const captures = (scope, binder) => [...args.keys()].some(name => freeIn.get(name).has(binderName(binder)) && occursFree(n, scope, name, inner));
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
const occursFree = (node, scope, name, outer) => {
  const scopes = scopesOf(node);
  const inRegion = (value, enclosing) => freeNames(value,
    new Set([...outer, ...enclosing.flatMap(s => s.binders.map(binderName))])).has(name);
  return scope.keys.some(key => inRegion(node[key] ?? null, scopes.filter(s => s.keys.includes(key))))
    || scope.paramsAfter !== undefined && node.params.some((param, index) => index >= scope.paramsAfter
      && inRegion(param, scopes.filter(s => s.paramsAfter <= index)));
};
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
      tokens.set(binder, { ...binder, text: other, label: binder.label ?? binderName(binder) });
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
// pattern's arguments, a declaration's parameters, and a block's statements.
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
