// Where the source syntax binds names. For each kind of node: the names it
// binds and the children they are in scope in. Source resolution and
// free-name traversals read their scopes here, so each binding form is
// described once without capturing a name or missing an occurrence (tests/scopes.test.mjs checks that every kind of node the parser
// and the translator build is described here).
import {parameterGroups,clauseTelescope} from "./telescopes.mjs";
import {sourceMetadata,syntaxValue} from "./source-syntax.mjs";

// A binder is a token, { text }, or, in a statement's pattern, a name node.
export const binderName = binder => binder?.text ?? binder?.name ?? null;
// Parsed reference tokens and retained expressions share their consumers.
export const referenceSyntax = token => token.kind ? token : {...token,kind:"name",name:token.text};
const present = binders => binders.filter(binder => binderName(binder) !== null);

// Selection is two effects: opening model labels and selecting notation.
// Compiler operand recipes request notation only; written selections request
// both. File-level recipes activate according to the consuming source item,
// before its parameters. A registration must not evaluate unused receivers.
export const selectionEffects=Object.freeze({
  all:Object.freeze({labels:true,notation:true}),
  notation:Object.freeze({labels:false,notation:true}),
  none:Object.freeze({labels:false,notation:false}),
});
const selectionConsumers=new Map([
  ...["def","inductive","theory","initial","free","evaluate","print","notation","use"].map(kind=>[kind,selectionEffects.all]),
  ...["simp_rule","simp_set","hlevel_rule"].map(kind=>[kind,selectionEffects.none]),
]);
export function fileSelectionEffects(kind) {
  const effects=selectionConsumers.get(kind);
  if(!effects)throw new TypeError(`A source consumer needs an explicit selection policy: ${kind}`);
  return effects;
}

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
  const add=(binders,role)=>groups.push({binders:present(binders),role,keys:["body","obligation"]});
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
    binders: present(parameters.map(p => p.name)), keys, paramsAfter: after,
    role: bound ? "universe" : "parameter"}));
};

// The scopes a node opens: the binders in the children under `keys`.
const SCOPES = {
  lambda: n => [{ binders: present([n.name]), keys: ["body"] }],
  forall: n => [{ binders: present([n.name]), keys: ["body"] }],
  exists: n => [{ binders: present([n.name]), keys: ["body"] }],
  binderGroup: n => [{ binders: present(n.names), keys: ["body"] }],
  select:n=>n.activation?[{binders:[n.activation],keys:["body"],role:"activation",
    effects:n.effects??selectionEffects.all}]:[],
  // An operator's operand receives a notation context, independently of its
  // already resolved term names. Its recipe supplies this parameter at use.
  notationArgument:n=>[{binders:[n.notation],keys:["body"],role:"notation"}],
  // Named-rule parameters are lazy syntax arguments, not term telescope
  // parameters. They bind only the rule body, never their operand recipes.
  namedNotationRule:n=>[{binders:n.operands,keys:["value"],role:"parameter"}],
  pathLambda: n => [{ binders: present([n.dimension]), keys: ["body"], role: "dimension" }],
  // induction n as k return P(k) { zero => …; succ h => …; }: the index in
  // the motive and, as the predecessor, in the step; the hypothesis in the
  // step. A general induction's motive name is in its motive only, and its
  // clauses bind their own names.
  induction: n => [{ binders: present([n.index]), keys: ["type", "step"] },
    { binders: present([n.motiveName]), keys: ["type"] },
    { binders: present([n.hypothesis]), keys: ["step"] }],
  // match s as k return P(k) { left x => …; right y => …; }, or clauses.
  match: n => [{ binders: present([n.motiveName]), keys: ["type"] },
    { binders: present([n.left]), keys: ["leftBody"] },
    { binders: present([n.right]), keys: ["rightBody"] }],
  // A clause's own names, a sum's side and a path constructor's
  // coordinates, are variables; its patterns' arguments may be constructors.
  clause: n => [{ binders: present([...(n.binders ?? []), ...(n.coordinates ?? []), ...(n.hypotheses ?? [])]),
    keys: ["body", "obligation"] },
    // Undecided bare heads are candidates in identity resolution; ordinary
    // free-name traversal sees only explicit pattern arguments.
    { binders: patternArguments(n), keys: ["body", "obligation"], role: "pattern" }],
  unpack: n => [{ binders: present([n.left, n.right]), keys: ["body"] }],
  // Declarations and a theory's items: their parameters.
  def: n => parameterScopes(n, ["type", "body", "value"]),
  derived: n => parameterScopes(n, ["type", "value"]),
  law: n => parameterScopes(n, ["type"]),
  operation: n => parameterScopes(n, ["type"]),
  sort: n => parameterScopes(n, []),
  constructor: n => parameterScopes(n, ["type"]),
  inductive: n => parameterScopes(n, ["result", "constructors"]),
  // A notation's numeral or literal rule: its parameter, in its value.
  numeral: n => [{ binders: present([n.param]), keys: ["value"] }],
  literal: n => [{ binders: present([n.param]), keys: ["value"] }],
};
// Statements that bind names for the statements after them, in a block.
const STATEMENTS = {
  use:n=>n.activation?[n.activation]:[],
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
  "transport", "lift", "binary", "binaryNumber", "block", "calc", "call", "demand", "evaluate", "exact", "free", "hlevel", "hlevel_rule",
  "initial", "matchStatement", "member", "name", "namedArgument", "negation", "notation", "number", "operatorOf", "over",
  "pair", "pathApply", "pattern", "print", "projection", "prop", "bindingReference", "rfl", "rw", "set", "simp_rule", "simp_set",
  "simpaOnly", "tactic", "term", "theory", "trunc", "unary", "withUnfolding",
  // Built by the translator and the theory expansion.
  "useScope", "notationReceiver", "notationRule", "boundNotation", "operandAlternatives", "rawNumeral", "sectionScope", "scoped", "instantiated", "typed",
  // Not syntax: a theory's field records and the shapes of a homomorphism's
  // types, which carry syntax but are never walked as it.
  "evidence", "morphism", "fixed", "carrier", "arrow", "other",
]);
export const BINDING = new Set([...Object.keys(SCOPES), ...Object.keys(STATEMENTS)]);

export const scopesOf = (node,{deferred=false}={}) => {
  if (!BINDING.has(node.kind) && !UNBINDING.has(node.kind))
    throw new TypeError("Unregistered syntax kind in scope traversal: " + node.kind);
  const scopes=deferred&&node.kind==="clause"?patternScopes(node):SCOPES[node.kind]?.(node)??[];
  return deferred?scopes:scopes.filter(scope=>scope.role!=="activation");
};
export const statementBinders = (node,{deferred=false}={}) => node.kind==="use"&&!deferred?[]
  :Object.hasOwn(STATEMENTS, node.kind) ? STATEMENTS[node.kind](node) : [];
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
  || node.kind === "rawNumeral" && key === "natural"
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
    extend: (outer, binders,_node,scope) => scope.role==="activation"?outer:new Set([...outer, ...binders.map(binderName)]),
  }, bound);
}

// The shared traversal also supports identity resolution: allocate each
// binder once, replace its declaration token, and extend only its schema
// regions. Neither this walker nor its clients rediscover binding forms.
// `bind` returns a binder token; `extend` adds a group's mapped binders to
// an immutable context. A replacement returned by `enter` is not entered.
// Its third argument can descend into original children in their current
// context. This permits a resolved operation or splice around source operands
// without resolving inserted syntax again or losing the enclosing binders.
export function scopeMapped(node, {prepare=n=>n,enter = n => n, bind = n => n, reference = n => n,
  region = at => at, parameter = n => n, extend, deferred = false}, context) {
  const walk = (node, outer, replacements,prepared=false) => {
    if (!node || typeof node !== "object") return node;
    if (replacements.has(node)) return replacements.get(node);
    if (isToken(node)) return node;
    if(!prepared)node=prepare(node,outer);
    if (node.kind || Array.isArray(node)) {
      const replaced = enter(node, outer, (child,at=outer)=>walk(child,at,replacements));
      if (replaced !== node) return replaced;
    }
    if (Array.isArray(node)) {
      let inner = outer, tokens = replacements;
      return node.map(item => {
        if(item&&typeof item==="object")item=prepare(item,inner);
        const binders = item?.kind ? statementBinders(item,{deferred}) : [];
        const scope={binders,...(item?.kind==="use"&&item.activation
          ?{role:"activation",effects:item.effects??selectionEffects.all}:{})};
        if (binders.length) tokens = new Map(tokens);
        const mapped = binders.map(binder => {
          if (!tokens.has(binder)) tokens.set(binder, bind(binder, node, scope, inner));
          return tokens.get(binder);
        });
        const out = walk(item, inner, tokens,true);
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
    // A declaration can supply a region-specific outer scope (structural
    // self in its body, for example). Its ordinary telescope is then applied
    // in the usual order, so parameters still shadow that outer binding.
    const inside = (predicate,key) => regions.filter(predicate)
      .reduce((at, scope) => extend(at, scope.binders, node, scope), region(outer,node,key));
    const copy = {};
    for (const [key, value] of Object.entries(node)) {
      if (captured(node, key)) {copy[key] = value; continue;}
      const namespace=Object.hasOwn(referenceFields,node.kind)?referenceFields[node.kind][key]:null;
      if(namespace) {
        const use=token=>token?.kind?walk(token,outer,tokens):token?reference(token,{namespace,node,key},outer):token;
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
          const at=inside(scope=>scope.paramsAfter<=after-parameters.length,key);
          const field=bound?"bound":"type",first=parameters[0][field];
          if(parameters.some(param=>param[field]!==first&&syntaxValue(param[field])!==syntaxValue(first)))
            throw new TypeError("Grouped parameters must share one domain.");
          const domain=walk(first,at,tokens);
          return parameters.map(param=>{
            const rest={...param};delete rest[field];
            return parameter({...walk(rest,at,tokens),[field]:domain},param,node,at);
          });
        });
        continue;
      }
      copy[key] = walk(value, inside(scope => scope.keys.includes(key),key), tokens);
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
