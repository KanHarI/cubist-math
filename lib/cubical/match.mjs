// `match` on a declared type (work plan L2.2a; the design's section 5 and
// the H1 specification's 3.6): one clause per constructor, elaborated against
// the clause type the kernel computes for it, ClauseType_k, from the motive
// and the clauses before it; then the eliminator applied to the value. A
// definition whose body matches on one of its parameters may call itself on
// a constructor's argument: that call is the argument's recursive result.
// Untrusted: the kernel checks every clause at its clause type.
import {T,substituteTerm,substituteDimension} from "./core.mjs";
import {interval as I} from "./lattice.mjs";

// The environment key of the declaration's own name, for recursion: a key
// no source name can spell.
export const RECURSIVE = "\u0000recursive";

// The declared type a signature was registered as, from the names in scope.
function inductiveOf(scope, binding) {
  for (const value of scope.env.values()) if (value?.tag === "Inductive" && value.binding === binding) return value;
  return null;
}
// The match that is a declaration's whole body, after its own parameters,
// when it is a match on a declared type: the only place its recursion means
// what it says. Its value after the parameters' binders, or the one exact of
// a stated type; nothing else is walked.
export function recursionSite(d, own) {
  let node = null;
  if (d.value) {
    node = d.value;
    for (let count = 0; count < own.length && node;) {
      if (node.kind === "lambda") { count++; node = node.body; }
      else if (node.kind === "binderGroup") { count += node.names.length; node = node.body; }
      else node = null;
    }
  } else if (d.body?.length === 1 && d.body[0].kind === "exact") node = d.body[0].value;
  return node?.kind === "match" && node.clauses && !node.leftBody ? node : null;
}

export function elaborateMatch(translator, n, value, instance, scope, expected) {
  const locate = (error, node = n) => scope.unit.locate(error, node);
  const inductive = inductiveOf(scope, instance.signature);
  if (!inductive) throw locate(Error(`The declared type of the matched value is not in scope.`), n.value);
  const info = translator.checker.kernel.signature(inductive.record.index);
  const names = inductive.record.constructors;
  // The motive: return T, over the value as z; or the expected type.
  let motive;
  const z = scope.fresh(n.motiveName?.text ?? "z");
  if (n.type) {
    const inner = n.motiveName ? translator.sourceBinding(n.motiveName, T.variable(z), scope.bind(z, instance)) : scope.bind(z, instance);
    motive = T.lam(z, instance, translator.term(n.type, inner, null));
  } else if (expected) motive = T.lam(z, instance, expected);
  else throw locate(Error("match needs its result's type: give return T, or use it where its type is known."));
  // One clause per constructor, named as declared, in any order.
  const byName = new Map();
  for (const clause of n.clauses) {
    const name = clause.constructor.text;
    if (!names.includes(name))
      throw locate(Error(`${inductive.source} has no constructor ${name}: its constructors are ${names.join(", ")}.`), clause.constructor);
    if (byName.has(name)) throw locate(Error(`${name} has two clauses.`), clause.constructor);
    byName.set(name, clause);
  }
  const missing = names.filter(name => !byName.has(name));
  if (missing.length) throw locate(Error(missing.includes("squash") && info.constructors.at(-1).generated
    ? `Give the squash clause, squash(x, y, …) i … => …: generated squash clauses come with automatic clauses (L2.2b).`
    : `match on ${inductive.source} needs a clause for ${missing.join(", ")}.`));
  // Recursion: a match on one of the declaration's own parameters.
  const recursive = scope.env.get(RECURSIVE);
  let recursion = null;
  if (recursive?.site === n && n.value.kind === "name") {
    // The value must be the parameter itself, as its own binder bound it: a
    // variable of another binder with the same name is not.
    const target = scope.env.get(n.value.name);
    const index = [...recursive.bindings].find(([, binding]) => binding === target)?.[0];
    if (index !== undefined)
      recursion = { ...recursive, index, fixed: recursive.params.map((_, i) => recursive.bindings.get(i)) };
  }
  const clauses = [];
  names.forEach((name, k) => {
    const shape = info.constructors[k];
    const constructor = k < inductive.constructors.length ? inductive.constructors[k]
      : { order: Array.from({ length: shape.data + shape.positions }, (_, i) => i), arity: shape.data + shape.positions, dims: shape.dimensions };
    clauses.push(clause(translator, scope, byName.get(name), name, k, instance, constructor, shape,
      scope.clauseType(motive, clauses), recursion));
  });
  return T.app(T.eliminator(instance.signature, motive, clauses), value);
}

// A clause λ (data, positions, recursive results). ⟨dims⟩ body, at its
// clause type: the source names its arguments in their declared order, and
// its dimensions after them.
function clause(translator, scope, source, name, index, instance, constructor, shape, clauseType, recursion) {
  const locate = (error, node = source.constructor) => scope.unit.locate(error, node);
  const args = source.args ?? [];
  if (args.length !== constructor.arity)
    throw locate(Error(`${name} takes ${constructor.arity} argument${constructor.arity === 1 ? "" : "s"} here: ${name}(…) with ${constructor.arity} names.`));
  if (source.names.length !== constructor.dims)
    throw locate(Error(constructor.dims ? `${name} is a path constructor: name its ${constructor.dims} dimension${constructor.dims === 1 ? "" : "s"} after its arguments, as in ${name}${constructor.arity ? "(…)" : ""} i => ….`
      : `${name} has no dimensions to name.`));
  let type = clauseType, inner = scope;
  const binders = [], results = new Map();
  // The declaration's own name first, so that an argument or a dimension of
  // the same name shadows it; the results are filled in as they are bound.
  if (recursion) inner = inner.alias(recursion.source, { ...recursion, results });
  const bind = (token, stem) => {
    if (type?.tag !== "Pi") throw locate(Error(`The clause type of ${name} has fewer arguments than expected.`));
    const variable = inner.fresh(stem), domain = type.domain;
    inner = token ? translator.sourceBinding(token, T.variable(variable), inner.bind(variable, domain)) : inner.bind(variable, domain);
    type = substituteTerm(type.body, type.name, T.variable(variable));
    binders.push([variable, domain]);
    return variable;
  };
  // The data and positions, in the kernel's order: data first.
  const positions = [];
  constructor.order.forEach((sourceIndex, kernelIndex) => {
    const token = args[sourceIndex], variable = bind(token, token.text);
    if (kernelIndex >= shape.data) positions.push({ variable, token });
  });
  // Each position's recursive result.
  for (const { variable, token } of positions) results.set(variable, bind(null, `${token.text}_rec`));
  // The dimensions, each a path of the result.
  const lines = [];
  for (const token of source.names) {
    if (type?.tag !== "Path") throw locate(Error(`The clause type of ${name} has fewer dimensions than expected.`), token);
    const dim = inner.fresh(token.text);
    inner = inner.bindDimension(dim).alias(token.text, { tag: "Dimension", name: dim });
    const family = substituteDimension(type.family, type.dim, I.variable(dim));
    lines.push({ dim, family });
    type = family;
  }
  // In a recursive match, the matched parameter is the constructor here: a
  // recursive call reuses this clause at another value, so the parameter's
  // first value must not be captured. A clause name of its own shadows it.
  if (recursion) {
    const parameter = recursion.params[recursion.index];
    if (![...args, ...source.names].some(token => token.text === parameter)) {
      let built = T.constructor(index, instance, name);
      for (const [variable] of binders.slice(0, constructor.order.length)) built = T.app(built, T.variable(variable));
      for (const { dim } of lines) built = T.at(built, I.variable(dim));
      inner = inner.alias(parameter, built);
    }
  }
  let body = translator.term(source.body, inner, type);
  for (const { dim, family } of lines.reverse()) body = T.line(dim, family, body);
  for (const [variable, domain] of binders.reverse()) body = T.lam(variable, domain, body);
  return body;
}

// A call of the declaration being defined, inside a clause of its match: on
// a constructor's argument, with its other arguments unchanged, it is that
// argument's recursive result.
// Why a declaration cannot use its own name here.
export const selfReference = name => `${name} is being defined: it can call itself only on an argument of a constructor that `
  + `its match takes apart, as ${name}(m) in succ(m) => …, when that match on one of its parameters is its whole body.`;
export function resolveRecursive(translator, node, value, args, scope) {
  const locate = (error, at = node) => scope.unit.locate(error, at);
  const example = `as ${value.source}(m) in succ(m) => …`;
  if (!value.results) throw locate(Error(selfReference(value.source)));
  if (!args || args.length !== value.params.length)
    throw locate(Error(`${value.source} takes ${value.params.length} argument${value.params.length === 1 ? "" : "s"}.`));
  args.forEach((arg, index) => {
    if (index === value.index) return;
    if (arg.kind !== "name" || scope.env.get(arg.name) !== value.fixed[index])
      throw locate(Error(`A recursive call of ${value.source} passes its other arguments unchanged: here ${value.params[index]}.`), arg);
  });
  const target = args[value.index];
  const head = target.kind === "call" ? target.fn : target, applied = target.kind === "call" ? target.args : [];
  const bound = head.kind === "name" ? scope.env.get(head.name) : null;
  const result = bound?.tag === "Var" ? value.results.get(bound.name) : undefined;
  if (!result)
    throw locate(Error(`The recursive call of ${value.source} is not on an argument of the matched constructor: only structural recursion, ${example}.`), target);
  let term = T.variable(result);
  for (const arg of applied) {
    const pi = scope.nf(scope.infer(term).type);
    if (pi.tag !== "Pi") throw locate(Error(`${head.name} takes fewer arguments.`), arg);
    term = T.app(term, translator.term(arg, scope, pi.domain));
  }
  translator.reference(scope, node, term);
  return term;
}
