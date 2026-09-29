// `match` on a declared type (work plan L2.2a; the design's section 5 and
// the H1 specification's 3.6): one clause per constructor, elaborated against
// the clause type the kernel computes for it, ClauseType_k, from the motive
// and the clauses before it; then the eliminator applied to the value. A
// definition whose body matches on one of its parameters may call itself on
// a constructor's argument: that call is the argument's recursive result.
// The expression's motive is its `return` type or its expected type; the
// closing proof statement's comes from its goal, through motive abstraction
// (motives.mjs), and each of its clauses is a proof block.
// Untrusted: the kernel checks every clause at its clause type.
import {T,substituteTerm,substituteDimension,freeNames} from "./core.mjs";
import {interval as I} from "./lattice.mjs";
import {abstractMotive} from "./motives.mjs";

// The environment key of the declaration's own name, for recursion: a key
// no source name can spell.
export const RECURSIVE = "\u0000recursive";

// The declared type a signature was registered as: from the checker's
// registry, whatever names are in scope, or from the names in scope.
function inductiveOf(translator, scope, binding) {
  const registered = translator.checker.inductives?.get(binding);
  if (registered) return registered;
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
  else if (d.body?.length === 1 && d.body[0].kind === "matchStatement") return d.body[0];
  return node?.kind === "match" && node.clauses && !node.leftBody ? node : null;
}

// The recursion of a match that is its declaration's whole body
// (recursionSite) and takes apart one of the declaration's own parameters:
// which one, and the others, which a recursive call passes unchanged.
function recursionOf(scope, n) {
  const recursive = scope.env.get(RECURSIVE);
  if (recursive?.site !== n || n.value.kind !== "name") return null;
  // The value must be the parameter itself, as its own binder bound it: a
  // variable of another binder with the same name is not.
  const target = scope.env.get(n.value.name);
  const index = [...recursive.bindings].find(([, binding]) => binding === target)?.[0];
  if (index === undefined) return null;
  const fixed = recursive.params.map((_, i) => recursive.bindings.get(i)), matched = fixed[index].name;
  // An unchanged argument whose type mentions the matched parameter is not
  // unchanged at a recursive call: that needs a generalized motive.
  const dependent = fixed.map((binding, i) => i !== index && binding?.tag === "Var"
    && freeNames(scope.context.get(binding.name) ?? T.unit).has(matched));
  return { ...recursive, index, fixed, matched, dependent };
}

// The declared type of the matched value and the source's clause for each of
// its constructors, one each, in any order. A user constructor is named as
// declared; the generated one is T.squash, or squash when no user
// constructor has that name.
function constructorClauses(translator, scope, n, instance, locate) {
  const inductive = inductiveOf(translator, scope, instance.signature);
  if (!inductive) throw locate(Error(`The declared type of the matched value is not in scope.`), n.value);
  const info = translator.checker.kernel.signature(inductive.record.index);
  const names = inductive.record.constructors;
  const generated = info.constructors.at(-1)?.generated ? info.constructors.length - 1 : -1;
  const keys = names.map((name, k) => k === generated ? `${inductive.source}.squash` : name);
  const indexOf = head => {
    const exact = keys.indexOf(head);
    if (exact >= 0) return exact;
    return head === "squash" && generated >= 0 && !names.slice(0, generated).includes("squash") ? generated : -1;
  };
  const byIndex = new Map();
  for (const clause of n.clauses) {
    const head = clause.constructor.text, k = indexOf(head);
    if (k < 0)
      throw locate(Error(`${inductive.source} has no constructor ${head}: its constructors are ${keys.join(", ")}.`), clause.constructor);
    if (byIndex.has(k)) throw locate(Error(`${keys[k]} has two clauses.`), clause.constructor);
    byIndex.set(k, clause);
  }
  const missing = keys.filter((_, k) => !byIndex.has(k));
  if (missing.length) throw locate(Error(generated >= 0 && !byIndex.has(generated)
    ? `Give the squash clause, ${keys[generated]}(x, y, …) i … => …: generated squash clauses come with automatic clauses (L2.2b).`
    : `match on ${inductive.source} needs a clause for ${missing.join(", ")}.`));
  // Each clause with the constructor's shape, in the kernel's order.
  return keys.map((name, k) => {
    const shape = info.constructors[k];
    const constructor = k < inductive.constructors.length ? inductive.constructors[k]
      : { order: Array.from({ length: shape.data + shape.positions }, (_, i) => i), arity: shape.data + shape.positions, dims: shape.dimensions };
    return { source: byIndex.get(k), name, index: k, constructor, shape };
  });
}

export function elaborateMatch(translator, n, value, instance, scope, expected) {
  const locate = (error, node = n) => scope.unit.locate(error, node);
  // Recursion: a match on one of the declaration's own parameters, as its
  // whole body (recursionSite).
  const recursion = recursionOf(scope, n);
  // The motive: return T, over the value as z; or the expected type. In a
  // recursive match the motive is over the matched parameter itself, so that
  // a recursive result has the type of the call it stands for.
  let motive;
  const z = scope.fresh(n.motiveName?.text ?? "z");
  if (n.type) {
    const inner = n.motiveName ? translator.sourceBinding(n.motiveName, T.variable(z), scope.bind(z, instance)) : scope.bind(z, instance);
    const body = translator.term(n.type, inner, null);
    if (recursion && freeNames(body).has(recursion.matched))
      throw locate(Error(`The motive mentions ${n.value.name} itself: write it over the matched value, match ${n.value.name} as z return … z …, so that recursive calls have their own types.`), n.type);
    motive = T.lam(z, instance, body);
  } else if (expected) motive = T.lam(z, instance, recursion ? substituteTerm(expected, recursion.matched, T.variable(z)) : expected);
  else throw locate(Error("match needs its result's type: give return T, or use it where its type is known."));
  const clauses = [];
  for (const each of constructorClauses(translator, scope, n, instance, locate))
    clauses.push(clause(translator, scope, each, instance, scope.clauseType(motive, clauses), recursion,
      (inner, type) => translator.term(each.source.body, inner, type)));
  return T.app(T.eliminator(instance.signature, motive, clauses), value);
}

// The closing proof statement `match v { c(xs) i => { … } … }`: its motive is
// the goal abstracted over v (motives.mjs), and a hypothesis whose type
// mentions v is generalized, so each clause proves the goal at its
// constructor with that hypothesis again, under its own name. There, a
// variable v names the constructor, and a local definition (have, let,
// obtain) made from v or a generalized hypothesis is made again from their
// values. A recursive call passes a value of its own for each generalized
// parameter.
export function elaborateMatchStatement(translator, n, goal, scope) {
  const locate = (error, node = n) => scope.unit.locate(error, node);
  const value = translator.term(n.value, scope, null);
  const instance = scope.nf(scope.infer(value).type);
  if (instance.tag !== "Sort")
    throw locate(Error(instance.tag === "Sum" ? "The match statement takes apart a value of a declared type; for a sum, use cases."
      : translator.checker.kernel?.extensions?.h1 ? "The match statement takes apart a value of a declared type."
      : "The match statement takes apart a value of a declared type, a kernel extension under review: enable the experimental option h1, with --experimental=h1 in the CLI or Declared types (H1) in the workbench."),
      n.value);
  const motive = abstractMotive(goal, [value]);
  let recursion = recursionOf(scope, n);
  if (recursion) {
    const generalized = new Set(motive.generalized.map(hypothesis => hypothesis.name));
    recursion = { ...recursion, generalized: recursion.fixed.map(binding => binding?.tag === "Var" && generalized.has(binding.name)) };
  }
  const clauses = [];
  for (const each of constructorClauses(translator, scope, n, instance, locate))
    clauses.push(clause(translator, scope, each, instance, scope.clauseType(motive.term, clauses), recursion,
      (inner, type, built) => {
        // The goal at the constructor, with the generalized hypotheses bound
        // again. Here the matched variable is the constructor and each
        // hypothesis its new variable: a source name that named one names its
        // value, and a local definition made from them is made again. A name
        // the clause binds itself is left alone.
        const {transition, renamed} = motive.introduce(motive.instance([built], inner));
        const values = new Map(renamed);
        if (value.tag === "Var") values.set(value.name, built);
        let at = transition.next.scope;
        for (const [name, bound] of transition.next.scope.env) {
          if (bound?.tag === "Var") {
            if (values.has(bound.name)) at = at.alias(name, values.get(bound.name));
            continue;
          }
          if (!bound || !translator.localSources.has(bound)) continue;
          const free = freeNames(bound);
          const again = [...values].reduce((term, [variable, replacement]) =>
            free.has(variable) ? substituteTerm(term, variable, replacement) : term, bound);
          if (again !== bound) at = at.alias(name, again);
        }
        // Inside a clause of an enclosing recursive match, a recursive call
        // still names the variable this match takes apart, and a recursive
        // result this match generalized is its new variable here.
        const enclosing = scope.env.get(RECURSIVE), current = enclosing && at.env.get(enclosing.source);
        if (current?.tag === "Recursive" && current.results) {
          const results = new Map([...current.results].map(([position, entry]) =>
            [position, values.get(entry.result)?.tag === "Var" ? { ...entry, result: values.get(entry.result).name } : entry]));
          const destructed = new Map(current.destructed ?? []);
          if (value.tag === "Var") for (const [name, bound] of transition.next.scope.env)
            if (bound?.tag === "Var" && bound.name === value.name && at.env.get(name) === built)
              destructed.set(name, { alias: built, variable: value.name });
          at = at.alias(enclosing.source, { ...current, results, destructed });
        }
        return transition.rebuild(translator.block(each.source.body, transition.next.at(at)));
      }));
  return motive.apply(T.app(T.eliminator(instance.signature, motive.term, clauses), value));
}

// A clause λ (data, positions, recursive results). ⟨dims⟩ body, at its
// clause type: the source names its arguments in their declared order, and
// its dimensions after them. `body` elaborates the clause's body at its
// scope and type, given the constructor there.
function clause(translator, scope, { source, name, index, constructor, shape }, instance, clauseType, recursion, body) {
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
  // A parameter that already shadows the name keeps it.
  if (recursion && scope.env.get(recursion.source)?.tag === "Recursive")
    inner = inner.alias(recursion.source, { ...recursion, results });
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
    // A position's arity, the arguments it takes before its cube, and its
    // cube's depth: 0 for an element, 1 for a path, and so on.
    let arity = 0, depth = 0, t = type?.domain;
    for (; t?.tag === "Pi"; t = t.body) arity++;
    for (; t?.tag === "Path"; t = t.family) depth++;
    const token = args[sourceIndex], variable = bind(token, token.text);
    if (kernelIndex >= shape.data) positions.push({ variable, token, arity, depth });
  });
  // Each position's recursive result.
  for (const { variable, token, arity, depth } of positions)
    results.set(variable, { result: bind(null, `${token.text}_rec`), arity, depth });
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
  // The constructor here, at the clause's arguments and dimensions.
  let built = T.constructor(index, instance, name);
  for (const [variable] of binders.slice(0, constructor.order.length)) built = T.app(built, T.variable(variable));
  for (const { dim } of lines) built = T.at(built, I.variable(dim));
  // In a recursive match, the matched parameter is the constructor here: a
  // recursive call reuses this clause at another value, so the parameter's
  // first value must not be captured. A clause name of its own shadows it.
  if (recursion) {
    const parameter = recursion.params[recursion.index];
    if (![...args, ...source.names].some(token => token.text === parameter)) inner = inner.alias(parameter, built);
  }
  let term = body(inner, type, built);
  for (const { dim, family } of lines.reverse()) term = T.line(dim, family, term);
  for (const [variable, domain] of binders.reverse()) term = T.lam(variable, domain, term);
  return term;
}

// A call of the declaration being defined, inside a clause of its match: on
// a constructor's argument, with its other arguments unchanged, it is that
// argument's recursive result.
// Why a declaration cannot use its own name here.
export const selfReference = name => `${name} is being defined: it can call itself only on an argument of a constructor that `
  + `its match takes apart, as ${name}(m) in succ(m) => …, when that match on one of its parameters is its whole body.`;
export function resolveRecursive(translator, node, value, args, scope) {
  const locate = (error, at = node) => scope.unit.locate(error, at);
  // A name that a match statement took apart names its constructor there,
  // but a recursive call means the variable it named.
  const resolve = name => {
    const bound = scope.env.get(name), taken = value.destructed?.get(name);
    return taken && bound === taken.alias ? T.variable(taken.variable) : bound;
  };
  const example = `as ${value.source}(m) in succ(m) => …`;
  if (!value.results) throw locate(Error(selfReference(value.source)));
  if (!args || args.length !== value.params.length)
    throw locate(Error(`${value.source} takes ${value.params.length} argument${value.params.length === 1 ? "" : "s"}.`));
  args.forEach((arg, index) => {
    // A match statement's generalized parameter takes the call's own value.
    if (index === value.index || value.generalized?.[index]) return;
    const bound = arg.kind === "name" ? resolve(arg.name) : null;
    if (bound?.tag !== "Var" || bound.name !== value.fixed[index]?.name)
      throw locate(Error(`A recursive call of ${value.source} passes its other arguments unchanged: here ${value.params[index]}.`), arg);
    if (value.dependent[index])
      throw locate(Error(`A recursive call of ${value.source} passes ${value.params[index]} unchanged, but its type mentions ${value.params[value.index]}, which the call changes: that needs a generalized motive, which comes later.`), arg);
  });
  // The argument: a position, applied to its arity's arguments, and a path
  // position at each of its dimensions, f(q(y) @ i): that is an element.
  const target = args[value.index], dimensions = [];
  let element = target;
  while (element.kind === "pathApply") { dimensions.unshift(element.right); element = element.left; }
  // Its application spine, curried or not: p(0, 0) and p(0)(0) alike.
  const applied = [];
  let head = element;
  while (head.kind === "call") { applied.unshift(...head.args); head = head.fn; }
  const bound = head.kind === "name" ? resolve(head.name) : null;
  const position = bound?.tag === "Var" ? value.results.get(bound.name) : undefined;
  if (!position)
    throw locate(Error(`The recursive call of ${value.source} is not on an argument of the matched constructor: only structural recursion, ${example}.`), target);
  // The position takes exactly its own arguments: f(x(δ)) for x : Pos -> T,
  // never an argument the result would take.
  if (applied.length !== position.arity)
    throw locate(Error(`${head.name} takes ${position.arity} argument${position.arity === 1 ? "" : "s"} here, as an argument of the matched constructor.`), target);
  // A path of the matched type is not one of its elements: the call takes it
  // at its dimensions, and its result is the recursive path there.
  if (dimensions.length !== position.depth)
    throw locate(Error(position.depth
      ? `${head.name} is a ${position.depth}-dimensional path of the matched type, not an element: call ${value.source} on it at its dimensions, as ${value.source}(${head.name}${" @ i".repeat(position.depth)}).`
      : `${head.name} is an element of the matched type, not a path: call ${value.source}(${head.name}) without @.`), target);
  let term = T.variable(position.result);
  for (const arg of applied) {
    const pi = scope.nf(scope.infer(term).type);
    if (pi.tag !== "Pi") throw locate(Error(`${head.name} takes fewer arguments.`), arg);
    term = T.app(term, translator.term(arg, scope, pi.domain));
  }
  for (const dimension of dimensions) term = T.at(term, translator.interval(dimension, scope.env));
  // A match statement's result quantifies over its generalized parameters,
  // in their order: the call's values for them, each at its type there.
  if (value.generalized) args.forEach((arg, index) => {
    if (!value.generalized[index]) return;
    const pi = scope.nf(scope.infer(term).type);
    if (pi.tag !== "Pi") throw locate(Error(`Internal elaboration error: the recursive result of ${value.source} takes fewer hypotheses.`), arg);
    term = T.app(term, translator.term(arg, scope, pi.domain));
  });
  translator.reference(scope, node, term);
  return term;
}
