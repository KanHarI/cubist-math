// `match` on a declared type (work plan L2.2a; the design's section 5 and
// the H1 specification's 3.6): one clause per constructor, elaborated against
// the clause type the kernel computes for it, ClauseType_k, from the motive
// and the clauses before it; then the eliminator applied to the value. A
// definition whose body matches on one of its parameters may call itself on
// a constructor's argument: that call is the argument's recursive result.
// When a call changes another parameter, the motive quantifies over the
// definition's other parameters, but those the matched one's type depends
// on, so a call may pass values of its own for them. The expression's motive
// is its `return` type or its expected type; the closing proof statement's
// comes from its goal, through motive abstraction (motives.mjs), and each of
// its clauses is a proof block.
// Untrusted: the kernel checks every clause at its clause type.
import {T,substituteTerm,substituteDimension,freeNames} from "./core.mjs";
import {interval as I} from "./lattice.mjs";
import {abstractMotive} from "./motives.mjs";
import {Goal} from "./proof-goals.mjs";
import {SearchFuel} from "./fuel.mjs";
import {HLevelSearch,HLevelUnproved,pathEvidence} from "./hlevel.mjs";

// The keyword a match or an induction was written with, for messages.
const keyword = n => n.kind === "induction" || n.induction === true ? "induction" : "match";

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
// which one, and the others. A motive may quantify over each other parameter
// that is a variable (generalizable), so that a recursive call passes a value
// of its own for it, but not over one the matched parameter's type depends
// on, directly or through the types of others: the eliminator's instance
// fixes those. A recursive call passes those, and universe parameters,
// unchanged. A parameter whose type mentions the matched one (dependent)
// takes another value at every call. Each elaboration's `state` records
// whether a call needed the motive over the others (varied) and whether one
// was made (called), for recursively.
function recursionOf(scope, n) {
  const recursive = scope.env.get(RECURSIVE);
  if (recursive?.site !== n || n.value.kind !== "name") return null;
  // The value must be the parameter itself, as its own binder bound it: a
  // variable of another binder with the same name is not.
  const target = scope.env.get(n.value.name);
  const index = [...recursive.bindings].find(([, binding]) => binding === target)?.[0];
  if (index === undefined) return null;
  const fixed = recursive.params.map((_, i) => recursive.bindings.get(i)), matched = fixed[index].name;
  const needed = new Set(), pending = [matched];
  while (pending.length)
    for (const name of freeNames(scope.context.get(pending.pop()) ?? T.unit))
      if (!needed.has(name)) { needed.add(name); pending.push(name); }
  const generalizable = fixed.map((binding, i) => i !== index && binding?.tag === "Var" && !needed.has(binding.name));
  const dependent = fixed.map((binding, i) => generalizable[i] && freeNames(scope.context.get(binding.name) ?? T.unit).has(matched));
  return { ...recursive, index, fixed, matched, generalizable, dependent };
}

// A recursive match is elaborated first as it is written, with the
// declaration's other parameters fixed. A recursive call that changes one of
// them, or passes one whose type mentions the matched parameter, marks that
// attempt varied, and the match is elaborated again with a motive over every
// generalizable parameter. That second elaboration also stands when the first
// fails and it does not: a dependent parameter used at its refined type, before
// a call or with none, fails as written. The decision is the
// one name resolution makes, so no spelling of a call or of a binder changes
// it, and a match that passes its parameters unchanged, or never calls
// itself, is the match as written.
function recursively(translator, scope, recursion, elaborate) {
  if (!recursion?.generalizable.some(Boolean))
    return elaborate(scope, recursion && { ...recursion, state: { varied: false, called: false } }, []);
  const first = attempt(translator, scope, recursion, [], elaborate);
  if (!first.state.varied && !first.failure) return first.keep();
  const second = attempt(translator, scope, recursion,
    recursion.fixed.filter((_, i) => recursion.generalizable[i]).map(binding => binding.name), elaborate);
  return (first.state.varied || first.failure && !second.failure ? second : first).keep();
}

// One elaboration of a recursive match, apart: its fuel starts where the
// declaration's stands, with its limits, and its search and work records are
// its own, as are what it records for the inspector and the proof view. Only
// the attempt kept passes them on, so an abandoned one spends nothing of the
// declaration's; keep() returns its term or throws its error.
function attempt(translator, scope, recursion, generalizing, elaborate) {
  const unit = scope.unit, state = { varied: false, called: false };
  const references = [], steps = [], sink = unit.references, onStep = translator.onStep;
  const fuel = unit.fuel && new SearchFuel(unit.fuel.search, unit.fuel.limits, { declaration: unit.fuel.declaration });
  if (fuel) fuel.used = { ...unit.fuel.used };
  const searches = { searches: unit.searches.searches, most: { ...unit.searches.most } }, work = { ...unit.work };
  const apart = scope.withUnit(unit.with({ fuel, searches, work, references: sink && ((...record) => references.push(record)) }));
  let result, failure;
  translator.onStep = onStep && (record => steps.push(record));
  try { result = elaborate(apart, { ...recursion, state }, generalizing); } catch (error) { failure = error; }
  finally { translator.onStep = onStep; }
  return { state, failure, keep() {
    if (fuel) for (const [kind, used] of Object.entries(fuel.used))
      if (used > unit.fuel.used[kind]) unit.fuel.spend(kind, used - unit.fuel.used[kind]);
    Object.assign(unit.work, work);
    unit.searches.searches = searches.searches;
    Object.assign(unit.searches.most, searches.most);
    for (const record of references) sink(...record);
    for (const record of steps) onStep(record);
    if (failure) throw failure;
    return result;
  } };
}

// The motive's generalized parameters, by their places in the declaration.
const generalizedParameters = (recursion, motive) => {
  const names = new Set(motive.generalized.map(hypothesis => hypothesis.name));
  return recursion.fixed.map(binding => binding?.tag === "Var" && names.has(binding.name));
};

// A source name bound again to `term`, as the binding it replaces was: an
// alias of its own, recorded as that local source, so that a tactic that
// needs a local hypothesis, and a nested match, see it as one.
function rebind(translator, previous, term) {
  const alias = { ...term }, source = translator.localSources.get(previous);
  if (source) translator.localSources.set(alias, source);
  return alias;
}

// The declared type of a value, as the pattern compiler (patterns.mjs) reads
// it: its source name, its instance and its constructors but the generated
// one, or null for a value of another type.
export function matchedType(translator, scope, value) {
  const instance = scope.nf(scope.infer(value).type);
  if (instance.tag !== "Sort") return null;
  const inductive = inductiveOf(translator, scope, instance.signature);
  if (!inductive) return null;
  const info = translator.checker.kernel.signature(inductive.record.index);
  return { source: inductive.source, instance, constructors: inductive.record.constructors
    .map((name, k) => ({ name, ...inductive.constructors[k] }))
    .filter((_, k) => k < inductive.constructors.length && !info.constructors[k]?.generated) };
}

// The declared type of the matched value, and its signature.
function declaredType(translator, scope, n, instance, locate) {
  const inductive = inductiveOf(translator, scope, instance.signature);
  if (!inductive) throw locate(Error(`The declared type of the matched value is not in scope.`), n.value);
  return { inductive, info: translator.checker.kernel.signature(inductive.record.index) };
}

// The source's clause for each constructor of the declared type, one each, in
// any order. A user constructor is named as declared; the generated one is
// T.squash, or squash when no user constructor has that name.
function constructorClauses(n, { inductive, info }, locate) {
  const names = inductive.record.constructors;
  const generated = info.constructors.at(-1)?.generated ? info.constructors.length - 1 : -1;
  const keys = names.map((name, k) => k === generated ? `${inductive.source}.squash` : name);
  const indexOf = head => {
    const exact = keys.indexOf(head);
    if (exact >= 0) return exact;
    return head === "squash" && generated >= 0 && !names.slice(0, generated).includes("squash") ? generated : -1;
  };
  const byIndex = new Map();
  for (const clause of [...n.clauses, ...(n.obligations ?? [])]) {
    const head = clause.constructor.text, k = indexOf(head);
    if (k < 0)
      throw locate(Error(`${inductive.source} has no constructor ${head}: its constructors are ${keys.join(", ")}.`), clause.constructor);
    if (byIndex.has(k)) throw locate(Error(`${keys[k]} has two clauses.`), clause.constructor);
    if (clause.obligation && !info.constructors[k].dimensions)
      throw locate(Error(`${keys[k]} is a point constructor: give its computational clause in ${keyword(n)}, before obligations.`), clause.constructor);
    byIndex.set(k, clause);
  }
  const missing = keys.filter((_, k) => !byIndex.has(k) && k !== generated
    && !(n.obligationProof && info.constructors[k].dimensions));
  if (missing.length) throw locate(Error(`${keyword(n)} on ${inductive.source} needs a clause for ${missing.join(", ")}. Give path clauses in obligations { … }, or obligations by { … }.`));
  const paths = keys.filter((_, k) => !byIndex.has(k) && k !== generated && info.constructors[k].dimensions);
  if (["term", "block"].includes(n.obligationProof?.kind) && paths.length !== 1)
    throw locate(Error(`obligations by a term or proof block needs exactly one missing declared path clause; found ${paths.length}. Use named obligations { … } for separate clauses.`), n.obligationsToken);
  // Each clause with the constructor's shape, in the kernel's order.
  return keys.map((name, k) => {
    const shape = info.constructors[k];
    const constructor = k < inductive.constructors.length ? inductive.constructors[k]
      : { order: Array.from({ length: shape.data + shape.positions }, (_, i) => i), arity: shape.data + shape.positions, dims: shape.dimensions };
    return { source: byIndex.get(k), name, index: k, constructor, shape,
      // A trailing proof supplies declared path clauses. The generated
      // squash remains automatic; hlevel hints can help generate it too.
      obligationProof: k !== generated || n.obligationProof?.body?.[0]?.kind === "hlevel" ? n.obligationProof : null,
      node: n.obligationsToken ?? n };
  });
}

export function elaborateMatch(translator, n, value, instance, scope, expected) {
  const locate = (error, node = n) => scope.unit.locate(error, node);
  const declared = declaredType(translator, scope, n, instance, locate);
  // Recursion: a match on one of the declaration's own parameters, as its
  // whole body (recursionSite).
  const recursion = recursionOf(scope, n);
  // The motive: return T, over the value as z; or the expected type. In a
  // recursive match the motive is over the matched parameter itself, so that
  // a recursive result has the type of the call it stands for.
  let body;
  const z = scope.fresh(n.motiveName?.text ?? "z");
  if (n.type) {
    const inner = n.motiveName ? translator.sourceBinding(n.motiveName, T.variable(z), scope.bind(z, instance)) : scope.bind(z, instance);
    body = translator.term(n.type, inner, null);
    if (recursion && freeNames(body).has(recursion.matched))
      throw locate(Error(`The motive mentions ${n.value.name} itself: write it over the matched value, match ${n.value.name} as z return … z …, so that recursive calls have their own types.`), n.type);
  } else if (expected) body = recursion ? substituteTerm(expected, recursion.matched, T.variable(z)) : expected;
  else throw locate(Error(`${keyword(n)} needs its result's type: give return T, or use it where its type is known.`));
  // An expected type that mentions the matched variable gives the motive
  // through the motive service, as the statement's goal does: each clause
  // is at its constructor, with the hypotheses about the variable again.
  const dependent = !n.type && !recursion && value.tag === "Var" && freeNames(body).has(value.name);
  return recursively(translator, scope, recursion, (scope, recursion, generalizing) => {
    const clauses = [];
    // A recursive match over the declaration's other parameters takes its
    // motive from the motive service, as the statement does: each clause
    // binds them again under their own names, and the eliminator's result is
    // applied to them.
    if (generalizing.length || dependent) {
      const motive = abstractMotive(new Goal(substituteTerm(body, z, value), scope), [value], { generalizing });
      const generalized = recursion ? { ...recursion, generalized: generalizedParameters(recursion, motive) } : null;
      for (const each of constructorClauses(n, declared, locate))
        clauses.push(clause(translator, scope, each, instance, scope.clauseType(motive.term, clauses), generalized,
          (inner, type, built) => {
            const {transition, goal} = branch(translator, motive, value, scope, inner, built);
            return transition.rebuild(translator.term(each.source.body, goal.scope, goal.target));
          }));
      return motive.apply(T.app(T.eliminator(instance.signature, motive.term, clauses), value));
    }
    const motive = T.lam(z, instance, body);
    for (const each of constructorClauses(n, declared, locate))
      clauses.push(clause(translator, scope, each, instance, scope.clauseType(motive, clauses), recursion,
        (inner, type) => translator.term(each.source.body, inner, type)));
    return T.app(T.eliminator(instance.signature, motive, clauses), value);
  });
}

// The closing proof statement `match v { c(xs) @ i => { … } … }`: its motive is
// the goal abstracted over v (motives.mjs), and a hypothesis whose type
// mentions v is generalized, so each clause proves the goal at its
// constructor with that hypothesis again, under its own name. There, a
// variable v names the constructor, and a local definition (let, obtain)
// made from v or a generalized hypothesis is made again from their
// values. A recursive call passes a value of its own for each generalized
// parameter.
export function elaborateMatchStatement(translator, n, goal, scope) {
  const locate = (error, node = n) => scope.unit.locate(error, node);
  const value = translator.term(n.value, scope, null);
  const type = scope.infer(value).type, instance = scope.nf(type);
  if (instance.tag === "Sum" && !n.induction) return sumStatement(translator, n, goal, scope, value, type, instance);
  if (instance.tag !== "Sort")
    throw locate(Error(instance.tag === "Sum" ? `The induction statement takes apart a value of a declared type; for a sum, use match.`
      : translator.checker.kernel?.extensions?.h1 ? n.induction ? `The ${keyword(n)} statement takes apart a value of a declared type.`
      : `The ${keyword(n)} statement takes apart a value of a declared type, or of a sum.`
      : `The ${keyword(n)} statement takes apart a value of a declared type, and declared types (H1) are switched off in this kernel session.`),
      n.value);
  const declared = declaredType(translator, scope, n, instance, locate);
  const recursion = recursionOf(scope, n);
  return recursively(translator, scope, recursion, (scope, recursion, generalizing) => {
    const motive = abstractMotive(goal.at(scope), [value], { generalizing });
    const own = recursion && { ...recursion, generalized: generalizedParameters(recursion, motive) };
    const clauses = [];
    for (const each of constructorClauses(n, declared, locate))
      clauses.push(clause(translator, scope, each, instance, scope.clauseType(motive.term, clauses), own,
        (inner, type, built) => {
          const {transition, goal} = branch(translator, motive, value, scope, inner, built);
          return transition.rebuild(translator.block(each.source.body, goal));
        }));
    return motive.apply(T.app(T.eliminator(instance.signature, motive.term, clauses), value));
  });
}

// The match statement on a sum, `match v { left(a) => { … } right(b) => { … } }`:
// its motive is the goal over v, and each clause proves it at its side's
// injection, with the hypotheses about v bound again, as on a declared type.
function sumStatement(translator, n, goal, scope, value, type, sum) {
  const locate = (error, node = n) => scope.unit.locate(error, node);
  const sides = new Map();
  for (const clause of n.clauses) {
    const side = clause.constructor.text;
    if (side !== "left" && side !== "right")
      throw locate(Error(`A sum's clauses are left(a) => { … } and right(b) => { … }; found ${side}.`), clause.constructor);
    if (sides.has(side)) throw locate(Error(`${side} has two clauses.`), clause.constructor);
    const names = clause.args ?? clause.binders;
    if (names.length !== 1 || names[0].kind === "pattern" || clause.coordinates.length || clause.more)
      throw locate(Error(`A sum's clause names its side's value: ${side}(a) => { … }.`), clause.constructor);
    sides.set(side, { clause, token: names[0] });
  }
  for (const side of ["left", "right"]) if (!sides.has(side))
    throw locate(Error(`The match on a sum needs a clause for ${side}: ${side}(a) => { … }.`));
  const motive = abstractMotive(goal.at(scope), [value], { contracted: true });
  const clause = side => {
    const { clause, token } = sides.get(side);
    const name = scope.fresh(token.text), domain = sum[side];
    const inner = translator.sourceBinding(token, T.variable(name), scope.bind(name, domain));
    const injected = (side === "left" ? T.inl : T.inr)(type, T.variable(name));
    const { transition, goal: at } = branch(translator, motive, value, scope, inner, injected);
    return T.lam(name, domain, transition.rebuild(translator.block(clause.body, at)));
  };
  return motive.apply(T.sumrec(motive.term, clause("left"), clause("right"), value));
}

// A clause's goal, from a motive of the motive service: the motive at the
// constructor, with the generalized hypotheses bound again. Here the matched
// variable is the constructor and each hypothesis its new variable: a source
// name that named one names its value, and a local definition made from them
// is made again. A name the clause binds itself is left alone. A hypothesis
// bound again supersedes the one it was, which a goal no longer shows.
function branch(translator, motive, value, scope, inner, built) {
  const {transition, renamed} = motive.introduce(motive.instance([built], inner));
  const values = new Map(renamed);
  if (value.tag === "Var") values.set(value.name, built);
  let at = transition.next.scope.supersede(renamed.keys());
  // An enclosing recursive match's calls, and the names matches took apart
  // for them.
  const enclosing = scope.env.get(RECURSIVE), current = enclosing && at.env.get(enclosing.source);
  const destructed = new Map();
  for (const [name, bound] of transition.next.scope.env) {
    if (bound?.tag === "Var") {
      if (!values.has(bound.name)) continue;
      const alias = rebind(translator, bound, values.get(bound.name));
      at = at.alias(name, alias);
      if (bound.name === value.name) destructed.set(name, { alias, variable: value.name });
      continue;
    }
    if (!bound || !translator.localSources.has(bound)) continue;
    const free = freeNames(bound);
    const again = [...values].reduce((term, [variable, replacement]) =>
      free.has(variable) ? substituteTerm(term, variable, replacement) : term, bound);
    if (again === bound) continue;
    const alias = rebind(translator, bound, again);
    at = at.alias(name, alias);
    // A name an enclosing match took apart, made again here, still names the
    // variable it named, for recursion.
    const taken = current?.destructed?.get(name);
    if (taken?.alias === bound) destructed.set(name, { alias, variable: taken.variable });
  }
  // Inside a clause of an enclosing recursive match, a recursive call still
  // names the variable this match takes apart, and a position or recursive
  // result this match generalized is its new variable here.
  if (current?.tag === "Recursive" && current.results) {
    const now = variable => values.get(variable)?.tag === "Var" ? values.get(variable).name : variable;
    const results = new Map([...current.results].map(([position, entry]) => [now(position), { ...entry, result: now(entry.result) }]));
    at = at.alias(enclosing.source, { ...current, results, destructed: new Map([...(current.destructed ?? []), ...destructed]) });
  }
  return { transition, goal: transition.next.at(at) };
}

// A clause λ (data, positions, recursive results). ⟨dims⟩ body, at its
// clause type: the source names its arguments in their declared order, and
// its dimensions after them. In an induction, the names after the arguments
// are the recursive results, one for each recursive argument in order: the
// induction hypotheses. `body` elaborates the clause's body at its scope and
// type, given the constructor there.
function clause(translator, scope, { source, name, index, constructor, shape, obligationProof, node }, instance, clauseType, recursion, body) {
  if (!source) return automaticClause(translator, scope, clauseType, name, node, obligationProof, index);
  const locate = (error, node = source.constructor) => scope.unit.locate(error, node);
  const induction = node?.kind === "induction" || node?.induction === true;
  const named = source.args ?? [];
  const hypotheses = induction && shape.positions && named.length === constructor.arity + shape.positions
    ? named.slice(constructor.arity) : [];
  const args = named.slice(0, named.length - hypotheses.length);
  if (args.length !== constructor.arity) {
    const s = constructor.arity === 1 ? "" : "s";
    throw locate(Error(induction && shape.positions
      ? `${name} takes ${constructor.arity} argument${s} here, then ${shape.positions === 1 ? "its induction hypothesis" : `its ${shape.positions} induction hypotheses`} if you name them: ${name}(…) with ${constructor.arity} or ${constructor.arity + shape.positions} names.`
      : `${name} takes ${constructor.arity} argument${s} here: ${name}(…) with ${constructor.arity} names.`));
  }
  // A path clause is written as the point it covers, the constructor at its
  // coordinates: loop @ i =>.
  const spelled = `${name}${constructor.arity ? "(…)" : ""}${["i", "j", "k", "l"].slice(0, constructor.dims).map(d => ` @ ${d}`).join("")} => …`;
  if (source.binders.length)
    throw locate(Error(constructor.dims ? `Write the dimension${constructor.dims === 1 ? "" : "s"} of ${name} after @, as the point the clause covers: ${spelled}.`
      : `${name} has no dimensions to name.`), source.binders[0]);
  if (source.coordinates.length !== constructor.dims)
    throw locate(Error(constructor.dims ? `${name} is a path constructor: name its ${constructor.dims} dimension${constructor.dims === 1 ? "" : "s"} after its arguments, as in ${spelled}.`
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
  // Each position's recursive result, named by its induction hypothesis
  // when the clause gives one.
  for (const [k, { variable, token, arity, depth }] of positions.entries())
    results.set(variable, { result: bind(hypotheses[k] ?? null, hypotheses[k]?.text ?? `${token.text}_rec`), arity, depth });
  // The dimensions, each a path of the result.
  const lines = [];
  for (const token of source.coordinates) {
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
    if (![...args, ...source.coordinates].some(token => token.text === parameter))
      inner = inner.alias(parameter, rebind(translator, scope.env.get(parameter), built));
  }
  let term = body(inner, type, built);
  for (const { dim, family } of lines.reverse()) term = T.line(dim, family, term);
  for (const [variable, domain] of binders.reverse()) term = T.lam(variable, domain, term);
  return term;
}

// Missing generated squash clauses are ordinary checked terms. Bind their
// data, positions and recursive results at the kernel's clause type, then
// solve its top path from checked h-level evidence. Explicit obligations
// use the same goal and may instead supply a proof block or a whole clause.
function automaticClause(translator, scope, type, name, node, proof, index) {
  const finish = term => {
    scope.check(term, type);
    const statement = {kind:"obligation",name,start:node.start,end:node.end,keyword:node};
    translator.onStep?.({statement,next:null,goal:new Goal(type,scope),proof:term});
    translator.reference(scope,{name,start:node.start,end:node.end,role:"coherence obligation",expansionIndex:index+1,
      description:`Checked clause for ${name}${proof ? " from the explicit obligation" : " from h-level evidence"}.`},term);
    return term;
  };
  if (proof?.kind === "term") return finish(translator.term(proof.value, scope, type));
  if (proof?.kind === "block") {
    // Clause motives leave beta redexes under their telescope. Expose the
    // path's family there so rfl sees a homogeneous goal when it is constant.
    const goalType = (at, target) => {
      target = at.nf(target);
      if (target.tag === "Pi") {
        const variable = at.fresh(target.name), inner = at.bind(variable, target.domain);
        return T.pi(variable, target.domain, goalType(inner, substituteTerm(target.body, target.name, T.variable(variable))));
      }
      return target.tag === "Path" ? {...target, family:at.bindDimension(target.dim).nf(target.family)} : target;
    };
    return finish(translator.block(proof.body, new Goal(goalType(scope, type), scope)));
  }
  const build = (at, target) => {
    if (target.tag === "Pi") {
      const variable = at.fresh(target.name), inner = at.bind(variable, target.domain);
      return T.lam(variable, target.domain, build(inner, substituteTerm(target.body, target.name, T.variable(variable))));
    }
    const goal = new Goal(target, at);
    if (proof?.kind === "tactic" && proof.body[0].kind !== "hlevel") {
      const path = at.nf(target);
      return translator.block(proof.body, path.tag === "Path"
        ? goal.with({...path,family:at.bindDimension(path.dim).nf(path.family)}) : goal);
    }
    if (!at.checker.kernel.definitions.has("hlevels__HasLevel"))
      throw scope.unit.locate(Error(`Cannot generate ${name}: import hlevels and supply h-level evidence for the motive, or give the clause explicitly.`), node);
    const path = at.nf(target);
    if (path.tag !== "Path") throw Error(`The obligation ${name} is not a path clause.`);
    const locals = [];
    for (const bound of at.env.values()) if (translator.localSources.has(bound)
      && !(bound.tag === "Var" && at.context.has(bound.name))) locals.push({term:bound,type:at.infer(bound).type});
    const hints = (proof?.body[0].hints ?? []).map(node => {
      const term = translator.term(node, at, null); return {term,type:at.infer(term).type};
    });
    const search = new HLevelSearch(at, hints, term => translator.shown(term), locals, {instantiate:true});
    try { return pathEvidence(search, path, at); }
    catch (error) {
      if (!(error instanceof HLevelUnproved)) throw error;
      throw scope.unit.locate(Error(`Cannot generate ${name}: ${translator.shown(error.chain.at(-1).type)} must be ${error.chain.at(-1).level === 0 ? "a proposition" : `of h-level ${error.chain.at(-1).level}`}; ${error.reason}. Give checked h-level evidence, or an explicit obligation.`), node);
    }
  };
  const term = translator.search(scope, `Generating ${name}`, at => build(at, type));
  return finish(term);
}

// A call of the declaration being defined, inside a clause of its match: on
// a constructor's argument, it is that argument's recursive result, at the
// call's values for the generalized parameters.
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
  // A call gives the explicit parameters; each implicit one is passed
  // unchanged, as its own name.
  const explicit = value.implicit?.filter(implicit => !implicit).length ?? value.params.length;
  if (args && explicit < value.params.length && args.length === explicit) {
    const given = [...args];
    args = value.implicit.map((implicit, index) => implicit
      ? {kind: "name", name: value.params[index], start: node.start, end: node.end} : given.shift());
  }
  if (!args || args.length !== value.params.length)
    throw locate(Error(`${value.source} takes ${value.params.length} argument${value.params.length === 1 ? "" : "s"}.`));
  args.forEach((arg, index) => {
    // A generalized parameter takes the call's own value.
    if (index === value.index || value.generalized?.[index]) return;
    // A fixed one is passed as the parameter's own binding, of whatever kind
    // (a universe parameter's is none of a variable's), or as the variable a
    // match statement took apart.
    const current = arg.kind === "name" ? scope.env.get(arg.name) : undefined, taken = arg.kind === "name" ? value.destructed?.get(arg.name) : undefined;
    const unchanged = current !== undefined && (current === value.fixed[index]
      || taken && current === taken.alias && value.fixed[index]?.tag === "Var" && value.fixed[index].name === taken.variable);
    // One the motive may quantify over, changed, or whose type mentions the
    // matched parameter, sends the match to its motive over the others.
    if (value.generalizable[index] && (!unchanged || value.dependent[index])) {
      value.state.varied = true;
      throw locate(Error(`A recursive call of ${value.source} changes ${value.params[index]}: the match needs its motive over its other parameters.`), arg);
    }
    if (!unchanged)
      throw locate(Error(value.fixed[index]?.tag === "Var"
        ? `A recursive call of ${value.source} passes ${value.params[index]} unchanged: the type of the matched ${value.params[value.index]} depends on it.`
        : `A recursive call of ${value.source} passes the universe parameter ${value.params[index]} unchanged.`), arg);
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
  // A recursive result quantifies over the generalized parameters, in their
  // order: the call's values for them, each at its type there.
  if (value.generalized) args.forEach((arg, index) => {
    if (!value.generalized[index]) return;
    const pi = scope.nf(scope.infer(term).type);
    if (pi.tag !== "Pi") throw locate(Error(`Internal elaboration error: the recursive result of ${value.source} takes fewer hypotheses.`), arg);
    term = T.app(term, translator.term(arg, scope, pi.domain));
  });
  value.state.called = true;
  translator.reference(scope, node, term);
  return term;
}
