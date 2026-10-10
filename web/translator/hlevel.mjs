// The hlevel tactic's search (work plan L2.5b; the HoTT roadmap's D1). It
// proves that a type is contractible, a proposition, a set or of a finite
// level, and an equality in a proposition, from the checked lemmas of
// library/hlevels.cubist, local evidence and hints. The search is untrusted:
// it builds a proof term, and the kernel checks that term against the goal.
//
// A level is "contr", or a number n: 0 for a proposition, 1 for a set. An
// obligation asks for evidence that a type has a level, in a universe; it is
// discharged, in this order, by
//   1. evidence in scope or a hint stating that the type has that level or a
//      lower one, lifted by cumulativity; a proposition, or a contractible
//      type, has every level, a variable one included;
//   2. the type being itself an h-level statement, which is a proposition;
//   3. a rule whose statement's carrier matches the type: quantified
//      evidence in scope or a quantified hint, then a lemma registered by
//      hlevel_rule, its parameters read from the match and its premises
//      proved as obligations of their own;
//   4. the type's weak head: Π, Σ and path types reduce to obligations on
//      their parts, and Unit, Void and Nat have their levels by lemmas.
// Each obligation spends a premise search, and each candidate a candidate,
// of the tactic's fuel. Every structural rule makes its obligations on
// strictly smaller types; a rule's premise that repeats an obligation it is
// proving is a cycle, and the rule is passed over.
import { T, substituteTerm, substituteDimension, freeNames } from "./core.mjs";
import { freeDimensions } from "./dimension-slots.mjs";
import { interval as I } from "./lattice.mjs";
import { transportToDependentPath } from "./path-over.mjs";
import {naturalSort,numeral,numeralValue} from "./numerals.mjs";
import { stem } from "./names.mjs";
export {numeralValue} from "./numerals.mjs";

const LIBRARY = "hlevels";
const lemma = name => ({ tag: "DefRef", name: `${LIBRARY}__${name}` });
// A lemma of the library, at a universe level, applied to its arguments.
const applied = (name, universe, ...args) => args.reduce(T.app, T.levelApply(lemma(name), universe));

// A closed numeral's value, or null.
// A level's term: a numeral, or the term of a level that is none.
const levelTerm = level => typeof level === "object" ? level.term : numeral(level);

// A term with the administrative beta-redexes at its head reduced, as intro
// leaves one around its goal: (fun x => B)(v) is B with v for x, and a
// universe lambda at a level is its body at that level. Named definitions
// stay folded.
export function headBeta(term) {
  for (;;) {
    const spine = [];
    let head = term;
    for (; head?.tag === "App" || head?.tag === "LApp"; head = head.fn) spine.unshift(head);
    const [first, ...rest] = spine;
    if (!(first?.tag === "App" && head?.tag === "Lam" || first?.tag === "LApp" && head?.tag === "LLam")) return term;
    term = rest.reduce((reduced, node) => node.tag === "App" ? T.app(reduced, node.arg) : T.levelApply(reduced, node.level),
      substituteTerm(head.body, head.name, first.tag === "App" ? first.arg : first.level));
  }
}

// What a type states about h-levels, read from its folded head:
// { level, universe, type }, where level is "contr", a number, or, for
// HasLevel at a level that is no numeral, the level's term; or null.
export function statement(term) {
  const args = [];
  let head = headBeta(term);
  for (; head?.tag === "App"; head = head.fn) args.unshift(head.arg);
  if (head?.tag !== "LApp" || head.fn?.tag !== "DefRef") return null;
  const universe = head.level, [first, second] = args;
  switch (head.fn.name) {
    case `${LIBRARY}__IsContr`: return args.length === 1 ? { level: "contr", universe, type: first } : null;
    case `${LIBRARY}__IsProp`: return args.length === 1 ? { level: 0, universe, type: first } : null;
    case `${LIBRARY}__IsSet`: return args.length === 1 ? { level: 1, universe, type: first } : null;
    case `${LIBRARY}__HasLevel`:
      return args.length === 2 ? { level: numeralValue(first) ?? { term: first }, universe, type: second } : null;
    default: return null;
  }
}

const named = level => level === "contr" ? "contractible" : level === 0 ? "a proposition" : level === 1 ? "a set"
  : `of level ${level}`;

// No evidence for an obligation. `chain` lists the obligations from the goal
// down to the first one nothing discharges.
export class HLevelUnproved extends Error {
  constructor(chain, reason) {
    super(reason);
    Object.assign(this, { chain, reason });
  }
}

// A rule, read from the type of a registered lemma or of quantified
// evidence (L2.5b): universe parameters and parameters, in any order, ending
// in an h-level statement at a numeral level or contractibility. Each
// parameter is determined by the statement's carrier or universe, or is a
// premise, an h-level statement under binders of its own, which the search
// proves. `binders` keeps their order, in which the rule is applied.
// A type that is no rule gives { refusal }, which noRule states; `show`
// displays a term.
export function ruleShape(type, show = term => JSON.stringify(term)) {
  const binders = [];
  let body = headBeta(type);
  for (;;) {
    if (body?.tag === "LPi") { binders.push({ name: body.name, universe: true }); body = headBeta(body.body); }
    else if (body?.tag === "Pi") { binders.push({ name: body.name, domain: body.domain }); body = headBeta(body.body); }
    else break;
  }
  const conclusion = statement(body);
  if (!conclusion) return { refusal: `its type ends in ${show(body)}, which states no h-level` };
  if (typeof conclusion.level === "object") return { refusal: `its statement's level, ${show(conclusion.level.term)}, is no numeral` };
  const determined = new Set([...freeNames(conclusion.type), ...freeNames({ tag: "U", level: conclusion.universe })]);
  for (const binder of binders)
    if (binder.universe && !determined.has(binder.name)) return { refusal: `its universe ${stem(binder.name)} is not determined by its statement` };
  for (const param of binders) {
    if (param.universe || determined.has(param.name)) continue;
    param.premise = premiseShape(param.domain);
    if (!param.premise) return { refusal: `its parameter ${stem(param.name)} is neither read from the carrier ${show(conclusion.type)} nor an h-level premise` };
  }
  return { binders, conclusion };
}

// Why a registered lemma, or a hint, is no rule; and a lemma registered
// twice in one module.
export const noRule = (what, reason) => Error(`${what} is no h-level rule: ${reason}.`);
export const ruleTwice = name => Error(`${name} is already an h-level rule in this module.`);

// A premise: an h-level statement at a numeral level or contractibility,
// under binders, as forall x : A. IsSet(U, B(x)); or null.
function premiseShape(type) {
  const binders = [];
  let body = headBeta(type);
  for (; body?.tag === "Pi"; body = headBeta(body.body)) binders.push({ name: body.name, domain: body.domain });
  const stated = statement(body);
  return stated && typeof stated.level !== "object" ? { binders, ...stated } : null;
}

// The values that make a rule's statement the obligation's: each universe
// parameter and determined parameter, read by matching the statement's
// carrier against the type and its universe against the obligation's; or
// null. Matching is candidate construction only: the instance is compared
// with the type, and the proof built from it goes through the kernel.
function instance(shape, universe, type, scope) {
  const { conclusion } = shape;
  const variables = new Set(shape.binders.filter(binder => !binder.premise).map(binder => binder.name));
  const values = new Map();
  const match = (pattern, actual) => {
    pattern = pattern?.tag ? headBeta(pattern) : pattern;
    actual = actual?.tag ? headBeta(actual) : actual;
    if (pattern?.tag === "Var" && variables.has(pattern.name)) {
      if (values.has(pattern.name)) return JSON.stringify(values.get(pattern.name)) === JSON.stringify(actual)
        || typeof actual === "object" && !!actual?.tag && attempt(() => scope.equal(values.get(pattern.name), actual));
      values.set(pattern.name, actual); return true;
    }
    if (pattern === actual) return true;
    if (!pattern || !actual || typeof pattern !== "object" || typeof actual !== "object") return false;
    const keys = Object.keys(pattern).filter(key => key !== "sort");
    if (keys.length !== Object.keys(actual).filter(key => key !== "sort").length) return false;
    return keys.every(key => Object.hasOwn(actual, key) && match(pattern[key], actual[key]));
  };
  const fits = carrier => {
    values.clear();
    if (!match(conclusion.type, carrier)) return false;
    // The statement's universe is the obligation's, unless the carrier fixed it.
    const level = conclusion.universe;
    if (level?.tag === "Var" && variables.has(level.name) && !values.has(level.name)) values.set(level.name, universe);
    return [...variables].every(name => values.has(name));
  };
  if (!fits(type)) {
    let normal;
    try { normal = scope.nf(type); } catch(error) { failedCandidate(error);return null; }
    if (!fits(normal)) return null;
  }
  try { if (!scope.equal(substituteAll(conclusion.type, values), type)) return null; }
  catch(error) { failedCandidate(error);return null; }
  return values;
}

const substituteAll = (term, values) => [...values].reduce((t, [name, value]) => substituteTerm(t, name, value), term);

export class HLevelSearch {
  // `scope` carries the tactic's fuel; `hints` are checked terms with their
  // types, and so are `locals`, the evidence that local definitions (let,
  // obtain) name; `show` displays a term in the goal's names. `rules` are
  // the lemmas hlevel_rule registered, each with its term and shape, in
  // order of priority.
  constructor(scope, hints, show, locals = [], { instantiate = false, rules = [] } = {}) {
    Object.assign(this, { scope, hints, show, locals, instantiate, rules, active: [] });
  }

  // Evidence that `type` has `level` in `universe`, in `scope`: a term of
  // type IsContr(universe, type) or HasLevel(universe, level, type). The
  // chain of obligations names a binder's body by the binder's own name,
  // for every value of its domain; `names` maps each variable the search
  // introduced for a binder to that binder's name, for display.
  prove(level, universe, type, scope = this.scope, chain = [], binder = null, names = new Map()) {
    scope.spend("premises");
    const dependent = binder && freeNames(binder.body).has(binder.name);
    chain = [...chain, dependent ? { level, type: binder.body, binder, names } : { level, type: binder ? binder.body : type, names }];
    const found = this.evidence(level, universe, type, scope)
      ?? this.statementRule(level, universe, type, scope);
    if (found) return found;
    // Where a rule matched but its premise was not proved, and nothing
    // structural applies either, the premise's chain says why.
    const failures = [];
    const ruled = this.ruled(level, universe, type, scope, chain, names, failures);
    if (ruled) return ruled;
    try { return this.structure(level, universe, type, scope, chain, names); }
    catch (error) {
      if (error instanceof HLevelUnproved && failures.length) throw failures[0];
      throw error;
    }
  }

  // Quantified evidence in scope and quantified hints, then registered
  // rules, whose statements match the type and whose premises the search
  // proves. A rule that fails, or whose premise repeats an obligation it is
  // proving, gives way to the next.
  ruled(level, universe, type, scope, chain, names, failures = []) {
    if (typeof level === "object") return null;
    const proving = this.active.find(obligation => obligation.level === level && attempt(() => scope.equal(obligation.type, type)));
    if (proving) return null;
    const quantified = [...[...scope.context].map(([name, stated]) => ({ term: T.variable(name), type: stated })),
      ...this.locals, ...this.hints, ...scope.evidence].flatMap(evidence => {
        const body = headBeta(evidence.type);
        if (body?.tag !== "Pi" && body?.tag !== "LPi") return [];
        const shape = ruleShape(evidence.type);
        return shape.refusal ? [] : [{ term: evidence.term, shape }];
      });
    this.active.push({ level, type });
    try {
      for (const rule of [...quantified, ...this.rules]) {
        const { conclusion } = rule.shape;
        if (!below(conclusion.level, level)) continue;
        scope.spend("candidates");
        const values = instance(rule.shape, universe, type, scope);
        if (!values) continue;
        try {
          const term = this.apply(rule, values, scope, chain, names);
          if (term) return this.lift(conclusion.level, level, universe, type, term);
        } catch (error) {
          if (!(error instanceof HLevelUnproved)) throw error;
          failures.push(error);
        }
      }
      return null;
    } finally { this.active.pop(); }
  }

  // A rule applied to its arguments, in the order of its binders: a
  // universe or a parameter read from the match, or a premise's evidence,
  // which later binders may mention. Matching the carrier does not make a
  // parameter's value inhabit its domain, as a type too large for it: the
  // kernel checks it, and where it does not, null, and the search goes on.
  apply(rule, values, scope, chain, names) {
    values = new Map(values);
    let term = rule.term;
    for (const binder of rule.shape.binders) {
      if (binder.universe) { term = T.levelApply(term, values.get(binder.name)); continue; }
      if (binder.premise) values.set(binder.name, this.premise(binder.premise, values, scope, chain, names));
      else if (!scope.accepts(values.get(binder.name), substituteAll(binder.domain, values))) return null;
      term = T.app(term, values.get(binder.name));
    }
    return term;
  }

  // Evidence for a rule's premise, its parameters read from the match: under
  // its binders, at fresh variables, as the structural rules prove a Π's.
  premise({ binders, level, universe, type }, values, scope, chain, names) {
    const [first, ...rest] = binders;
    if (!first) return this.prove(level, substituteLevel(universe, values), substituteAll(type, values), scope, chain, null, names);
    const domain = substituteAll(first.domain, values), name = scope.fresh(first.name);
    const inner = new Map(values).set(first.name, T.variable(name));
    return T.lam(name, domain, this.premise({ binders: rest, level, universe, type }, inner, scope.bind(name, domain), chain,
      new Map(names).set(name, first.name)));
  }

  // Evidence in scope, local or a hint, stating the level or a lower one.
  evidence(level, universe, type, scope) {
    const candidates = [...[...scope.context].map(([name, stated]) => [T.variable(name), stated]),
      ...[...this.locals, ...this.hints, ...scope.evidence].map(evidence => [evidence.term, evidence.type])];
    for (let [term, stated] of candidates) {
      if (this.instantiate) {
        const specialized = specializeEvidence(term, stated, type, scope);
        if (specialized) ({ term, type: stated } = specialized);
      }
      const known = statement(stated);
      if (!known) continue;
      scope.spend("candidates");
      if (typeof known.level === "object") {
        // A level that is no numeral gives only itself, in the same universe:
        // at a variable level, HasLevel does not reduce, so the universe is
        // part of the statement.
        if (typeof level !== "object") continue;
        if (scope.equal(stated, applied("HasLevel", universe, level.term, type))) return term;
        continue;
      }
      if (!below(known.level, level) || !scope.equal(known.type, type)) continue;
      return this.lift(known.level, level, universe, type, term);
    }
    return null;
  }

  // From evidence at `from` to evidence at `to`, at or above it.
  lift(from, to, universe, type, term) {
    if (from === to) return term;
    if (from === "contr") return applied("contr_has_level", universe, levelTerm(to), type, term);
    if (typeof to === "object") return applied("prop_has_level", universe, to.term, type, term);
    for (let n = from; n < to; n++) term = T.app(T.app(applied("level_up", universe, numeral(n)), type), term);
    return term;
  }

  // An h-level statement is a proposition, and so has every level.
  statementRule(level, universe, type, scope) {
    const inner = statement(type);
    if (!inner || level === "contr") return null;
    scope.spend("candidates");
    const isProp = inner.level === "contr" ? applied("is_contr_is_prop", inner.universe, inner.type)
      : T.app(applied("has_level_is_prop", inner.universe,
        typeof inner.level === "object" ? inner.level.term : numeral(inner.level)), inner.type);
    return applied("prop_has_level", universe, levelTerm(level), type, isProp);
  }

  // The type's weak head: Π, Σ and paths by their parts; Unit, Void, Nat.
  structure(level, universe, type, scope, chain, names) {
    scope.spend("candidates");
    if (typeof level === "object")
      throw new HLevelUnproved(chain, `nothing in scope states that ${this.show(type)} has level ${this.show(level.term)}`);
    const head = scope.nf(type);
    const unproved = reason => { throw new HLevelUnproved(chain, reason); };
    // The family of a Π or Σ over its own binder, and evidence for its body at
    // a fresh variable.
    const family = binder => T.lam(binder.name, binder.domain, binder.body);
    const body = binder => {
      const name = scope.fresh(binder.name);
      const inner = scope.bind(name, binder.domain);
      const evidence = this.prove(level, universe, substituteTerm(binder.body, binder.name, T.variable(name)), inner, chain,
        binder, new Map(names).set(name, binder.name));
      return T.lam(name, binder.domain, evidence);
    };
    switch (head.tag) {
      case "Pi":
        return level === "contr" ? applied("pi_is_contr", universe, head.domain, family(head), body(head))
          : applied("pi_has_level", universe, numeral(level), head.domain, family(head), body(head));
      case "Sigma": {
        const domain = this.prove(level, universe, head.domain, scope, chain, null, names);
        return level === "contr" ? applied("sigma_is_contr", universe, head.domain, family(head), domain, body(head))
          : applied("sigma_has_level", universe, numeral(level), head.domain, family(head), domain, body(head));
      }
      case "Path": {
        if (freeDimensions(head.family).has(head.dim)) {
          // Carry the homogeneous path's h-level statement from the start
          // of the line to its end. The family at t is the path over
          // A(t ∧ i), with its right endpoint universally quantified; at
          // t = 0 it is a homogeneous path, and at t = 1 the wanted PathP.
          const t = scope.fresh("path_level"), y = scope.fresh("path_endpoint");
          // Substitution constructs fresh syntax: check it before a head
          // query so neutral path applications retain their annotations.
          const start = scope.infer(substituteDimension(head.family, head.dim, I.zero)).term;
          const along = substituteDimension(head.family, head.dim, I.variable(t));
          const shortened = substituteDimension(head.family, head.dim, I.meet(I.variable(t), I.variable(head.dim)));
          const path = T.path(head.dim, shortened, head.left, T.variable(y));
          const stated = level === "contr" ? applied("IsContr", universe, path)
            : applied("HasLevel", universe, numeral(level), path);
          const family = T.pi(y, along, stated);
          const evidence = this.prove(level === "contr" ? "contr" : level + 1, universe, start, scope, chain, null, names);
          const base = level === "contr" ? applied("path_is_contr", universe, start, evidence, head.left, T.variable(y))
            : T.app(T.app(evidence, head.left), T.variable(y));
          return T.app(T.comp(t, family, [], T.lam(y, start, base)), head.right);
        }
        return level === "contr"
          ? applied("path_is_contr", universe, head.family, this.prove("contr", universe, head.family, scope, chain, null, names),
            head.left, head.right)
          : applied("path_has_level", universe, numeral(level), head.family,
            this.prove(level + 1, universe, head.family, scope, chain, null, names), head.left, head.right);
      }
      case "Unit":
        return level === "contr" ? lemma("unit_is_contr")
          : applied("contr_has_level", universe, numeral(level), T.unit, lemma("unit_is_contr"));
      case "Void":
        if (level === "contr") unproved("Void is empty, so it is not contractible");
        return applied("prop_has_level", universe, numeral(level), T.void, lemma("void_is_prop"));
      case "Sort": {
        if(scope.equal(head,naturalSort)) {
          if(level==="contr"||level===0)unproved(`Nat is not ${named(level)}: 0 and 1 differ`);
          return this.lift(1,level,universe,head,lemma("nat_is_set"));
        }
        const record = scope.checker.kernel?.signatures.get(head.signature);
        const info = record && scope.checker.kernel.signature(record.index);
        if (!info?.modifier || !below(info.modifier - 1, level)) break;
        const index = info.constructors.length - 1;
        // A generated squash is exactly the carrier's h-level witness;
        // it is a constructor term checked by ordinary instructions.
        return this.lift(info.modifier - 1, level, universe, head,
          T.constructor(index, head, record.constructors[index]));
      }
    }
    return unproved("no local evidence, hint or rule gives that");
  }
}

// A level with the rule's universe parameters given their values.
const substituteLevel = (level, values) => substituteAll({ tag: "U", level }, values).level;
const failedCandidate = error => {
  if(["fuel","budget","deadline"].includes(error?.kind))throw error;
  return false;
};
const attempt = check => { try { return check(); } catch(error) { return failedCandidate(error); } };

// Automatic clauses may use evidence for every fiber of a motive. Match
// the carrier of a folded h-level statement against the wanted carrier to
// determine all quantified arguments. This is candidate construction only:
// the resulting proof still goes through the kernel, including its domains.
// Matching is conservative and structural, not alpha-aware. Shadowed binder
// names can produce an unusable candidate; its subsequent kernel check keeps
// this limitation in completeness rather than proof validity.
function specializeEvidence(term, type, carrier, scope) {
  const parameters = [];
  let body = headBeta(type);
  while (body?.tag === "Pi") { parameters.push(body.name); body = headBeta(body.body); }
  const known = statement(body);
  if (!parameters.length || !known) return null;
  const variables = new Set(parameters), values = new Map();
  const match = (pattern, actual) => {
    pattern = pattern?.tag ? headBeta(pattern) : pattern;
    actual = actual?.tag ? headBeta(actual) : actual;
    if (pattern?.tag === "Var" && variables.has(pattern.name)) {
      if (values.has(pattern.name)) return scope.equal(values.get(pattern.name), actual);
      values.set(pattern.name, actual); return true;
    }
    if (pattern === actual) return true;
    if (!pattern || !actual || typeof pattern !== "object" || typeof actual !== "object") return false;
    const keys = Object.keys(pattern);
    if (keys.length !== Object.keys(actual).length) return false;
    return keys.every(key => Object.hasOwn(actual, key) && match(pattern[key], actual[key]));
  };
  if (!match(known.type, carrier) || parameters.some(name => !values.has(name))) return null;
  for (const name of parameters) { term = T.app(term, values.get(name)); body = substituteTerm(body, name, values.get(name)); }
  return { term, type: body };
}

// Whether a type of numeral level, or contractible, at `known` also has
// level `wanted`: a contractible type has every level, a proposition every
// level but contractibility, and a type of level n the numerals above n.
function below(known, wanted) {
  if (known === "contr") return true;
  if (wanted === "contr") return false;
  return known === 0 || typeof wanted === "number" && known <= wanted;
}

export { named as levelName };

// Inhabit a (possibly dependent) path using proposition evidence at its
// target fiber. Higher squash clauses call this on a path whose fiber is
// itself a path type; structure() reduces the required level accordingly.
export function pathEvidence(search, path, scope) {
  const fiber = substituteDimension(path.family, path.dim, I.one);
  const sort = scope.nf(scope.infer(fiber).type);
  if (sort.tag !== "U") throw Error("The path's fiber must live in a universe.");
  const prop = search.prove(0, sort.level, fiber);
  if (!freeDimensions(path.family).has(path.dim)) return T.app(T.app(prop, path.left), path.right);
  const transported = T.comp(path.dim, path.family, [], path.left);
  const equality = T.app(T.app(prop, transported), path.right);
  return T.app(transportToDependentPath(path.dim, path.family, path.left, path.right), equality);
}
