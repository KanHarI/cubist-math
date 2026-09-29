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
//   3. the type's weak head: Π, Σ and path types reduce to obligations on
//      their parts, and Unit, Void and Nat have their levels by lemmas.
// Each obligation spends a premise search, and each candidate a candidate,
// of the tactic's fuel. Every rule makes its obligations on strictly smaller
// types, so the search ends.
import { T, substituteTerm, freeNames } from "./core.mjs";
import { freeDimensions } from "./dimension-slots.mjs";

const LIBRARY = "hlevels";
const lemma = name => ({ tag: "DefRef", name: `${LIBRARY}__${name}` });
// A lemma of the library, at a universe level, applied to its arguments.
const applied = (name, universe, ...args) => args.reduce(T.app, T.levelApply(lemma(name), universe));

// A closed numeral's value, or null.
export function numeralValue(term) {
  let count = 0;
  for (; term?.tag === "Succ"; term = term.value) count++;
  return term?.tag === "Zero" ? count : null;
}
const numeral = n => Array.from({ length: n }).reduce(T.succ, T.zero);
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

export class HLevelSearch {
  // `scope` carries the tactic's fuel; `hints` are checked terms with their
  // types, and so are `locals`, the evidence that local definitions (have,
  // let, obtain) name; `show` displays a term in the goal's names.
  constructor(scope, hints, show, locals = []) {
    Object.assign(this, { scope, hints, show, locals });
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
    return this.evidence(level, universe, type, scope)
      ?? this.statementRule(level, universe, type, scope)
      ?? this.structure(level, universe, type, scope, chain, names);
  }

  // Evidence in scope, local or a hint, stating the level or a lower one.
  evidence(level, universe, type, scope) {
    const candidates = [...[...scope.context].map(([name, stated]) => [T.variable(name), stated]),
      ...[...this.locals, ...this.hints].map(evidence => [evidence.term, evidence.type])];
    for (const [term, stated] of candidates) {
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
        // A path over a line of types is no path type of one type.
        if (freeDimensions(head.family).has(head.dim)) break;
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
      case "Nat":
        if (level === "contr" || level === 0) unproved(`Nat is not ${named(level)}: 0 and 1 differ`);
        return this.lift(1, level, universe, T.nat, lemma("nat_is_set"));
    }
    return unproved("no local evidence, hint or rule gives that");
  }
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
