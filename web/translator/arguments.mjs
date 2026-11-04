// Arguments a call determines (work-plan L4.1a, L4.1b). A hole `_` in an
// argument's place, and a named argument `x := e`, which gives the parameter
// x: the parameters before it that no argument gives are holes too, and those
// after the last one given are left to a later application, as in f(a). A
// definition's implicit parameters, `def f{{A : U}}(x : A)`, are not given
// among its other arguments: before the last argument given, each is a hole
// unless double braces after the name, f{{Nat}}(x), or its name give it.
//
// A universe argument that is a hole is the least universe the call needs:
// the largest of the universes its arguments' types say it must contain, or
// the one an equality of types fixes. Where nothing bounds it and the call's
// type depends on it, it is refused; where the call's type does not, any
// universe would do, and it is the least, U0.
//
// A hole is solved at its own call, from the types of the call's other
// arguments and the type the call is expected to have, by first-order
// unification that descends only where equality is equality of parts: type
// formers, constructors and neutral terms. A definition is unfolded rather
// than matched by its arguments, since a defined function need not be
// injective. A solution is accepted only when it is determined: it mentions
// neither the hole nor a variable bound inside the constraint, and it is not
// a universe where cumulativity would admit a larger one as well. The kernel
// checks every solution at its type, and every written argument is checked
// against its parameter's type, as in a call without holes, so an unsolved
// hole never reaches the kernel. Nothing is searched for: a hole is never
// filled because some inhabitant of its type exists. A scope-blocked candidate
// is reduced only as a last resort, after the other constraints have had their say.
import {propagateElaborationStop,propagateLimit} from "./control.mjs";
import {T,finiteLevel,substituteTerm,substituteDimension,freeNames,levelNames,betaReduce,isTerm} from "./core.mjs";
import {universeText} from "../cubical-levels.mjs";
import {interval as I} from "./lattice.mjs";
import {freeDimensions,bindDimensions} from "./dimension-slots.mjs";
import {dimensionScope,termBinders,termFields} from "./term-shape.mjs";
import {syntaxGraphBudget,dimensionContextKey} from "./syntax-graph.mjs";
import {statement as hlevelStatement} from "./hlevel.mjs";
import {INDUCTIVE_TAGS} from "./inductive.mjs";
import {stem} from "./names.mjs";

import {assignArguments} from "../cubist/call-arguments.mjs";
export {assignArguments} from "../cubist/call-arguments.mjs";

export const isHole = node => node?.kind === "name" && node.name === "_";
// Whether a call needs this elaboration: it has a hole, a named argument or
// implicit arguments in braces.
export const determinesArguments = node =>
  node.kind === "call" && (!!node.implicitArgs || node.args.some(arg => arg.kind === "namedArgument" || isHole(arg)));

// A builtin, a name the module does not bind, and a declared type or a
// constructor take their arguments written out, in parentheses: a call of
// one with arguments in double braces, a named argument or, unless `holes`
// (a pattern's, evaluation.mjs), a hole is refused.
export function writtenOut(n, scope, holes = false) {
  const {env, unit} = scope;
  const headName = n.fn.kind === "name" ? n.fn.name : null;
  const spelling = n.fn.spelling ?? headName;
  const builtin = headName && !env.has(headName);
  if (!builtin && !INDUCTIVE_TAGS.has(env.get(headName)?.tag)) return;
  if (n.implicitArgs)
    throw unit.locate(Error(`${spelling} has no implicit parameters: give its arguments in parentheses, as ${spelling}(…).`), n.fn);
  if (!n.args.some(arg => arg.kind === "namedArgument" || !holes && isHole(arg))) return;
  throw unit.locate(Error(builtin
    ? `${spelling} takes its arguments explicitly: a hole _ or a named argument is an argument of a definition or a function.`
    : `${spelling} is a declared type or a constructor, whose arguments are written out: a hole _ or a named argument is an argument of a definition or a function.`), n.fn);
}

// Running out of fuel, steps or time ends the elaboration that asked.

// A definition's own parameters, {name, implicit}, as its source declares
// them, or null: a function that is not a definition has none. A head that
// is already a call, as choose(1) in choose(1)(2), has those the earlier call
// left; the assumptions a definition uses are applied to it already
// (define), and are none of its parameters.
function sourceParameters(t, head) {
  let core = head, applied = 0;
  for (; core.tag === "App" || core.tag === "LApp"; core = core.fn) applied++;
  const view = core.tag === "DefRef" ? t.checker.definitionViews?.get(core.name) : null;
  if (!view?.parameters) return null;
  const consumed = applied - (view.assumptions?.size ?? 0);
  return consumed > 0 ? view.parameters.slice(consumed) : view.parameters;
}

// Elaborate a call of a definition or a function: its written arguments,
// its holes and its named arguments, from the function's type.
export function elaborateCall(t, n, scope, expected) {
  const {env, unit} = scope;
  const headName = n.fn.kind === "name" ? n.fn.name : null;
  const called = n.fn.spelling ?? headName ?? "This function";
  const bound = headName ? env.get(headName) : undefined;
  writtenOut(n, scope);
  if (bound?.tag === "Recursive") {
    if (n.implicitArgs)
      throw unit.locate(Error(`A recursive call of ${headName} passes its implicit parameters unchanged: give only the others, as ${headName}(…).`), n.fn);
    if (determinesArguments(n))
      throw unit.locate(Error(`A recursive call of ${headName} takes its arguments explicitly.`), n.fn);
  }
  const head = t.term(n.fn, scope, null);
  const parameters = sourceParameters(t, head);
  const given = assignArguments(n, parameters, unit, called);
  // Each parameter in turn, from the head's type, with the earlier ones
  // replaced by variables that stand for their values: no argument's type is
  // inferred again from the growing application.
  const slots = [], solver = new ArgumentSolver(t, scope, slots, called, n);
  let type = scope.infer(head).type;
  for (let index = 0; ; index++) {
    const node = given(index);
    if (node === undefined) break;
    // A type that computes to a function type may need the earlier
    // arguments' values: those are elaborated first.
    if (type.tag !== "Pi" && type.tag !== "LPi") {
      solver.run(false);
      type = solver.scopeOf().nf(solver.queryView(type));
    }
    const parameter = parameters?.[index]?.name ?? null;
    const site = node ?? n.fn;
    // Instantiation at a universe, below UU0 (G0 §2.7); a hole there is a
    // universe to infer, a placeholder level until it is solved.
    if (type.tag === "LPi") {
      if (!node || isHole(node)) {
        const variable = unit.names.placeholder(parameter ?? "universe");
        solver.add({index, parameter, node, variable, universe: true, kind: node === null ? "omitted" : "hole"});
        type = substituteTerm(type.body, type.name, {tag: "Var", name: variable});
        continue;
      }
      const level = t.levelOf(node, scope);
      if (!finiteLevel(level)) throw unit.locate(Error("A universe argument must lie below UU0: U0, U1, … or a universe variable."), node);
      slots.push({index, parameter, node, level});
      type = substituteTerm(type.body, type.name, level);
      continue;
    }
    if (type.tag !== "Pi") {
      // Arguments by position skip the implicit parameters.
      const implicit = parameters?.filter(parameter => parameter.implicit).map(parameter => parameter.name) ?? [];
      const explicit = index - implicit.length;
      throw unit.locate(Error(!index ? "Source application is not a function."
        : implicit.length ? `${called} takes ${explicit} argument${explicit === 1 ? "" : "s"} by position; give its implicit parameters ${implicit.join(", ")} in double braces, in order or by name, as ${called}{{…}}(…) or ${called}{{${implicit[0]} := …}}(…).`
        : `${called} takes ${index} argument${index === 1 ? "" : "s"}; this is one more.`), site);
    }
    // A name no source or ordinary fresh-name request spells, so a call without holes
    // leaves the declaration's generated names as they were.
    const variable = unit.names.placeholder(parameter ?? "argument");
    solver.add({index, parameter, node, variable, domain: type.domain,
      kind: node === null ? "omitted" : isHole(node) ? "hole" : "argument"});
    type = substituteTerm(type.body, type.name, T.variable(variable));
  }
  if (expected) solver.require(type, expected, {expected: true});
  solver.result = type;
  solver.run();
  solver.checkSolutions();
  // The call, each argument as elaborated and each hole's solution, all
  // checked at their types.
  let term = head;
  for (const slot of slots)
    term = slot.level !== undefined ? T.levelApply(term, slot.level)
      : slot.universe ? T.levelApply(term, solver.solution.get(slot.variable))
      : T.app(term, slot.kind === "argument" ? slot.value : solver.zonk(T.variable(slot.variable)));
  solver.record(n, term);
  return term;
}

// The unknowns of one call and its constraints. Each slot's variable stands
// for its value: a hole's is found by unification, a written argument's by
// elaborating it once its parameter's type mentions no unknown. The
// unknowns not substituted where the kernel is asked (view) are entries of a
// scope of the solver's own (scopeOf), for the head queries about types
// that mention them. The call's arguments are elaborated in its own scope.
class ArgumentSolver {
  constructor(t, scope, slots, called, call) {
    Object.assign(this, {t, scope, slots, called, call});
    // The changes to the unknowns and their solutions, counted, and what was
    // made for the kernel's queries after the last (view, scopeOf).
    this.changes = 0;
    this.scopes = new WeakMap();
    this.viewed = null;
    // Each slot whose solution the kernel accepted at its type, with that
    // solution (fits).
    this.fitted = new Map();
    // The solved holes whose types have bounded their parameters' types.
    this.typed = new Set();
    // Whether the call has a hole or a named argument as written.
    this.written = determinesArguments(call);
    this.byVariable = new Map();
    // Each universe placeholder's bounds: {lower, upper, equal}.
    this.bounds = new Map();
    this.solution = new Map();
    this.pending = [];
    // A hole a universe would solve, were a larger one not as good.
    this.ambiguous = new Map();
    // A hole that only a term mentioning a bound variable would solve.
    this.escaping = new Map();
    this.clashes = [];
    // Whether one definition applied on both sides may be matched argument
    // by argument: only as a last resort (approximate).
    this.approximating = false;
  }
  // The term with every solved unknown replaced by its value. A solution
  // never mentions its own variable, so this ends.
  zonk(term) {
    if (!this.solution.size) return term;
    for (let round = 0; round <= this.slots.length; round++) {
      const solved = [...freeNames(term)].filter(name => this.solution.has(name));
      if (!solved.length) return term;
      for (const name of solved) term = substituteTerm(term, name, this.solution.get(name));
    }
    return term;
  }
  unknowns(term) {return [...freeNames(term)].filter(name => this.byVariable.has(name) && !this.solution.has(name));}
  // Whether the call has a hole: one written, an omitted parameter, or an
  // implicit one.
  get determined() {return this.written || this.slots.some(slot => slot.kind === "hole" || slot.kind === "omitted");}
  // A hole's variable, unsolved: the only unknowns unification may solve.
  flexible(term) {
    const slot = term?.tag === "Var" ? this.byVariable.get(term.name) : null;
    return slot && slot.kind !== "argument" && !slot.universe && !this.solution.has(term.name) ? slot : null;
  }
  add(slot) {
    this.slots.push(slot);
    this.byVariable.set(slot.variable, slot);
    if (slot.universe) this.bounds.set(slot.variable, {lower: [], upper: [], equal: null});
    this.changes++;
  }
  // An unknown solved.
  settle(variable, value) {
    this.solution.set(variable, value);
    this.changes++;
  }
  // What the kernel is asked about: the call's scope, with an entry for each
  // unknown not substituted, and the substitution of the others. A universe
  // placeholder is substituted once solved, at its solution; a hole or an
  // argument once solved by a value known to have its type there (fits).
  // Any other is an entry at its type as it stands here, a universe's a
  // level entry, so that the scope's types and the terms asked about agree.
  // A hole A? : U(V?) solved as B : U(W) stays an entry until V? is solved:
  // with V? free, B is no U(V?), and Square(V?, B, …) is no type. Nothing is
  // read at a level it may not keep: a placeholder is substituted only at its
  // solution. `withheld` holds the solved unknowns left as entries. Made
  // again after each change to the unknowns or their solutions.
  view() {
    if (this.viewed?.changes === this.changes) return this.viewed;
    let scope = this.scope;
    const substitution = new Map(), withheld = new Set();
    for (const slot of this.slots) {
      if (!slot.variable) continue;
      const solved = this.solution.get(slot.variable);
      if (slot.universe) {
        if (solved !== undefined) substitution.set(slot.variable, solved);
        else scope = scope.withVariable(slot.variable, T.bound).scope;
        continue;
      }
      const domain = substituted(slot.domain, substitution);
      if (solved !== undefined) {
        const value = substituted(solved, substitution);
        if (this.fits(slot, solved, value, domain, scope, withheld)) { substitution.set(slot.variable, value); continue; }
        withheld.add(slot.variable);
      }
      scope = scope.withVariable(slot.variable, domain).scope;
    }
    return this.viewed = {changes: this.changes, scope, substitution, withheld};
  }
  // Whether a solved slot's value, as the kernel is asked about it, is
  // known to have its type there, in the scope of the slots before it.
  // Known when neither mentions an unknown: the kernel checks the solution
  // at that type before the call is made (checkSolutions), and a call whose
  // solution does not fit fails there. Not known when either mentions an
  // unknown the scope has no entry for yet, or one withheld. Otherwise the
  // kernel is asked, once for each solution it accepts: a judgement stays
  // true as the unknowns in it are solved.
  fits(slot, solved, value, domain, scope, withheld) {
    const unknowns = [...freeNames(value), ...freeNames(domain)].filter(name => this.byVariable.has(name));
    if (!unknowns.length) return true;
    if (unknowns.some(name => withheld.has(name) || !scope.context.has(name))) return false;
    if (this.fitted.get(slot) === solved) return true;
    let accepted;
    try { accepted = scope.accepts(value, domain); }
    catch (error) { propagateLimit(error); accepted = false; }
    if (accepted) this.fitted.set(slot, solved);
    return accepted;
  }
  // A term as the kernel is asked about it (view).
  queryView(term) {return substituted(term, this.view().substitution);}
  // The same, and a term that is a withheld unknown as its solution is asked
  // about: a constraint's side is a term on its own, in scope as it stands.
  opened(term) {
    const {substitution, withheld} = this.view();
    term = substituted(term, substitution);
    while (term?.tag === "Var" && withheld.has(term.name)) term = substituted(this.solution.get(term.name), substitution);
    return term;
  }
  // Whether a term mentions a solved unknown left as an entry (view).
  mentionsWithheld(term) {
    const {withheld} = this.view();
    return withheld.size > 0 && [...freeNames(term)].some(name => withheld.has(name));
  }
  // The scope the solver asks about its terms in: the view's, with each
  // binder a constraint has descended under, `chain` (innermost first,
  // {name, domain} or {dimension}), at its domain as the kernel is asked
  // about it. A term is asked about there as it stands when it is asked,
  // so it mentions no unknown the scope leaves out and agrees with the types
  // the scope gives the others: a binder bound at its domain as it stood
  // before a placeholder in it was solved, Magma(V?) where V? = V, would
  // make Magma.M(V, B) ill-typed. Made again after each change.
  scopeOf(chain = null) {
    const known = this.scopes.get(chain ?? this);
    if (known?.changes === this.changes) return known.scope;
    const scope = !chain ? this.view().scope
      : chain.dimension !== undefined ? this.scopeOf(chain.next).bindDimension(chain.dimension)
      : this.scopeOf(chain.next).withVariable(chain.name, this.queryView(chain.domain)).scope;
    this.scopes.set(chain ?? this, {changes: this.changes, scope});
    return scope;
  }
  // A level with each solved universe placeholder replaced, as in zonk.
  zonkLevel(level) {return this.zonk({tag: "U", level}).level;}
  // The universe placeholder a level is, unsolved, or null.
  placeholder(level) {
    const slot = level?.tag === "Var" ? this.byVariable.get(level.name) : null;
    return slot?.universe && !this.solution.has(level.name) ? slot : null;
  }
  // Whether a level mentions a universe placeholder not yet solved.
  levelUnknown(level) {return [...levelNames(level)].some(name => this.byVariable.has(name) && !this.solution.has(name));}
  // Two levels where `polarity` relates them: covariant, the first at most
  // the second, as U(a) inhabits U(b) when a ≤ b; invariant, equal. A bound
  // on a placeholder is recorded; anything else waits for the kernel.
  relateLevels(smaller, larger, polarity) {
    smaller = this.zonkLevel(smaller); larger = this.zonkLevel(larger);
    if (!this.levelUnknown(smaller) && !this.levelUnknown(larger)) return "done";
    const below = this.placeholder(smaller), above = this.placeholder(larger);
    if (polarity === "invariant") {
      if (below && !this.levelUnknown(larger)) this.equalLevel(below, larger);
      else if (above && !this.levelUnknown(smaller)) this.equalLevel(above, smaller);
      else return "stuck";
      return "done";
    }
    if (above && !this.levelUnknown(smaller)) this.bounds.get(above.variable).lower.push(smaller);
    else if (below && !this.levelUnknown(larger)) this.bounds.get(below.variable).upper.push(larger);
    else return "stuck";
    return "done";
  }
  // A placeholder an equation determines, as an instance's universe
  // matched against another's: solved at once, to the level solveUniverses
  // would give it from that bound, which comes before every other. The rest
  // of the constraint then reads the level, where it compared, part by part
  // and unfolded, the types that mention the placeholder. A level not below
  // ω stays a bound, for solveUniverses to refuse.
  equalLevel(slot, level) {
    const bounds = this.bounds.get(slot.variable);
    bounds.equal ??= level;
    if (finiteLevel(bounds.equal) && !this.solution.has(slot.variable)) this.settle(slot.variable, bounds.equal);
  }
  // Solve the universe placeholders that bounds determine: by an equality,
  // or as the largest lower bound. With `last`, also those nothing bounds
  // that the call's type does not mention, as U0. True when one was solved.
  solveUniverses(last = false) {
    let solved = false;
    for (const [variable, bounds] of this.bounds) {
      if (this.solution.has(variable)) continue;
      let level = this.least(bounds);
      if (level === null && last && !freeNames(this.zonk(this.result ?? T.unit)).has(variable)) level = 0;
      if (level === null) continue;
      const slot = this.byVariable.get(variable);
      if (!finiteLevel(level))
        throw this.scope.unit.locate(Error(`The universe ${slot.parameter ?? "argument"} of ${this.called} would be ${universeText(level)}, which is not below UU0. Give it explicitly.`), slot.node ?? this.call.fn);
      this.settle(variable, level);
      solved = true;
    }
    return solved;
  }
  // The level bounds give a placeholder: its equation, or the largest of its
  // lower bounds; null when it has neither.
  least({lower, equal}) {
    if (equal !== null || !lower.length) return equal;
    return lower.every(bound => typeof bound === "number") ? Math.max(...lower)
      : lower.reduce((left, right) => ({tag: "LMax", left, right}));
  }
  // `smaller` has to inhabit what `larger` does: an argument's type and its
  // parameter's, or the call's type and the one expected of it.
  require(smaller, larger, origin) {
    this.pending.push({smaller, larger, origin});
  }
  // Elaborate the arguments and solve the holes, as far as they go; when
  // `complete`, a hole left open is an error.
  run(complete = true) {
    for (;;) {
      let progress = this.retry();
      for (const slot of this.slots) {
        if (slot.kind !== "argument" || this.solution.has(slot.variable)) continue;
        const domain = this.zonk(slot.domain);
        if (!this.unknowns(domain).length) {
          // The holes its type mentions are checked first, so that the type
          // it is checked at is a type.
          this.checkSolutions(slot.index);
          slot.value = this.t.term(slot.node, this.scope, domain);
          // The later parameters' types take the term the kernel derived,
          // which carries its annotations, as a type the kernel inferred does.
          // Where unification found holes, the argument is checked at its
          // parameter's type, so that a wrong solution is reported here;
          // otherwise the call's own check compares the two, at no extra
          // kernel work.
          // A generator's checked application validates each argument here
          // before extracting solved values, including fully positional calls.
          // This policy is independent of whether source arguments had labels.
          try { this.settle(slot.variable, this.determined||this.call.checkArguments
            ? this.scope.check(slot.value, domain) : this.scope.infer(slot.value).term); }
          catch (error) {propagateElaborationStop(error); throw this.scope.unit.locate(error, slot.node); }
          progress = true;
        } else if (!slot.tried) {
          // Its type, to solve the holes its parameter's type mentions; the
          // argument itself is elaborated again against that type once the
          // holes are solved.
          slot.tried = true;
          const inferred = this.infer(slot.node);
          if (inferred) { this.require(inferred, slot.domain, {slot}); progress = true; }
        }
      }
      // A hole solved at a type that mentions unknowns bounds them by the
      // solution's own type, as a written argument's type does: a
      // constraint like any other, solved here or waiting, never while
      // approximate() guesses.
      for (const slot of this.slots) {
        if (slot.kind === "argument" || slot.universe || this.typed.has(slot) || !this.solution.has(slot.variable)) continue;
        const domain = this.zonk(slot.domain), value = this.zonk(T.variable(slot.variable));
        if (!this.unknowns(domain).length || this.unknowns(value).length) continue;
        this.typed.add(slot);
        this.require(this.scope.infer(value).type, slot.domain, {slot});
        progress = true;
      }
      if (progress) continue;
      if (complete && this.approximate()) continue;
      // Universes last: once every argument has said what it needs.
      if (!complete) break;
      if (this.solveUniverses() || this.solveUniverses(true)) continue;
      // Then a hole that states an h-level, by the hlevel search.
      if (!this.fillLevels()) break;
    }
    const open = this.slots.find(slot => slot.variable && !this.solution.has(slot.variable));
    if (open && complete) throw this.undetermined(open);
  }
  // When nothing else makes progress: a pending constraint between one
  // definition applied on both sides, as T.Hom(A, B) against T.Hom(M, N),
  // matched argument by argument. That solves what unfolding cannot, but
  // it is a guess where the definition does not determine its arguments,
  // as Family(n) := Nat does not determine n, so it waits until every other
  // constraint has had its say, and keeps a constraint's solutions only
  // when all of it agrees. True when one was kept.
  approximate() {
    let progress = false;
    this.approximating = true;
    try {
      for (const constraint of this.pending.splice(0)) {
        const saved = this.snapshot();
        if (this.unify(constraint.smaller, constraint.larger, constraint.origin, "covariant", new Set(), null) === "done") {
          progress = true;
          continue;
        }
        this.restore(saved);
        this.pending.push(constraint);
      }
    } finally { this.approximating = false; }
    return progress;
  }
  // Each pending constraint, once more; those still blocked stay.
  retry() {
    let progress = false;
    for (let changed = true; changed;) {
      changed = false;
      const pending = this.pending.splice(0);
      for (const constraint of pending) {
        const before = this.solution.size;
        const outcome = this.unify(constraint.smaller, constraint.larger, constraint.origin, "covariant", new Set(), null);
        if (outcome === "stuck") this.pending.push(constraint);
        // The kernel's check of the argument reports it, unless a hole it
        // leaves open is reported first, with this as the reason.
        if (outcome === "clash") this.clashes.push(constraint);
        if (this.solution.size > before || outcome === "done") changed = progress = true;
      }
    }
    return progress;
  }
  // An argument's type with no expected type, or null when it needs one. The
  // attempt records no inspector references and no proof steps.
  infer(node) {
    const {t, scope} = this, observations = scope.unit.observations.fork("argument-inference",{visible:false});
    const quiet = scope.withUnit(scope.unit.with({references:null,steps:null,observations}));
    try { return quiet.infer(t.term(node, quiet, null)).type; }
    catch (error) {
      propagateLimit(error);
      return null;
    }
    finally { observations.discard(); }
  }
  // One constraint between two terms: "done", "stuck" (for now) or "clash",
  // when they cannot agree. `polarity` is "covariant" where a larger
  // universe would also do, `bound` the variables and `chain` the binders,
  // dimensions too, that the constraint has descended under (scopeOf). The
  // solver decides on the terms with every solution in them (zonk), and asks
  // the kernel about `asked`, the same two terms as they stood, with only
  // the solutions known to fit substituted (view).
  unify(left, right, origin, polarity, bound, chain, normal = false, asked = {left, right}) {
    left = this.zonk(left); right = this.zonk(right);
    const unknown = [...this.unknowns(left), ...this.unknowns(right)];
    // Only a hole is solved here; an argument's value is waited for.
    if (!unknown.some(name => this.byVariable.get(name).kind !== "argument")) return unknown.length ? "stuck" : "done";
    const hole = this.flexible(left), other = this.flexible(right);
    if (hole && other && hole === other) return "done";
    // A hole on the smaller side is at most the other; on the larger, at least.
    if (hole) return this.solve(hole, right, polarity, bound, chain, "upper", asked.right);
    if (other) return this.solve(other, left, polarity, bound, chain, "lower", asked.left);
    // An argument's variable stands for a value still to be elaborated.
    if (left.tag === "Var" && this.byVariable.has(left.name) || right.tag === "Var" && this.byVariable.has(right.name)) return "stuck";
    if (left.tag === right.tag && rigid(left, right, normal, this.byVariable)) {
      const outcome = this.parts(left, right, origin, polarity, bound, chain, asked);
      if (outcome !== "clash" || normal) return outcome;
    }
    // One definition applied on both sides, as T.Hom(A, B) or Tagged(U, A).
    if (!normal && sameDefinitionHead(left, right)) {
      // When nothing else made progress (approximate): its arguments, as
      // they stand. Unless they agree, nothing they solved is kept, and the
      // unfoldings are compared instead.
      if (this.approximating) {
        const saved = this.snapshot(), outcome = this.parts(left, right, origin, "invariant", bound, chain, asked);
        if (outcome === "done") return outcome;
        this.restore(saved);
      } else {
        // Otherwise the unfoldings first. Where they agree with a hole in
        // the arguments still open, as Tagged(U, A) := Nat leaves A, the
        // constraint waits: for other constraints to solve the hole, or for
        // approximate() to read it off the arguments.
        const outcome = this.unfolded(origin, polarity, bound, chain, asked);
        const open = [...this.unknowns(this.zonk(left)), ...this.unknowns(this.zonk(right))]
          .some(name => this.byVariable.get(name).kind !== "argument");
        return outcome === "done" && open ? "stuck" : outcome;
      }
    }
    // Different type formers never agree; other heads may, by eta.
    if (normal) return left.tag !== right.tag && CANONICAL.has(left.tag) && CANONICAL.has(right.tag) ? "clash" : "stuck";
    return this.unfolded(origin, polarity, bound, chain, asked);
  }
  // A definition, a redex or a projection: their head normal forms compared,
  // each asked about as it stands (view). A head that a withheld solution
  // blocks, or that mentions one, is not yet the term's: the constraint
  // waits until that solution is known to fit.
  unfolded(origin, polarity, bound, chain, asked) {
    let leftHead, rightHead;
    try {
      const scope = this.scopeOf(chain);
      leftHead = scope.nf(this.opened(asked.left)); rightHead = scope.nf(this.opened(asked.right));
    } catch (error) {
      propagateLimit(error);
      return "stuck";
    }
    if (this.mentionsWithheld(leftHead) || this.mentionsWithheld(rightHead)) return "stuck";
    return this.unify(leftHead, rightHead, origin, polarity, bound, chain, true);
  }
  // What the solver has found, to return to after a failed attempt.
  snapshot() {
    return { solution: new Map(this.solution), ambiguous: new Map(this.ambiguous), escaping: new Map(this.escaping),
      clashes: [...this.clashes], pending: [...this.pending], typed: new Set(this.typed), fitted: new Map(this.fitted),
      bounds: new Map([...this.bounds].map(([variable, bounds]) =>
        [variable, { ...bounds, lower: [...bounds.lower], upper: [...bounds.upper] }])) };
  }
  // A restored state is a change: the scopes made after the snapshot asked
  // about solutions no longer held.
  restore(saved) { Object.assign(this, saved); this.changes++; }
  // The parts of two terms with the same rigid head, each part asked about
  // as the same part of `asked` (unify).
  parts(left, right, origin, polarity, bound, chain, asked) {
    const askedLeft = this.opened(asked.left), askedRight = this.opened(asked.right);
    // The two sides have the same head as they are asked about.
    if (askedLeft?.tag !== left.tag || askedRight?.tag !== right.tag) return "stuck";
    const same = (l, r, al, ar, p = "invariant", b = bound, c = chain) => this.unify(l, r, origin, p, b, c, false, {left: al, right: ar});
    const field = (key, p) => same(left[key], right[key], askedLeft[key], askedRight[key], p);
    const all = outcomes => outcomes.includes("clash") ? "clash" : outcomes.includes("stuck") ? "stuck" : "done";
    // Both binders renamed to one fresh name, bound at the left one's domain,
    // as it is asked about, for the queries about the bodies.
    const under = p => {
      const name = this.scopeOf(chain).fresh(stem(left.name)), body = term => substituteTerm(term.body, term.name, T.variable(name));
      return same(body(left), body(right), body(askedLeft), body(askedRight), p, new Set(bound).add(name),
        {name, domain: askedLeft.domain, next: chain});
    };
    const dimension = (key, p) => {
      const dim = this.scopeOf(chain).fresh("i"), part = term => substituteDimension(term[key], term.dim, I.variable(dim));
      return same(part(left), part(right), part(askedLeft), part(askedRight), p, new Set(bound).add(dim), {dimension: dim, next: chain});
    };
    const each = key => left[key].map((item, index) => same(item, right[key][index], askedLeft[key][index], askedRight[key][index]));
    switch (left.tag) {
      case "Pi": return all([field("domain"), under(polarity)]);
      case "Sigma": return all([field("domain", polarity), under(polarity)]);
      case "Lam": return all([field("domain"), under()]);
      case "Path": return all([dimension("family", polarity), field("left"), field("right")]);
      case "PLam": return all([dimension("family"), dimension("body")]);
      case "PApp": return I.equal(left.arg, right.arg) ? field("path") : "stuck";
      case "App": return all([field("fn"), field("arg")]);
      case "LApp":
        if (this.levelUnknown(left.level) || this.levelUnknown(right.level))
          return all([this.relateLevels(left.level, right.level, "invariant"), field("fn")]);
        return JSON.stringify(left.level) === JSON.stringify(right.level) ? field("fn") : "clash";
      case "Fst": case "Snd": return field("pair");
      case "Sum": return all([field("left", polarity), field("right", polarity)]);
      case "Sort": {
        if (left.signature !== right.signature || left.parameters.length !== right.parameters.length) return "clash";
        // An instance's recorded universes are its own: equal on both sides.
        const levels = (left.levels ?? []).map((level, index) => right.levels?.[index] === undefined ? "done"
          : this.relateLevels(level, right.levels[index], "invariant"));
        return all([...levels, ...each("parameters")]);
      }
      case "Con": return left.index === right.index ? field("sort") : "clash";
      case "Elim":
        if (left.signature !== right.signature || left.clauses.length !== right.clauses.length) return "clash";
        return all([field("motive"), ...each("clauses")]);
      case "Var": case "DefRef": return left.name === right.name ? "done" : "clash";
      case "U":
        if (this.levelUnknown(left.level) || this.levelUnknown(right.level))
          return this.relateLevels(left.level, right.level, polarity);
        return JSON.stringify(left.level) === JSON.stringify(right.level) ? "done" : "stuck";
      case "Unit": case "Void": case "Point": return "done";
      default: return "stuck";
    }
  }
  // A hole's solution, when it is determined. `asked` is the value as the
  // kernel is asked about it (unify).
  solve(slot, value, polarity, bound, chain, side, asked = value) {
    value = this.zonk(value);
    const original = value;
    if (this.approximating) {
      // Let other arguments preserve a named type before reducing a scope-
      // blocked candidate. Only the fallback phase may expose its definition.
      const offending = new Set([...freeNames(value)].filter(name => name === slot.variable || bound.has(name)));
      const dimensions = new Set([...freeDimensions(value)].filter(dim => bound.has(dim) || !this.scope.dimensions.has(dim)));
      const blocked = term => [...freeNames(term)].some(name => offending.has(name))
        || [...freeDimensions(term)].some(dim => dimensions.has(dim));
      if (offending.size || dimensions.size) {
        value = betaReduce(value);
        if (blocked(value)) {
          // Its heads are asked about as the kernel is asked (view); an
          // unchanged candidate keeps its placeholders.
          const viewed = betaReduce(this.opened(asked)), reduced = reduceScopeCandidate(viewed, blocked, this.scopeOf(chain));
          if (reduced !== viewed) value = this.zonk(reduced);
        }
      }
    }
    const names = freeNames(value);
    // It would mention itself, or a variable bound inside the constraint.
    if (names.has(slot.variable)) return "stuck";
    const escaping = [...names].find(name => bound.has(name));
    if (escaping) { this.escaping.set(slot.variable, original); return "stuck"; }
    if ([...freeDimensions(value)].some(dim => bound.has(dim) || !this.scope.dimensions.has(dim))) return "stuck";
    // A universe where a larger one would do as well is a bound, not a
    // solution, unless a bound on the other side is the same universe.
    if (polarity === "covariant" && universeAt(value)) {
      const bounds = this.ambiguous.get(slot.variable) ?? {lower: [], upper: []}, key = JSON.stringify(value);
      bounds[side].push(value);
      this.ambiguous.set(slot.variable, bounds);
      if (!bounds[side === "lower" ? "upper" : "lower"].some(other => JSON.stringify(other) === key)) return "stuck";
    }
    this.settle(slot.variable, value);
    this.ambiguous.delete(slot.variable);
    return "done";
  }
  // Why a constraint failed, in words: its own display, or a part of a
  // message's whose `show` it is given.
  mismatch({smaller, larger, origin}, show = null) {
    const [found, wanted] = show ? [show(this.display(this.zonk(smaller))), show(this.display(this.zonk(larger)))]
      : this.t.shownTogether([this.display(this.zonk(smaller)), this.display(this.zonk(larger))], this.scope);
    return origin.expected ? `the call has type ${found}, where ${wanted} is expected`
      : `${this.source(origin.slot.node)} has type ${found}, where its ${this.describe(origin.slot)} has type ${wanted}`;
  }
  // The solved holes before `before`, each at its type, once: the kernel
  // checks them.
  checkSolutions(before = Infinity) {
    for (const slot of this.slots) {
      if (slot.index >= before) break;
      if (slot.kind === "argument" || slot.universe || !slot.variable || slot.checked || !this.solution.has(slot.variable)) continue;
      if (this.unknowns(this.zonk(slot.domain)).length) continue;
      slot.checked = true;
      this.checkSolution(slot, this.zonk(T.variable(slot.variable)));
    }
  }
  checkSolution(slot, value) {
    const type = this.zonk(slot.domain), result = this.scope.attempt(value, type);
    if (result.ok) { this.settle(slot.variable, result.term); return; }
    if (result.failure !== "mismatch") throw result.error;
    const [shown, typeText] = this.t.shownTogether([value, type], this.scope);
    throw this.scope.unit.locate(Error(`The hole for ${this.describe(slot)} of ${this.called} was solved as ${shown}, which does not have its type ${typeText}.`), slot.node ?? this.call.fn);
  }
  // A hole whose type states an h-level, as a model's setness field left out
  // of T.make(…), is proved by the search hlevel; uses (L2.5b): from the
  // evidence in scope and the registered rules. True when one was filled.
  fillLevels() {
    let progress = false;
    for (const slot of this.slots) {
      if (!slot.variable || slot.kind === "argument" || slot.universe || this.solution.has(slot.variable)) continue;
      const domain = this.zonk(slot.domain);
      if (this.unknowns(domain).length || !hlevelStatement(domain)) continue;
      const proof = this.t.hlevelEvidence(this.scope, domain);
      if (proof) { this.settle(slot.variable, proof); progress = true; }
    }
    return progress;
  }
  undetermined(slot) {
    if (slot.universe)
      return this.scope.unit.locate(Error(`Nothing determines the universe ${slot.parameter ?? "argument"} of ${this.called}: no argument's type bounds it, and the call's type depends on it. Give it explicitly.`), slot.node ?? this.call.fn);
    // The message's terms, its clash's too, are one display.
    const message = this.t.message(this.scope), show = message.show;
    const type = show(this.display(this.zonk(slot.domain)));
    const candidate = this.ambiguous.get(slot.variable), {called} = this, parameter = this.describe(slot);
    const escaping = this.escaping.get(slot.variable);
    const clash = this.clashes.length ? ` (${this.mismatch(this.clashes[0], show)})` : "";
    const error = slot.kind === "argument"
      ? Error(`The argument ${this.source(slot.node)} of ${called} needs the type of its ${parameter}, ${type}, which mentions a hole nothing determines${clash}. Give the hole explicitly.`)
      : candidate ? Error(`The ${parameter} of ${called} is not determined: ${show(candidate.lower[0] ?? candidate.upper[0])} fits, and so would ${candidate.lower.length ? "a larger" : "a smaller"} universe${clash}. Give it explicitly.`)
      : escaping ? Error(`The ${parameter} of ${called} would be ${show(this.display(escaping))}, which mentions a variable bound inside an argument, out of its scope${clash}. Give it explicitly.`)
      : Error(`Nothing determines the ${parameter} of ${called}, of type ${type}: not the other arguments' types, nor the type expected of the call${clash}. Give it explicitly.`);
    return this.scope.unit.locate(message.resolve(error), slot.node ?? this.call.fn);
  }
  describe(slot) {return slot.parameter ? `parameter ${slot.parameter}` : `argument ${slot.index + 1}`;}
  source(node) {return this.scope.unit.source.slice(node.start, node.end).trim();}
  // A term to show, with each unknown as ?name.
  display(term) {
    for (const name of this.unknowns(term)) {
      const slot = this.byVariable.get(name);
      term = substituteTerm(term, name, T.variable(`?${slot.parameter ?? slot.index + 1}`));
    }
    return term;
  }
  // The inspector shows what each hole and omitted parameter became.
  record(n, term) {
    const {t, scope} = this;
    // The omitted parameters, A := …, are one display, which writes their
    // names.
    const omitted = [], message = t.message(scope);
    for (const slot of this.slots) {
      if (!slot.variable || slot.kind === "argument") continue;
      // A universe is shown as the universe it is.
      const value = slot.universe ? T.universe(this.solution.get(slot.variable)) : this.zonk(T.variable(slot.variable));
      if (slot.kind === "hole")
        t.reference(scope, {...slot.node, name: "_", expressionSite: true, role: "inferred argument",
          description: `The ${slot.universe ? `universe ${slot.parameter ?? "argument"}` : this.describe(slot)} of ${this.called}, inferred: ${
            slot.universe ? universeText(this.solution.get(slot.variable)) : t.shown(value, scope)}.`}, value);
      else omitted.push(`${message.bind(slot.parameter)} := ${slot.universe ? universeText(this.solution.get(slot.variable)) : message.show(value)}`);
    }
    if (omitted.length && Number.isInteger(n.end))
      t.reference(scope, {name: ")", start: n.end - 1, end: n.end,
        ...(n.origin?{origin:n.origin}:{}),...(n.synthetic?{synthetic:true}:{}), expressionSite: true, role: "inferred arguments",
        description: message.text(`Arguments of ${this.called} inferred: ${omitted.join(", ")}.`)}, term);
  }
}

// A term with the solver's substitution for the kernel's queries applied
// (view): its values mention no variable it substitutes, so one pass does.
function substituted(term, substitution) {
  if (!substitution.size) return term;
  const names = [...freeNames(term)].filter(name => substitution.has(name));
  for (const name of names) term = substituteTerm(term, name, substitution.get(name));
  return term;
}

// A fallback scope check may need a definition beneath a type former.
// Visit the shared syntax once per scope it is met in. Retain a native head
// only if it removes the offending names; never revisit a decoded head as
// apparent progress. Candidate-local binders are not offending names: each
// is bound at its domain as the walk enters its body, so that a head asked
// there is asked in a context that has it.
function reduceScopeCandidate(value, blocked, at) {
  const memo = new WeakMap(), budget = syntaxGraphBudget(), contexts = new WeakMap(), mentioned = new WeakMap();
  let count = 0;
  const contextKey = scope => {
    if (!contexts.has(scope.context)) contexts.set(scope.context, ++count);
    return contexts.get(scope.context);
  };
  // The dimensions the types of a scope's variables mention: they stay in
  // scope under a dimension binder of the candidate that does not mention
  // them, as those variables do, and the binder is named and placed apart.
  const contextDimensions = scope => {
    let names = mentioned.get(scope.context);
    if (!names) {
      names = new Set();
      for (const type of scope.context.values()) if (isTerm(type)) for (const name of freeDimensions(type)) names.add(name);
      mentioned.set(scope.context, names);
    }
    return names;
  };
  // A dimension binder with its dimension named `name` in the parts it binds.
  const renamedDimension = (term, name) => {
    const rename = part => substituteDimension(part, term.dim, I.variable(name)), result = {...term, dim: name};
    for (const key of dimensionScope.get(term.tag))
      result[key] = key === "system" ? term.system.map(piece => ({...piece, term: rename(piece.term)})) : rename(term[key]);
    return result;
  };
  // A binder's body, its variable bound in the scope, apart from a variable
  // the scope has already: walked as the body that names that one, then
  // named as the binder again.
  const body = (term, scope) => {
    const level = term.tag === "LPi" || term.tag === "LLam";
    const {scope: inner, variable} = scope.withVariable(term.name, level ? T.bound : term.domain);
    if (variable === term.name) return reduce(term.body, inner);
    const renamed = substituteTerm(term.body, term.name, T.variable(variable)), walked = reduce(renamed, inner);
    return walked === renamed ? term.body : substituteTerm(walked, variable, T.variable(term.name));
  };
  const reduce = (term, scope) => {
    if (!term || typeof term !== "object") return term;
    const key = `${dimensionContextKey(scope.dimensions)}|${contextKey(scope)}`;
    const known = memo.get(term);
    if (known?.has(key)) return known.get(key);
    budget.tick();
    let result = term;
    if (isTerm(term)) {
      if (!blocked(term)) return term;
      if (term.tag !== "Var" && !CANONICAL.has(term.tag)) {
        try {
          let head = scope.nf(term);
          // A newly exposed type former cannot reduce at its head again;
          // its children may contain the ignored arguments we need to erase.
          if (CANONICAL.has(head.tag) && blocked(head)) head = reduce(head, scope);
          if (!blocked(head)) result = head;
        } catch (error) { propagateLimit(error); }
      }
    }
    if (result === term) {
      // Use the codec's binder allocation, including pruning dead outer
      // dimensions, when a candidate contains a path or composition family;
      // but the dimensions the scope's variables' types mention stay. A
      // binder named as one of them is walked renamed, and named back.
      const keys = dimensionScope.get(term.tag);
      if (keys && contextDimensions(scope).has(term.dim) && scope.dimensions.has(term.dim)) {
        const name = scope.fresh(term.dim), renamed = renamedDimension(term, name), walked = reduce(renamed, scope);
        result = walked === renamed ? term : walked.tag === term.tag && walked.dim === name ? renamedDimension(walked, term.dim) : walked;
        if (!known) memo.set(term, new Map([[key, result]]));
        else known.set(key, result);
        return result;
      }
      const inner = keys ? scope.with({dimensions: bindDimensions(term, scope.dimensions, contextDimensions(scope)).inner}) : scope;
      // The kernel view: a solution names what its annotations mention too.
      for (const [field, child] of termFields(term)) {
        const changed = field === "body" && termBinders.has(term.tag) ? body(term, scope) : reduce(child, keys?.includes(field) ? inner : scope);
        if (changed !== child) {
          if (result === term) result = Array.isArray(term) ? [...term] : {...term};
          result[field] = changed;
        }
      }
    }
    if (!known) memo.set(term, new Map([[key, result]]));
    else known.set(key, result);
    return result;
  };
  return betaReduce(reduce(value, at));
}

// Type formers: two with different heads are never equal.
const CANONICAL = new Set(["Pi", "Sigma", "Path", "U", "Sum", "Sort", "Unit", "Void"]);
// Whether two terms' parts can be compared as they are: a type former, a
// constructor, or a neutral term once in head normal form. A term headed by
// a definition, a redex or a projection is compared in head normal form.
function rigid(left, right, normal, unknown) {
  if (["Pi", "Sigma", "Lam", "Path", "PLam", "Sum", "Sort", "Con", "U", "Unit", "Void", "Point"].includes(left.tag)) return true;
  if (left.tag === "Var") return !unknown.has(left.name) && !unknown.has(right.name);
  if (left.tag === "DefRef") return left.name === right.name;
  // An application whose head is a local variable is neutral as it stands.
  if (left.tag === "App" || left.tag === "PApp") return normal || [left, right].every(term => neutralHead(term, unknown));
  return normal;
}
// Two applications, to terms and universes, of one definition, with as many
// arguments each.
function sameDefinitionHead(left, right) {
  const spine = term => {
    let length = 0;
    while (term.tag === "App" || term.tag === "LApp") { term = term.fn; length++; }
    return { head: term, length };
  };
  if (!["App", "LApp"].includes(left.tag) || left.tag !== right.tag) return false;
  const a = spine(left), b = spine(right);
  return a.head.tag === "DefRef" && b.head.tag === "DefRef" && a.head.name === b.head.name && a.length === b.length;
}
function neutralHead(term, unknown) {
  while (["App", "PApp", "Fst", "Snd"].includes(term.tag)) term = term.fn ?? term.path ?? term.pair;
  return term.tag === "Var" && !unknown.has(term.name);
}
// Whether a term is, or ends in, a universe where cumulativity applies: as
// itself, a function's codomain or a pair's component.
function universeAt(term) {
  if (term.tag === "U") return true;
  if (term.tag === "Pi") return universeAt(term.body);
  if (term.tag === "Sigma") return universeAt(term.domain) || universeAt(term.body);
  return false;
}
