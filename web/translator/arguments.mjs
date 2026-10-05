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
// filled because some inhabitant of its type exists.
import {T,finiteLevel,substituteTerm,substituteDimension,freeNames,levelNames} from "./core.mjs";
import {universeText} from "../cubical-levels.mjs";
import {interval as I} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";
import {INDUCTIVE_TAGS} from "./inductive.mjs";
import {stem} from "./names.mjs";

export const isHole = node => node?.kind === "name" && node.name === "_";
// Whether a call needs this elaboration: it has a hole, a named argument or
// implicit arguments in braces.
export const determinesArguments = node =>
  node.kind === "call" && (!!node.implicitArgs || node.args.some(arg => arg.kind === "namedArgument" || isHole(arg)));

// Placeholders for parameters' values, numbered apart from every name supply.
let placeholders = 0;

// Running out of fuel, steps or time ends the elaboration that asked.
const isLimit = error => ["fuel", "budget", "deadline"].includes(error?.kind);

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

// What a call's arguments give, parameter by parameter: a written argument,
// a hole, an omitted parameter (before the last one given), or nothing more.
// A named argument gives the parameter it names: an implicit one in double
// braces, f{{A := Nat}}(x), an explicit one in parentheses. The others in
// double braces fill the implicit parameters no name gives, in order; those
// in parentheses fill the explicit parameters no name gives, in order, and
// then whatever the result takes.
function assign(n, parameters, unit, called) {
  const positional = [], named = new Map(), names = parameters?.map(parameter => parameter.name);
  const name = (arg, braced) => {
    const name = arg.name.text;
    if (!parameters)
      throw unit.locate(Error(`${called} has no named parameters: a named argument gives a parameter that a definition declares.`), arg.name);
    const index = names.indexOf(name);
    if (index < 0)
      throw unit.locate(Error(`${called} has no parameter ${name}; its parameters are ${names.join(", ")}.`), arg.name);
    if (named.has(index)) throw unit.locate(Error(`The argument ${name} is given twice.`), arg.name);
    if (!!parameters[index].implicit !== braced)
      throw unit.locate(Error(braced ? `${name} is not an implicit parameter of ${called}: give it in parentheses, as ${called}(${name} := …).`
        : `${name} is an implicit parameter of ${called}: give it in double braces, as ${called}{{${name} := …}}(…).`), arg.name);
    named.set(index, arg.value);
  };
  for (const arg of n.args) {
    if (arg.kind === "namedArgument") name(arg, false);
    else positional.push(arg);
  }
  const braced = new Map();
  if (n.implicitArgs) {
    const implicit = parameters?.flatMap((parameter, index) => parameter.implicit ? [index] : []) ?? [];
    if (!implicit.length)
      throw unit.locate(Error(`${called} has no implicit parameters: give its arguments in parentheses, as ${called}(…).`), n.implicitArgs[0]);
    const unnamed = [];
    for (const arg of n.implicitArgs) {
      if (arg.kind === "namedArgument") name(arg, true);
      else unnamed.push(arg);
    }
    const open = implicit.filter(index => !named.has(index));
    if (unnamed.length > open.length)
      throw unit.locate(Error(`${called} has ${implicit.length} implicit parameter${implicit.length === 1 ? "" : "s"}, ${
        implicit.map(index => names[index]).join(", ")}; the double braces give ${n.implicitArgs.length}.`), unnamed[open.length]);
    unnamed.forEach((arg, k) => braced.set(open[k], arg));
  }
  const given = new Map(), count = parameters?.length ?? 0;
  let next = 0;
  for (let index = 0; index < count; index++) {
    if (named.has(index)) given.set(index, named.get(index));
    else if (braced.has(index)) given.set(index, braced.get(index));
    else if (!parameters[index].implicit && next < positional.length) given.set(index, positional[next++]);
  }
  for (let index = count; next < positional.length; index++) given.set(index, positional[next++]);
  const last = Math.max(-1, ...given.keys());
  return index => given.has(index) ? given.get(index) : index < last ? null : undefined;
}

// Elaborate a call of a definition or a function: its written arguments,
// its holes and its named arguments, from the function's type.
export function elaborateCall(t, n, scope, expected) {
  const {env, unit} = scope;
  const headName = n.fn.kind === "name" ? n.fn.name : null;
  const called = headName ?? "This function";
  const bound = headName ? env.get(headName) : undefined;
  if (n.implicitArgs) {
    if (headName && !env.has(headName) || INDUCTIVE_TAGS.has(bound?.tag))
      throw unit.locate(Error(`${headName} has no implicit parameters: give its arguments in parentheses, as ${headName}(…).`), n.fn);
    if (bound?.tag === "Recursive")
      throw unit.locate(Error(`A recursive call of ${headName} passes its implicit parameters unchanged: give only the others, as ${headName}(…).`), n.fn);
  }
  if (determinesArguments(n)) {
    if (headName && !env.has(headName))
      throw unit.locate(Error(`${headName} takes its arguments explicitly: a hole _ or a named argument is an argument of a definition or a function.`), n.fn);
    if (INDUCTIVE_TAGS.has(bound?.tag))
      throw unit.locate(Error(`${headName} is a declared type or a constructor, whose arguments are written out: a hole _ or a named argument is an argument of a definition or a function.`), n.fn);
    if (bound?.tag === "Recursive")
      throw unit.locate(Error(`A recursive call of ${headName} takes its arguments explicitly.`), n.fn);
  }
  const head = t.term(n.fn, scope, null);
  const parameters = sourceParameters(t, head);
  const given = assign(n, parameters, unit, called);
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
      type = scope.nf(solver.zonk(type));
    }
    const parameter = parameters?.[index]?.name ?? null;
    const site = node ?? n.fn;
    // Instantiation at a universe, below UU0 (G0 §2.7); a hole there is a
    // universe to infer, a placeholder level until it is solved.
    if (type.tag === "LPi") {
      if (!node || isHole(node)) {
        const variable = `${parameter ?? "universe"}?${++placeholders}`;
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
    // A name no source or name supply spells, so that a call without holes
    // leaves the declaration's generated names as they were.
    const variable = `${parameter ?? "argument"}?${++placeholders}`;
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
// elaborating it once its parameter's type mentions no unknown.
class ArgumentSolver {
  constructor(t, scope, slots, called, call) {
    Object.assign(this, {t, scope, slots, called, call});
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
      if (below && !this.levelUnknown(larger)) this.bounds.get(below.variable).equal ??= larger;
      else if (above && !this.levelUnknown(smaller)) this.bounds.get(above.variable).equal ??= smaller;
      else return "stuck";
      return "done";
    }
    if (above && !this.levelUnknown(smaller)) this.bounds.get(above.variable).lower.push(smaller);
    else if (below && !this.levelUnknown(larger)) this.bounds.get(below.variable).upper.push(larger);
    else return "stuck";
    return "done";
  }
  // Solve the universe placeholders that bounds determine: by an equality,
  // or as the largest lower bound. With `last`, also those nothing bounds
  // that the call's type does not mention, as U0. True when one was solved.
  solveUniverses(last = false) {
    let solved = false;
    for (const [variable, {lower, equal}] of this.bounds) {
      if (this.solution.has(variable)) continue;
      let level = equal;
      if (level === null && lower.length)
        level = lower.every(bound => typeof bound === "number") ? Math.max(...lower)
          : lower.reduce((left, right) => ({tag: "LMax", left, right}));
      if (level === null && last && !freeNames(this.zonk(this.result ?? T.unit)).has(variable)) level = 0;
      if (level === null) continue;
      const slot = this.byVariable.get(variable);
      if (!finiteLevel(level))
        throw this.scope.unit.locate(Error(`The universe ${slot.parameter ?? "argument"} of ${this.called} would be ${universeText(level)}, which is not below UU0. Give it explicitly.`), slot.node ?? this.call.fn);
      this.solution.set(variable, level);
      solved = true;
    }
    return solved;
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
          try { this.solution.set(slot.variable, this.determined ? this.scope.check(slot.value, domain) : this.scope.infer(slot.value).term); }
          catch (error) { throw this.scope.unit.locate(error, slot.node); }
          progress = true;
        } else if (!slot.tried) {
          // Its type, to solve the holes its parameter's type mentions; the
          // argument itself is elaborated again against that type once the
          // holes are solved.
          slot.tried = true;
          const inferred = this.infer(slot.node);
          if (inferred) { this.require(inferred, domain, {slot}); progress = true; }
        }
      }
      // A hole solved at a type that mentions a placeholder bounds it by the
      // solution's own type, as a written argument's type does.
      for (const slot of this.slots) {
        if (slot.kind === "argument" || slot.universe || slot.typed || !this.solution.has(slot.variable)) continue;
        const domain = this.zonk(slot.domain), value = this.zonk(T.variable(slot.variable));
        if (!this.unknowns(domain).length || this.unknowns(value).length) continue;
        slot.typed = true;
        this.require(this.scope.infer(value).type, domain, {slot});
        progress = true;
      }
      if (progress) continue;
      if (complete && this.approximate()) continue;
      // Universes last: once every argument has said what it needs.
      if (!complete || (!this.solveUniverses() && !this.solveUniverses(true))) break;
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
        if (this.unify(constraint.smaller, constraint.larger, constraint.origin, "covariant", new Set(), this.scope) === "done") {
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
        const outcome = this.unify(constraint.smaller, constraint.larger, constraint.origin, "covariant", new Set(), this.scope);
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
    const {t, scope} = this, quiet = scope.withUnit(scope.unit.with({references: null}));
    const onStep = t.onStep;
    t.onStep = null;
    try { return quiet.infer(t.term(node, quiet, null)).type; }
    catch (error) {
      if (isLimit(error)) throw error;
      return null;
    }
    finally { t.onStep = onStep; }
  }
  // One constraint between two terms: "done", "stuck" (for now) or "clash",
  // when they cannot agree. `polarity` is "covariant" where a larger
  // universe would also do, `bound` the variables and `at` the scope, with
  // its dimensions, that the constraint has descended under.
  unify(left, right, origin, polarity, bound, at, normal = false) {
    left = this.zonk(left); right = this.zonk(right);
    const unknown = [...this.unknowns(left), ...this.unknowns(right)];
    // Only a hole is solved here; an argument's value is waited for.
    if (!unknown.some(name => this.byVariable.get(name).kind !== "argument")) return unknown.length ? "stuck" : "done";
    const hole = this.flexible(left), other = this.flexible(right);
    if (hole && other && hole === other) return "done";
    // A hole on the smaller side is at most the other; on the larger, at least.
    if (hole) return this.solve(hole, right, polarity, bound, at, "upper");
    if (other) return this.solve(other, left, polarity, bound, at, "lower");
    // An argument's variable stands for a value still to be elaborated.
    if (left.tag === "Var" && this.byVariable.has(left.name) || right.tag === "Var" && this.byVariable.has(right.name)) return "stuck";
    if (left.tag === right.tag && rigid(left, right, normal, this.byVariable)) {
      const outcome = this.parts(left, right, origin, polarity, bound, at);
      if (outcome !== "clash" || normal) return outcome;
    }
    // One definition applied on both sides, as T.Hom(A, B) or Tagged(U, A).
    if (!normal && sameDefinitionHead(left, right)) {
      // When nothing else made progress (approximate): its arguments, as
      // they stand. Unless they agree, nothing they solved is kept, and the
      // unfoldings are compared instead.
      if (this.approximating) {
        const saved = this.snapshot(), outcome = this.parts(left, right, origin, "invariant", bound, at);
        if (outcome === "done") return outcome;
        this.restore(saved);
      } else {
        // Otherwise the unfoldings first. Where they agree with a hole in
        // the arguments still open, as Tagged(U, A) := Nat leaves A, the
        // constraint waits: for other constraints to solve the hole, or for
        // approximate() to read it off the arguments.
        const outcome = this.unfolded(left, right, origin, polarity, bound, at);
        const open = [...this.unknowns(this.zonk(left)), ...this.unknowns(this.zonk(right))]
          .some(name => this.byVariable.get(name).kind !== "argument");
        return outcome === "done" && open ? "stuck" : outcome;
      }
    }
    // Different type formers never agree; other heads may, by eta.
    if (normal) return left.tag !== right.tag && CANONICAL.has(left.tag) && CANONICAL.has(right.tag) ? "clash" : "stuck";
    return this.unfolded(left, right, origin, polarity, bound, at);
  }
  // A definition, a redex or a projection: their head normal forms compared.
  unfolded(left, right, origin, polarity, bound, at) {
    let leftHead, rightHead;
    try { leftHead = at.nf(left); rightHead = at.nf(right); }
    catch (error) {
      if (isLimit(error)) throw error;
      return "stuck";
    }
    return this.unify(leftHead, rightHead, origin, polarity, bound, at, true);
  }
  // What the solver has found, to return to after a failed attempt.
  snapshot() {
    return { solution: new Map(this.solution), ambiguous: new Map(this.ambiguous), escaping: new Map(this.escaping),
      clashes: [...this.clashes], bounds: new Map([...this.bounds].map(([variable, bounds]) =>
        [variable, { ...bounds, lower: [...bounds.lower], upper: [...bounds.upper] }])) };
  }
  restore(saved) { Object.assign(this, saved); }
  // The parts of two terms with the same rigid head.
  parts(left, right, origin, polarity, bound, at) {
    const same = (l, r, p = "invariant", b = bound, s = at) => this.unify(l, r, origin, p, b, s);
    const all = outcomes => outcomes.includes("clash") ? "clash" : outcomes.includes("stuck") ? "stuck" : "done";
    // Both binders renamed to one fresh name.
    const under = (l, r, p) => {
      const name = at.fresh(stem(left.name));
      return same(substituteTerm(l.body, l.name, T.variable(name)), substituteTerm(r.body, r.name, T.variable(name)),
        p, new Set(bound).add(name));
    };
    const dimension = (l, r, key, p) => {
      const dim = at.fresh("i"), inner = at.bindDimension(dim);
      return same(substituteDimension(l[key], l.dim, I.variable(dim)), substituteDimension(r[key], r.dim, I.variable(dim)),
        p, new Set(bound).add(dim), inner);
    };
    switch (left.tag) {
      case "Pi": return all([same(left.domain, right.domain), under(left, right, polarity)]);
      case "Sigma": return all([same(left.domain, right.domain, polarity), under(left, right, polarity)]);
      case "Lam": return all([same(left.domain, right.domain), under(left, right)]);
      case "Path": return all([dimension(left, right, "family", polarity), same(left.left, right.left), same(left.right, right.right)]);
      case "PLam": return all([dimension(left, right, "family"), dimension(left, right, "body")]);
      case "PApp": return I.equal(left.arg, right.arg) ? same(left.path, right.path) : "stuck";
      case "App": return all([same(left.fn, right.fn), same(left.arg, right.arg)]);
      case "LApp":
        if (this.levelUnknown(left.level) || this.levelUnknown(right.level))
          return all([this.relateLevels(left.level, right.level, "invariant"), same(left.fn, right.fn)]);
        return JSON.stringify(left.level) === JSON.stringify(right.level) ? same(left.fn, right.fn) : "clash";
      case "Fst": case "Snd": return same(left.pair, right.pair);
      case "Sum": return all([same(left.left, right.left, polarity), same(left.right, right.right, polarity)]);
      case "Sort": {
        if (left.signature !== right.signature || left.parameters.length !== right.parameters.length) return "clash";
        // An instance's recorded universes are its own: equal on both sides.
        const levels = (left.levels ?? []).map((level, index) => right.levels?.[index] === undefined ? "done"
          : this.relateLevels(level, right.levels[index], "invariant"));
        return all([...levels, ...left.parameters.map((parameter, index) => same(parameter, right.parameters[index]))]);
      }
      case "Con": return left.index === right.index ? same(left.sort, right.sort) : "clash";
      case "Elim":
        if (left.signature !== right.signature || left.clauses.length !== right.clauses.length) return "clash";
        return all([same(left.motive, right.motive), ...left.clauses.map((clause, index) => same(clause, right.clauses[index]))]);
      case "Var": case "DefRef": return left.name === right.name ? "done" : "clash";
      case "U":
        if (this.levelUnknown(left.level) || this.levelUnknown(right.level))
          return this.relateLevels(left.level, right.level, polarity);
        return JSON.stringify(left.level) === JSON.stringify(right.level) ? "done" : "stuck";
      case "Unit": case "Void": case "Point": return "done";
      default: return "stuck";
    }
  }
  // A hole's solution, when it is determined.
  solve(slot, value, polarity, bound, at, side) {
    value = this.zonk(value);
    const names = freeNames(value);
    // It would mention itself, or a variable bound inside the constraint.
    if (names.has(slot.variable)) return "stuck";
    const escaping = [...names].find(name => bound.has(name));
    if (escaping) { this.escaping.set(slot.variable, value); return "stuck"; }
    if ([...freeDimensions(value)].some(dim => bound.has(dim) || !this.scope.dimensions.has(dim))) return "stuck";
    // A universe where a larger one would do as well is a bound, not a
    // solution, unless a bound on the other side is the same universe.
    if (polarity === "covariant" && universeAt(value)) {
      const bounds = this.ambiguous.get(slot.variable) ?? {lower: [], upper: []}, key = JSON.stringify(value);
      bounds[side].push(value);
      this.ambiguous.set(slot.variable, bounds);
      if (!bounds[side === "lower" ? "upper" : "lower"].some(other => JSON.stringify(other) === key)) return "stuck";
    }
    this.solution.set(slot.variable, value);
    this.ambiguous.delete(slot.variable);
    return "done";
  }
  // Why a constraint failed, in words.
  mismatch({smaller, larger, origin}) {
    const [found, wanted] = this.t.shownTogether([this.display(this.zonk(smaller)), this.display(this.zonk(larger))]);
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
    if (result.ok) { this.solution.set(slot.variable, result.term); return; }
    if (result.failure !== "mismatch") throw result.error;
    const [shown, typeText] = this.t.shownTogether([value, type]);
    throw this.scope.unit.locate(Error(`The hole for ${this.describe(slot)} of ${this.called} was solved as ${shown}, which does not have its type ${typeText}.`), slot.node ?? this.call.fn);
  }
  undetermined(slot) {
    if (slot.universe)
      return this.scope.unit.locate(Error(`Nothing determines the universe ${slot.parameter ?? "argument"} of ${this.called}: no argument's type bounds it, and the call's type depends on it. Give it explicitly.`), slot.node ?? this.call.fn);
    const type = this.t.shown(this.display(this.zonk(slot.domain)));
    const candidate = this.ambiguous.get(slot.variable), {called} = this, parameter = this.describe(slot);
    const escaping = this.escaping.get(slot.variable);
    const clash = this.clashes.length ? ` (${this.mismatch(this.clashes[0])})` : "";
    const error = slot.kind === "argument"
      ? Error(`The argument ${this.source(slot.node)} of ${called} needs the type of its ${parameter}, ${type}, which mentions a hole nothing determines${clash}. Give the hole explicitly.`)
      : candidate ? Error(`The ${parameter} of ${called} is not determined: ${this.t.shown(candidate.lower[0] ?? candidate.upper[0])} fits, and so would ${candidate.lower.length ? "a larger" : "a smaller"} universe${clash}. Give it explicitly.`)
      : escaping ? Error(`The ${parameter} of ${called} would be ${this.t.shown(this.display(escaping))}, which mentions a variable bound inside an argument, out of its scope${clash}. Give it explicitly.`)
      : Error(`Nothing determines the ${parameter} of ${called}, of type ${type}: not the other arguments' types, nor the type expected of the call${clash}. Give it explicitly.`);
    return this.scope.unit.locate(error, slot.node ?? this.call.fn);
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
    const omitted = [];
    for (const slot of this.slots) {
      if (!slot.variable || slot.kind === "argument") continue;
      // A universe is shown as the universe it is.
      const value = slot.universe ? T.universe(this.solution.get(slot.variable)) : this.zonk(T.variable(slot.variable));
      const shown = slot.universe ? universeText(this.solution.get(slot.variable)) : t.shown(value);
      if (slot.kind === "hole")
        t.reference(scope, {...slot.node, name: "_", expressionSite: true, role: "inferred argument",
          description: `The ${slot.universe ? `universe ${slot.parameter ?? "argument"}` : this.describe(slot)} of ${this.called}, inferred: ${shown}.`}, value);
      else omitted.push(`${slot.parameter} := ${shown}`);
    }
    if (omitted.length && Number.isInteger(n.end))
      t.reference(scope, {name: ")", start: n.end - 1, end: n.end, expressionSite: true, role: "inferred arguments",
        description: `Arguments of ${this.called} inferred: ${omitted.join(", ")}.`}, term);
  }
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
