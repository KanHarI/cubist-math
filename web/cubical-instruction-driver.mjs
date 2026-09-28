// The untrusted driver of the instruction kernel. It replays a term the
// elaborator built as instructions, one per node, and searches for the
// equality steps that make types agree where a rule needs them to:
// congruence on common heads, weak-head steps as the term checker's
// conversion takes them, the kernel's weak head normal form for heads those
// steps do not take, eta, and a normalization when that runs long. Where it
// could do several of these, a chooser picks (heuristicChooser, below); the
// default steers by its own guide, which asks the kernel for weak heads. The
// kernel checks every instruction; a wrong search only fails, it cannot
// prove anything.
import { InstructionGraph } from "./cubical-instructions.mjs";
import { KernelError } from "./cubical-kernel.mjs";
import { freeDimensionMask } from "./cubical-syntax.mjs";
import { levelNormal } from "./cubical-levels.mjs";

const TERM_BINDERS = new Set(["Pi", "Lam", "Sigma", "W", "LPi", "LLam"]);
// Binders of a universe variable x < ω (G0): the level entry is found by its
// symbol, which levels below name.
const LEVEL_BINDERS = new Set(["LPi", "LLam"]);
// Nodes whose payload is an interval or face formula.
const FORMULA_PAYLOADS = new Set(["PApp", "Tube", "GlueSystem", "PushPath"]);
const unsupported = kind => new Error(`${kind} is not in instruction mode yet.`);
// Whether child i of a node is under its dimension binder (the payload).
const dimensionBound = (kind, i) => kind === "PLam" || ((kind === "Path" || kind === "Trans") && i === 0) ||
  (kind === "Comp" && i < 2) || (kind === "HComp" && i === 1);
// Weak heads that only compute by eta, or not at all.
// A declared type's instance, constructor and eliminator are weak heads too
// (H1): a constructor applied computes only under an eliminator.
const CONSTRUCTORS = new Set(["U", "Pi", "Lam", "LPi", "LLam", "Sigma", "Pair", "Nat", "Zero", "Succ", "Unit", "Point", "Void",
  "Sum", "Inl", "Inr", "Path", "PLam", "W", "Sup", "Pushout", "PushLeft", "PushRight", "Sort", "Con", "Elim", "List"]);
// The type former a constructor's eta expansion needs. A Glue term's is
// glue [φ ↦ g] (unglue g), for g of a Glue type.
const etaTypes = { Lam: "Pi", PLam: "Path", Pair: "Sigma", LLam: "LPi", GlueTerm: "Glue" };
// Steps after which a comparison the oracle finds true computes normal forms.
const LONG_COMPUTATION = 64;
// The kernel steps the Glue step may take (the glue move). It normalizes its
// side conditions, and open terms can be large shared graphs, whose normal
// forms are not.
const GLUE_STEPS = 200000;
// The guide (InstructionDriver.guide): how many pairs of subterms one
// question may compare, and the kernel steps each weak head may take.
const GUIDE_FUEL = 400, GUIDE_HEAD_STEPS = 4000;
// A comparison's moves (InstructionDriver.agree), and the kernel steps the
// oracle may take to answer one question.
const FUEL = 20000, ORACLE_STEPS = 20000;
// The search's fixed limits, for reports that must say what they measured.
export const searchLimits = Object.freeze({ fuel: FUEL, longComputation: LONG_COMPUTATION, guideFuel: GUIDE_FUEL,
  guideHeadSteps: GUIDE_HEAD_STEPS, oracleSteps: ORACLE_STEPS, glueSteps: GLUE_STEPS });
// Weak heads that are constructors: two of different kinds never agree.
// An instance of a declared type is one (H1); so is a list of its parameters.
const RIGID = new Set(["U", "Pi", "Sigma", "W", "LPi", "Nat", "Zero", "Succ", "Unit", "Point", "Void", "Sum",
  "Inl", "Inr", "Path", "Sup", "Pushout", "PushLeft", "PushRight", "Lam", "LLam", "PLam", "Pair", "Sort", "List"]);
// Constructors that eta relates to a neutral term of their type.
const ETA_CONSTRUCTORS = new Set(["Lam", "LLam", "PLam", "Pair", "GlueTerm"]);
// Neutral weak heads: variables and eliminations stuck on one. A declared
// type's constructor and eliminator count here, not as rigid heads: each is
// a function, or a path, which eta relates to a lambda. Two constructors of
// different numbers still differ, and so does a constructor from a variable.
const NEUTRAL = new Set(["Var", "App", "LApp", "Fst", "Snd", "NatRec", "SumRec", "UnitRec", "WRec", "PApp", "Abort",
  "Con", "Elim"]);
// The child that is only a constructor's annotation: two equal terms may
// carry different annotations, so a difference there proves nothing.
const ANNOTATION = { Pair: 0, Inl: 0, Inr: 0, Sup: 0, PushLeft: 0, PushRight: 0, Abort: 0, Lam: 0, Con: 0 };
// A scope maps term symbols to entries; under this key, the mask of the
// interval dimensions live in it.
const LIVE = "dims";
const liveIn = scope => scope.get(LIVE) ?? 0n;
const withLive = (scope, dimension) => new Map(scope).set(LIVE, liveIn(scope) | 1n << BigInt(dimension));
// Scopes of several judgements together: their entries, and every live dimension.
const joinScopes = (...scopes) => new Map([...scopes.flatMap(scope => [...scope]),
  [LIVE, scopes.reduce((mask, scope) => mask | liveIn(scope), 0n)]]);
// The children of a dimension binder that it binds.
const underBinder = { Path: [0], PLam: [0, 1], Comp: [0, 1], HComp: [1], Trans: [0] };

// The search's choices (docs/roadmaps/learned-search.md, "The decision
// problem"). `agree` rewrites two focused subterms until they are
// alpha-equal; each time round, it stops at a branch point, lists the moves
// open there, and asks a chooser which to make. A move is a plain object:
//   { move: "normalize" }              both sides to normal form: a long closed
//                                      computation, offered once per comparison
//   { move: "descend" }                congruence: agree part by part under a
//                                      common head, offered once per branch point
//   { move: "step", side, rule, step } a weak-head step on one side ("left" or
//                                      "right") by `rule`: beta, iota, path,
//                                      face or delta, at `step.path`; delta on
//                                      both sides is also side "both", `steps`
//   { move: "whnf", side }             the kernel's weak head normal form
//   { move: "eta" }                    eta-expand the side that is not a
//                                      constructor, against one that is
//   { move: "glue", side }             Glue eta by the kernel's Glue step,
//                                      within GLUE_STEPS: a piece may be the
//                                      base's restriction only once both are
//                                      reduced, which the weak head does not
//                                      do; the last resort, and never inside a
//                                      speculative descent
// The list is syntactic: it offers what the terms' shapes allow, and the
// kernel checks the rest when the move is made. A step always applies. A
// whnf or eta that turns out to change nothing leaves the point as it was.
// A failed normalize or descend may have rewritten the sides, so the point
// is listed again, without them.
//
// A chooser is { name, rank(point), observe?(point, move, outcome, error) }.
// rank yields moves of point.moves, best first; the driver makes each in
// turn until one applies, and the comparison fails when none does. observe
// hears each move's outcome: "agreed", "progress", "stuck" (it changed
// nothing), "changed" (it failed and may have rewritten the sides),
// "deferred" (a comparison inside gave up for an enclosing closed one to
// normalize) or "error" (it threw `error`, such as the kernel running out of
// budget or time, which ends the comparison).
// A point is { driver, a, b, x, y, nx, ny, terms, dims, moves, round, taken,
// depth }: the foci, their subterms and nodes when the point was reached,
// the bound names that correspond, the moves, the listing's number at this
// point, the steps taken by the whole comparison so far, and how many
// comparisons enclose this one (descending compares parts, one inside the
// other). Choosers are untrusted,
// like the driver: a bad choice only fails, and the kernel checks each move.
//
// The heuristic is the driver's own order, lazily, since its tests ask the
// guide: normalize a long closed computation unless the guide finds the
// sides different; descend when no parts are known to differ; computation
// steps before unfolding, left before right; unfold the later definition,
// or both when it is the same (lazy delta reduction); then weak head normal
// forms, left then right; then eta.
export const heuristicChooser = Object.freeze({
  name: "heuristic",
  *rank(point) {
    const { driver, moves } = point, find = (move, side) => moves.find(m => m.move === move && (!side || m.side === side));
    const normalize = find("normalize");
    if (normalize && driver.equal(point.x, point.y, point.terms, point.dims) !== false) yield normalize;
    const descend = find("descend");
    if (descend && driver.partsEqual(point.nx, point.ny, point.terms, point.dims)) yield descend;
    const left = find("step", "left"), right = find("step", "right");
    if (left && left.rule !== "delta") return yield left;
    if (right && right.rule !== "delta") return yield right;
    if (left && right) {
      const order = driver.definitionAt(left.term, left.step) - driver.definitionAt(right.term, right.step);
      return yield order > 0 ? left : order < 0 ? right : find("step", "both");
    }
    if (left || right) return yield left ?? right;
    for (const move of moves) if (move.move === "whnf" || move.move === "eta") yield move;
    for (const move of moves) if (move.move === "glue") yield move;
  },
});

export class InstructionDriver {
  constructor(kernel, { graph = new InstructionGraph(kernel), fuel = FUEL, guideSteps = ORACLE_STEPS,
                        oracle = kernel.conversionOracle ?? false, chooser = kernel.chooser ?? heuristicChooser } = {}) {
    this.kernel = kernel;
    this.graph = graph;
    this.fuel = fuel;
    this.guideSteps = guideSteps;
    // Whether the term checker's conversion guides the search instead of the
    // driver's own guide (guide, below).
    this.oracle = oracle;
    // Who picks the moves of `agree` (heuristicChooser, above), and how many
    // comparisons are open, one inside another.
    this.chooser = chooser;
    this.depth = 0;
    this.nodes = new Map();
    // Judgements never change, so reads are cached; so are the scopes of
    // contexts, derivations by term and scope, and terms known to be in weak
    // head normal form.
    this.statements = new Map();
    this.scopes = new Map();
    this.scopeKeys = new WeakMap();
    this.mentions = new Map();
    this.derived = new Map();
    this.stable = new Set();
    // Glue terms the glue move need not try again: no Glue eta redex, even
    // with its side conditions normalized, or one whose side conditions take
    // more than the move's budget.
    this.glueStuck = new Set();
    this.equalities = new Map();
    // The guide's answers and the weak heads it asked for.
    this.guesses = new Map();
    this.heads = new Map();
    this.alphaMemo = new Map();
    this.contextScopes = new Map();
    this.chainIds = new WeakMap();
    this.chainNumbers = new Map();
    this.freeDims = new Map();
    this.pruned = new Map();
  }

  // The judgement `expression : type` for a checked term and its type, in a
  // context of [symbol, type] assumptions, each over the ones before it.
  // `dimensions` is the mask of the interval dimensions the terms may use.
  check(expression, type, context = [], dimensions = 0n) {
    const scope = this.contextScope(context, dimensions);
    return this.convertTo(this.derive(expression, scope), this.asType(this.derive(type, scope)));
  }
  // The judgement for a term alone, at the type its derivation gives it.
  infer(expression, context = [], dimensions = 0n) {
    return this.derive(expression, this.contextScope(context, dimensions));
  }
  // A context's scope: each assumption bound at its type, derived in order;
  // the same context gives the same scope.
  contextScope(context, dimensions) {
    const key = `${dimensions}|${context.map(([symbol, type]) => `${symbol}:${type}`).join(",")}`;
    if (!this.contextScopes.has(key)) {
      // A new scope for each assumption: a scope is a memo key for the
      // derivations made in it (scopeKey), so it never changes once used.
      let scope = new Map([[LIVE, dimensions]]);
      for (const [symbol, assumption] of context)
        // A universe variable (G0) is a level entry, typed by its bound.
        scope = new Map(scope).set(symbol, this.node(assumption).kind === "LBound" ? this.graph.levelEntry(symbol)
          : this.bind(symbol, this.asType(this.derive(assumption, scope))));
      this.contextScopes.set(key, scope);
    }
    return this.contextScopes.get(key);
  }

  node(handle) {
    if (!this.nodes.has(handle)) this.nodes.set(handle, this.kernel.node(handle));
    return this.nodes.get(handle);
  }
  statement(id) {
    if (!this.statements.has(id)) this.statements.set(id, this.graph.judgement(id));
    return this.statements.get(id);
  }
  sideOf(id, side) {
    const j = this.statement(id);
    return side === "term" ? j.term : side === "other" ? j.other : j.type;
  }
  subterm(focus) {
    let term = this.sideOf(focus.ref.id, focus.side);
    for (const child of focus.path) term = this.node(term).children[child];
    return term;
  }
  focus(id, side, path = []) { return { ref: { id }, side, path }; }
  child(focus, index) { return { ref: focus.ref, side: focus.side, path: [...focus.path, index] }; }
  reduce(focus, step) {
    focus.ref.id = this.graph.step(focus.ref.id, focus.side, [...focus.path, ...step.path], step.rule);
  }

  // The variables of a judgement's context, by symbol, for deriving its terms.
  scope(id) {
    const context = this.statement(id).context, key = context.join(",");
    if (!this.scopes.has(key)) {
      const scope = new Map();
      let live = 0n;
      for (const entry of context) {
        const info = this.graph.entry(entry);
        if (info.dimension) live |= 1n << BigInt(info.symbol);
        else scope.set(info.symbol, entry);
      }
      this.scopes.set(key, scope.set(LIVE, live));
    }
    return this.scopes.get(key);
  }
  // Whether the type of a variable in scope mentions a dimension.
  typesMention(scope, dimension) {
    const key = `${this.scopeKey(scope)}|${dimension}`;
    if (!this.mentions.has(key))
      this.mentions.set(key, [...scope].some(([symbol, entry]) => symbol !== LIVE && this.graph.entry(entry).source &&
        this.statement(this.graph.entry(entry).source).context.some(other => {
          const info = this.graph.entry(other);
          return info.dimension && info.symbol === dimension;
        })));
    return this.mentions.get(key);
  }
  scopeKey(scope) {
    if (!this.scopeKeys.has(scope)) this.scopeKeys.set(scope, [...scope].map(([symbol, entry]) => `${symbol}:${entry}`).sort().join(","));
    return this.scopeKeys.get(scope);
  }
  // A binder name no term uses: numbered per kernel, as fresh entries are.
  freshSymbol(stem) {
    const counters = this.kernel.freshNames ??= new Map(), suffix = (counters.get(stem) ?? 0) + 1;
    counters.set(stem, suffix);
    return this.kernel.symbol(this.variant(stem, suffix));
  }
  // A name made up for a binder, remembered with its stem, so that displays
  // can show the stem again where nothing can tell the two apart.
  variant(stem, suffix) {
    const name = `${stem}'${suffix}`;
    (this.kernel.variantStems ??= new Map()).set(name, stem);
    return name;
  }
  // An interval index no judgement among `ids` has in its context, so none of
  // their terms uses it.
  freeDimension(ids) {
    const used = new Set();
    for (const id of ids)
      for (const entry of this.statement(id).context) {
        const info = this.graph.entry(entry);
        if (info.dimension) used.add(info.symbol);
      }
    let dimension = 0;
    while (used.has(dimension)) dimension++;
    return dimension;
  }
  // A context entry for a binder: its own name unless another entry of a
  // different type has it, then a fresh variant. Fresh names are numbered
  // per kernel, so finding one never searches.
  bind(symbol, type) { return this.entry(type, this.kernel.symbolName(symbol), false); }
  freshEntry(type, stem) { return this.entry(type, stem, true); }
  //
  // A binder's variant is remembered by its name and type, and used again the
  // next time the same name is bound at the same type: two variants of one
  // variable would make terms that mention it differ for ever.
  entry(type, stem, fresh) {
    const variants = this.kernel.variantNames ??= new Map();
    const key = fresh ? null : `${stem}\u0000${this.statement(type).term}`;
    if (!fresh) {
      try { return this.graph.extend(type, stem); }
      catch (error) { if (!/already names/.test(error.message)) throw error; }
      if (variants.has(key)) {
        try { return this.graph.extend(type, variants.get(key)); }
        catch (error) { if (!/already names/.test(error.message)) throw error; variants.delete(key); }
      }
    }
    const counters = this.kernel.freshNames ??= new Map();
    for (let suffix = (counters.get(stem) ?? 0) + 1; ; suffix++) {
      try {
        const name = `${stem}'${suffix}`, entry = this.graph.extend(type, name);
        counters.set(stem, suffix);
        this.variant(stem, suffix);
        if (key) variants.set(key, name);
        return entry;
      } catch (error) { if (!/already names/.test(error.message)) throw error; }
    }
  }

  // A term derived once per scope: the kernel shares repeated instructions,
  // and this skips walking the term again.
  derive(handle, scope) {
    const key = `${this.scopeKey(scope)}|${handle}`;
    if (!this.derived.has(key)) this.derived.set(key, this.deriveNode(handle, scope));
    return this.derived.get(key);
  }

  deriveNode(handle, scope) {
    const g = this.graph, n = this.node(handle), [a, b, c, d] = n.children;
    // A dimension binder whose index is live outside it is renamed first,
    // when its parts could not tell the two apart: a composition's faces are
    // outside it, and a variable's type may mention the outer one. Otherwise
    // it keeps its index, so that the derived term is the source's.
    if (underBinder[n.kind] && liveIn(scope) & 1n << BigInt(n.payload) &&
        (!["Path", "PLam"].includes(n.kind) || this.typesMention(scope, n.payload)))
      return this.derive(this.renameBinder(n, liveIn(scope)), scope);
    const bound = underBinder[n.kind] ? withLive(scope, n.payload) : scope;
    const derive = (child, inner = scope) => this.derive(child, inner);
    const within = child => this.derive(child, bound);
    switch (n.kind) {
    case "U": return g.universe(n.children[0]);
    case "Nat": return g.nat();
    case "Zero": return g.zero();
    case "Unit": return g.unit();
    case "Point": return g.point();
    case "Void": return g.void();
    case "DefRef": return g.lookup(handle);
    case "Var": {
      if (!scope.has(n.payload)) throw new Error(`Unbound variable ${this.kernel.symbolName(n.payload)}.`);
      return g.variable(scope.get(n.payload));
    }
    case "Succ": return g.succ(this.convertTo(derive(a), g.nat()));
    case "LPi": case "LLam": {
      const entry = g.levelEntry(n.payload), inner = new Map(scope).set(n.payload, entry);
      const body = derive(b, inner);
      return n.kind === "LPi" ? g.levelPi(entry, this.asType(body)) : g.levelLambda(entry, body);
    }
    case "LApp": return g.levelApply(this.shape(this.focus(derive(a), "type"), "LPi"), b);
    case "Pi": case "Sigma": case "W": case "Lam": {
      const entry = this.bind(n.payload, this.asType(derive(a)));
      const inner = new Map(scope).set(n.payload, entry);
      if (n.kind === "Lam") return g.lambda(entry, derive(b, inner));
      const body = this.asType(derive(b, inner));
      return n.kind === "Pi" ? g.pi(entry, body) : n.kind === "Sigma" ? g.sigma(entry, body) : g.w(entry, body);
    }
    case "Sup": {
      // sup(l, c) : T, with c : Π(i : B[l/x]). T.
      const [type, back] = this.former(this.asType(derive(a)), "W");
      const label = this.convertTo(derive(b), g.domain(type));
      const index = this.freshEntry(g.family(type, label), "i");
      return this.restore(g.sup(type, label, this.convertTo(derive(c), g.pi(index, type))), back);
    }
    case "WRec": {
      // The step at Π(l : L). Π(c : Π(i : B[l]). W). Π(h : Π(i : B[l]).
      // M(c(i))). M(sup(l, c)), built by instructions.
      const value = this.shape(this.focus(derive(c), "type"), "W");
      const type = this.evidence(this.focus(value, "type"));
      const motive = this.motive(derive(a), type);
      const label = this.freshEntry(g.domain(type), "l"), lv = g.variable(label);
      const arity = g.family(type, lv), index = this.freshEntry(arity, "i");
      const children = this.freshEntry(g.pi(index, type), "c"), cv = g.variable(children);
      const hypothesis = this.freshEntry(g.pi(index, g.apply(motive, g.apply(cv, g.variable(index)))), "h");
      const step = g.pi(label, g.pi(children, g.pi(hypothesis, g.apply(motive, g.sup(type, lv, cv)))));
      return g.wElim(motive, this.convertTo(derive(b), step), value);
    }
    case "App": {
      // The argument's type and the function's domain agree in place, both
      // rewritten toward a common form; a domain derived again is the
      // fallback, for cumulativity.
      const fn = this.focus(this.shape(this.focus(derive(a), "type"), "Pi"), "type");
      const argument = this.focus(derive(b), "type");
      if (this.agree(this.child(fn, 0), argument)) return g.apply(fn.ref.id, argument.ref.id);
      return g.apply(fn.ref.id, this.convertTo(argument.ref.id, this.evidence(this.child(fn, 0))));
    }
    case "Pair": {
      const [type, back] = this.former(this.asType(derive(a)), "Sigma");
      const first = this.convertTo(derive(b), g.domain(type));
      return this.restore(g.pair(type, first, this.convertTo(derive(c), g.family(type, first))), back);
    }
    case "Fst": case "Snd": {
      const pair = this.shape(this.focus(derive(a), "type"), "Sigma");
      return n.kind === "Fst" ? g.first(pair) : g.second(pair);
    }
    case "Abort": return g.abort(this.asType(derive(a)), this.convertTo(derive(b), g.void()));
    case "Sum": return g.sum(this.asType(derive(a)), this.asType(derive(b)));
    case "Inl": case "Inr": {
      const [type, back] = this.former(this.asType(derive(a)), "Sum");
      const summand = this.evidence(this.focus(type, "term", [n.kind === "Inl" ? 0 : 1]));
      return this.restore(g.inject(type, this.convertTo(derive(b), summand), n.kind === "Inr"), back);
    }
    case "NatRec": {
      const value = this.convertTo(derive(d), g.nat());
      const motive = this.motive(derive(a), g.nat());
      const zero = this.convertTo(derive(b), g.apply(motive, g.zero()));
      const predecessor = this.freshEntry(g.nat(), "n"), pv = g.variable(predecessor);
      const hypothesis = this.freshEntry(g.apply(motive, pv), "ih");
      const stepType = g.pi(predecessor, g.pi(hypothesis, g.apply(motive, g.succ(pv))));
      return g.natElim(motive, zero, this.convertTo(derive(c), stepType), value);
    }
    case "UnitRec": {
      const motive = this.motive(derive(a), g.unit());
      return g.unitElim(motive, this.convertTo(derive(b), g.apply(motive, g.point())), this.convertTo(derive(c), g.unit()));
    }
    case "SumRec": {
      const value = this.shape(this.focus(derive(d), "type"), "Sum");
      const sum = this.evidence(this.focus(value, "type"));
      const motive = this.motive(derive(a), sum);
      const branches = [b, c].map((branch, right) => {
        const entry = this.freshEntry(this.evidence(this.focus(value, "type", [right])), "x");
        const injected = g.inject(sum, g.variable(entry), right === 1);
        return this.convertTo(derive(branch), g.pi(entry, g.apply(motive, injected)));
      });
      return g.sumElim(motive, branches[0], branches[1], value);
    }
    case "Path": {
      const dimension = g.dimension(n.payload), family = this.asType(within(a));
      return g.path(dimension, family, this.convertTo(derive(b), g.endpoint(family, dimension, 0)),
        this.convertTo(derive(c), g.endpoint(family, dimension, 1)));
    }
    case "PLam": {
      // At its own family, so that the derived term is the source's: the
      // kernel annotates a path lambda with its body's type.
      const dimension = g.dimension(n.payload), body = within(b);
      return g.pathLambda(dimension, a ? this.convertTo(body, this.asType(within(a))) : body);
    }
    case "PApp": {
      const path = this.shape(this.focus(derive(a), "type"), "Path");
      const point = this.point(n.payload);
      if (point.dimension !== undefined) return g.pathApply(path, g.dimension(point.dimension), 0);
      if (point.endpoint !== undefined) return g.pathApply(path, 0, point.endpoint);
      return g.pathAt(path, n.payload);
    }
    case "Comp": case "HComp": {
      // comp^i A [φ ↦ u] a0: each tube, already restricted to its face, is
      // checked against the family there, and shown equal to the base at 0.
      // hcomp is the same box, over a type that does not vary along i.
      const dimension = g.dimension(n.payload);
      const family = this.asType(n.kind === "HComp" ? derive(a) : within(a));
      const base = this.convertTo(derive(c), g.endpoint(family, dimension, 0));
      // Where a tube's face meets an earlier tube's, the two agree there.
      let system = g.system(dimension, family, base);
      const tubes = [];
      for (const { face, term, clause } of this.clauses(b, 1)) {
        if (!clause) {
          // The face 0, as a substitution can leave it: the tube is never used.
          system = g.systemTube(system, face, within(term), 0);
          tubes.push(null);
          continue;
        }
        const restricted = this.restrict(family, clause);
        const value = this.convertTo(within(term), restricted);
        const start = this.focus(g.refl(g.endpoint(value, dimension, 0)), "other");
        const end = this.focus(g.refl(this.restrict(base, clause)), "other");
        if (!this.agree(start, end)) throw new Error("Composition tube disagrees with its base.");
        const adjacency = g.transitivity(start.ref.id, g.symmetry(end.ref.id));
        system = g.systemTube(system, face, value, adjacency);
        tubes.forEach((earlier, position) => {
          const overlap = earlier && [clause[0] | earlier.clause[0], clause[1] | earlier.clause[1]];
          if (!overlap || overlap[0] & overlap[1]) return;
          system = g.systemOverlap(system, position, this.overlapAgreement(value, earlier.value, overlap));
        });
        tubes.push({ clause, value });
      }
      return n.kind === "HComp" ? g.hcomp(system) : g.comp(system);
    }
    case "Trans": {
      // transp^i A φ a0: on each clause of φ, the base itself is a tube, at
      // the family there, which is constant.
      const dimension = g.dimension(n.payload), family = this.asType(within(a));
      const base = this.convertTo(derive(c), g.endpoint(family, dimension, 0));
      const face = this.node(b).payload, { clauses } = this.kernel.inspectFormula(face);
      let system = g.system(dimension, family, base);
      clauses.forEach((clause, index) => {
        const value = this.convertTo(this.restrict(base, clause), this.restrict(family, clause));
        system = g.systemTube(system, this.kernel.formula("face", [clause]), value, g.refl(this.restrict(base, clause)));
        for (let earlier = 0; earlier < index; earlier++) {
          const other = clauses[earlier], overlap = [clause[0] | other[0], clause[1] | other[1]];
          if (overlap[0] & overlap[1]) continue;
          system = g.systemOverlap(system, earlier, g.refl(this.restrict(base, overlap)));
        }
      });
      return g.trans(system, face);
    }
    case "Glue": {
      // Glue [φ ↦ (T, e)] A: each piece's equivalence at the type the kernel
      // states, Equiv(T, A on the face), and where two faces meet, the types
      // and the equivalences agree.
      const base = this.asType(derive(a));
      let system = g.glueBase(base);
      const pieces = [];
      for (const { face, term: [T, e], clause } of this.clauses(b, 2, true)) {
        if (!clause) {
          system = g.gluePiece(system, face, this.asType(derive(T)), derive(e));
          pieces.push(null);
          continue;
        }
        const type = this.asType(derive(T)), target = this.restrict(base, clause);
        const equivalenceType = this.graph.equivType(this.statement(type).term, this.statement(target).term);
        const equivalence = this.convertTo(derive(e),
          this.asType(this.derive(equivalenceType, joinScopes(this.scope(type), this.scope(target)))));
        system = g.gluePiece(system, face, type, equivalence);
        pieces.forEach((earlier, position) => {
          const overlap = earlier && [clause[0] | earlier.clause[0], clause[1] | earlier.clause[1]];
          if (!overlap || overlap[0] & overlap[1]) return;
          system = g.glueOverlap(system, position, this.overlapAgreement(type, earlier.type, overlap),
            this.overlapAgreement(equivalence, earlier.equivalence, overlap));
        });
        pieces.push({ clause, type, equivalence });
      }
      return g.glue(system);
    }
    case "GlueTerm": {
      // glue(a, [φ ↦ t]) : G: a value for each piece of G, in order, whose
      // image under the piece's equivalence is the base on its face.
      const annotation = this.asType(derive(a)), k = this.kernel;
      const base = this.convertTo(derive(b), this.evidence(this.focus(annotation, "term", [0])));
      let system = g.glueTermBase(annotation, base);
      const values = [];
      let path = [1];
      for (const { term: t, clause } of this.clauses(c, 1)) {
        const here = path;
        path = [...path, 2];
        if (!clause) {
          system = g.glueTermPiece(system, derive(t), 0);
          values.push(null);
          continue;
        }
        const value = this.convertTo(derive(t), this.evidence(this.focus(annotation, "term", [...here, 0])));
        const equivalence = this.subterm(this.focus(annotation, "term", [...here, 1]));
        const image = this.derive(k.term("App", 0, k.term("Fst", 0, equivalence), this.statement(value).term),
          joinScopes(this.scope(annotation), this.scope(value)));
        const start = this.focus(g.refl(image), "other"), end = this.focus(g.refl(this.restrict(base, clause)), "other");
        if (!this.agree(start, end)) throw new Error("A Glue value's image disagrees with the base.");
        system = g.glueTermPiece(system, value, g.transitivity(start.ref.id, g.symmetry(end.ref.id)));
        values.forEach((earlier, position) => {
          const overlap = earlier && [clause[0] | earlier.clause[0], clause[1] | earlier.clause[1]];
          if (!overlap || overlap[0] & overlap[1]) return;
          system = g.systemOverlap(system, position, this.overlapAgreement(value, earlier.value, overlap));
        });
        values.push({ clause, value });
      }
      return g.glueTerm(system);
    }
    case "Unglue": return g.unglue(this.convertTo(derive(b), this.asType(derive(a))));
    case "Pushout": {
      // The maps are a pair C → A, C → B, derived as that type's syntax.
      const [source, left, right] = [a, b, c].map(child => this.asType(derive(child)));
      const x = this.freshSymbol("x"), f = this.freshSymbol("f"), k = this.kernel;
      const span = k.term("Sigma", f, k.term("Pi", x, a, b), k.term("Pi", x, a, c));
      return g.pushout(source, left, right, this.convertTo(derive(d), this.asType(derive(span))));
    }
    case "PushLeft": case "PushRight": case "PushPath": {
      const [type, back] = this.former(this.asType(derive(a)), "Pushout");
      const slot = { PushPath: 0, PushLeft: 1, PushRight: 2 }[n.kind];
      const value = this.convertTo(derive(b), this.evidence(this.focus(type, "term", [slot])));
      return this.restore(n.kind === "PushPath" ? g.pushPath(type, value, n.payload)
        : g.pushPoint(type, value, n.kind === "PushRight"), back);
    }
    case "PushElim": {
      // A motive over a pushout type P = Pushout(C, A, B, (f, g)), and each
      // case at the type the kernel asks for, derived from its syntax.
      const motive = this.focus(this.shape(this.focus(derive(a), "type"), "Pi"), "type");
      this.shape(this.child(motive, 0), "Pushout");
      this.shape(this.child(motive, 1), "U");
      const k = this.kernel, M = this.statement(motive.ref.id).term, P = this.subterm(this.child(motive, 0));
      const [C, A, B, maps] = this.node(P).children;
      const point = (kind, domain, stem) => {
        const x = this.freshSymbol(stem);
        return k.term("Pi", x, domain, k.term("App", 0, M, k.term(kind, 0, P, k.term("Var", x))));
      };
      // Built from judgements, the syntax names their entries: derive it in
      // their scope, not the source's.
      const own = this.scope(motive.ref.id);
      const left = this.convertTo(derive(b), this.asType(derive(point("PushLeft", A, "a"), own)));
      const right = this.convertTo(derive(c), this.asType(derive(point("PushRight", B, "b"), own)));
      const [l, r] = [left, right].map(id => this.statement(id).term);
      const joint = joinScopes(own, this.scope(left), this.scope(right));
      const dimension = this.freeDimension([motive.ref.id, left, right]), x = this.freshSymbol("c");
      const at = k.formula("interval", [[1n << BigInt(dimension), 0n]]), cv = k.term("Var", x);
      const bridge = k.term("Pi", x, C, k.term("Path", dimension, k.term("App", 0, M, k.term("PushPath", at, P, cv)),
        k.term("App", 0, l, k.term("App", 0, k.term("Fst", 0, maps), cv)),
        k.term("App", 0, r, k.term("App", 0, k.term("Snd", 0, maps), cv))));
      return g.pushElim(motive.ref.id, left, right, this.convertTo(derive(d), this.asType(derive(bridge, joint))));
    }
    // Declared types (H1; the specification's section 6.1).
    case "Sort": return this.instance(n, scope);
    case "Con": {
      // Constructor k of an instance, at the type the kernel gives it.
      const instance = this.asType(derive(a));
      if (this.node(this.statement(instance).term).kind !== "Sort") throw new Error("A constructor names an instance of a declared type.");
      return g.construct(instance, n.payload);
    }
    case "Elim": {
      let eliminator = this.openEliminator(derive(a), n.payload);
      for (let clause = b; clause; clause = this.node(clause).children[1])
        eliminator = this.addClause(eliminator, derive(this.node(clause).children[0]));
      return g.eliminatorClose(eliminator);
    }
    default: throw unsupported(n.kind);
    }
  }

  // An eliminator in progress from a motive Π (z : S(as)). U(l), its type
  // reduced to that shape; with `index`, over that signature only. Its
  // judgement's type is the next clause's type, ClauseType_k.
  openEliminator(motiveJudgement, index = null) {
    const motive = this.focus(this.shape(this.focus(motiveJudgement, "type"), "Pi"), "type");
    this.shape(this.child(motive, 0), "Sort");
    this.shape(this.child(motive, 1), "U");
    if (index !== null && this.node(this.subterm(this.child(motive, 0))).payload !== index)
      throw new Error("The eliminator's motive is over another declared type.");
    return this.graph.eliminator(motive.ref.id);
  }
  // The next clause, converted to the type the kernel computes for it.
  addClause(eliminator, clause) {
    return this.graph.eliminatorClause(eliminator, this.convertTo(clause, this.evidence(this.focus(eliminator, "type"))));
  }
  // An admitted signature as the kernel records it, read once per driver.
  signatureInfo(index) {
    const infos = this.signatureInfos ??= new Map();
    if (!infos.has(index)) infos.set(index, this.kernel.signature(index));
    return infos.get(index);
  }
  // The former Π (xs < ω). Π (ps : Ps). U(ℓ) of a signature, read as its
  // level symbols and its parameters' types, each over the earlier ones.
  telescope(info) {
    let term = info.former;
    const levels = [], types = [];
    for (let j = 0; j < info.levels; j++, term = this.node(term).children[1]) {
      if (this.node(term).kind !== "LPi") throw new Error("A signature's former binds its universe parameters first.");
      levels.push(this.node(term).payload);
    }
    for (let i = 0; i < info.parameters; i++, term = this.node(term).children[1]) {
      if (this.node(term).kind !== "Pi") throw new Error("A signature's former binds its parameters after its levels.");
      types.push(this.node(term).children[0]);
    }
    return { levels, types };
  }
  // A signature's former with its level binders renamed to fresh symbols:
  // they are the admission's symbols, which a caller's variables may share,
  // and a level entry cannot take a symbol that names a term entry.
  freshFormer(index, info) {
    const formers = this.formers ??= new Map();
    if (!formers.has(index)) {
      const rebuild = term => {
        const n = this.node(term);
        if (n.kind !== "LPi") return term;
        // A symbol the kernel allocates now, with no name: no entry has it.
        const fresh = this.kernel.module._cb_fresh_symbol(this.kernel.handle) >>> 0;
        if (!fresh) throw new Error("Could not allocate a symbol.");
        return this.kernel.term("LPi", fresh, n.children[0], rebuild(this.graph.rename(n.children[1], false, n.payload, fresh)));
      };
      formers.set(index, rebuild(info.former));
    }
    return formers.get(index);
  }
  // S{ls}(as): an instance of an admitted signature (the specification's
  // sections 3.1 and 6.1). The kernel checks each parameter's type against
  // the telescope's, with the levels and the earlier parameters substituted,
  // up to bound names: so each parameter is converted to exactly that type.
  // The types come from applying an entry of the former's type to the
  // levels and the parameters, as an application would.
  //
  // A recorded level is given. An erased one is read from the parameters
  // whose telescope type ends in U(x), each reduced to that shape first; the
  // largest reading is used, and the lower parameters are lifted to it, as
  // the kernel asks.
  instance(n, scope) {
    const g = this.graph, info = this.signatureInfo(n.payload), { levels: symbols, types } = this.telescope(info);
    const list = cell => cell ? [this.node(cell).children[0], ...list(this.node(cell).children[1])] : [];
    const given = list(n.children[1]), parameters = list(n.children[0]);
    if (parameters.length !== info.parameters) throw new Error("An instance takes each of its signature's parameters.");
    const derived = parameters.map(parameter => this.derive(parameter, scope));
    // The Π binders a telescope type has before its end, and that end.
    const shapeOf = type => {
      let depth = 0;
      for (; this.node(type).kind === "Pi"; depth++) type = this.node(type).children[1];
      return { depth, end: this.node(type) };
    };
    let recorded = 0;
    for (let j = 0; j < info.levels; j++) recorded += info.recorded >> j & 1;
    if (given.length !== recorded) throw new Error("An instance gives each recorded universe parameter its level, and no other.");
    const levels = [];
    for (let j = 0, r = 0; j < info.levels; j++) {
      if (info.recorded >> j & 1) {
        levels.push(given[r++]);
        continue;
      }
      let read = 0;
      types.forEach((type, i) => {
        const { depth, end } = shapeOf(type);
        if (end.kind !== "U" || this.node(end.children[0]).kind !== "Var" || this.node(end.children[0]).payload !== symbols[j]) return;
        let focus = this.focus(derived[i], "type");
        for (let d = 0; d < depth; d++) { this.shape(focus, "Pi"); focus = this.child(focus, 1); }
        this.shape(focus, "U");
        derived[i] = focus.ref.id;
        const level = this.node(this.subterm(focus)).children[0];
        read = read ? this.kernel.term("LMax", 0, read, level) : level;
      });
      if (!read) throw new Error("An erased universe parameter has no parameter to read it from.");
      levels.push(read);
    }
    let fn = g.variable(this.freshEntry(this.asType(this.derive(this.freshFormer(n.payload, info), new Map([[LIVE, 0n]]))), "S"));
    for (const level of levels) fn = g.levelApply(this.shape(this.focus(fn, "type"), "LPi"), level);
    let instance = g.sortBegin(n.payload);
    for (const level of given) instance = g.sortLevel(instance, level);
    derived.forEach(parameter => {
      const type = this.focus(this.shape(this.focus(fn, "type"), "Pi"), "type");
      const converted = this.convertTo(parameter, this.evidence(this.child(type, 0)));
      instance = g.sortParameter(instance, converted);
      fn = g.apply(type.ref.id, converted);
    });
    return instance;
  }

  // Two typing judgements agree where two faces meet: an equality between
  // their terms, both restricted to the overlap.
  overlapAgreement(mine, theirs, overlap) {
    const g = this.graph;
    const x = this.focus(g.refl(this.restrict(mine, overlap)), "other");
    const y = this.focus(g.refl(this.restrict(theirs, overlap)), "other");
    if (!this.agree(x, y)) throw new Error("Two pieces disagree where their faces meet.");
    return g.transitivity(x.ref.id, g.symmetry(y.ref.id));
  }

  // A system's parts, one per clause of each face, in order, each restricted
  // to its clause, as the term checker splits and restricts them. A part on a
  // single clause keeps its face, and one already restricted is unchanged.
  // `next` is the child chaining the parts; with `pair`, a part is its first
  // two children (a Glue piece's type and equivalence), otherwise its first.
  *clauses(chain, next, pair = false) {
    for (let part = chain; part; part = this.node(part).children[next]) {
      const { payload: face, children } = this.node(part);
      const term = pair ? [children[0], children[1]] : children[0];
      const { clauses } = this.kernel.inspectFormula(face);
      if (!clauses.length) { yield { face, term, clause: null }; continue; }
      for (const clause of clauses) {
        const restrict = handle => this.restrictSyntax(handle, clause);
        yield { face: clauses.length === 1 ? face : this.kernel.formula("face", [clause]),
          term: pair ? term.map(restrict) : restrict(term), clause };
      }
    }
  }
  // Raw syntax with a clause's endpoints substituted for its dimensions.
  restrictSyntax(handle, [positive, negative]) {
    for (let dim = 0n; (positive | negative) >> dim; dim++) {
      const bit = 1n << dim;
      if ((positive | negative) & bit) handle = this.graph.endpointTerm(handle, Number(dim), positive & bit ? 1 : 0);
    }
    return handle;
  }
  // A dimension binder moved to an index not live around it. A composition's
  // faces are in the outer cube: only its tubes' bodies are renamed.
  renameBinder(n, live) {
    let fresh = 0;
    while (live & 1n << BigInt(fresh)) fresh++;
    if (fresh >= 64) throw new Error("No interval dimension is free for a binder.");
    const rename = handle => this.graph.rename(handle, true, n.payload, fresh);
    const tubes = chain => {
      if (!chain) return 0;
      const tube = this.node(chain);
      return this.kernel.term("Tube", tube.payload, rename(tube.children[0]), tubes(tube.children[1]));
    };
    const children = n.children.map((child, index) => !child || !underBinder[n.kind].includes(index) ? child
      : (n.kind === "Comp" || n.kind === "HComp") && index === 1 ? tubes(child) : rename(child));
    return this.kernel.term(n.kind, fresh, ...children);
  }

  // A constructor's annotation as a type former of the given kind: the
  // annotation itself, or its reduct with the equality back to it, so the
  // constructed term can be given the annotation again, in its term (the
  // annotation is its first operand) and as its type. A derived term must be
  // the syntax it was derived from, or a type derived as evidence would not
  // be the type it stands for.
  former(annotation, kind) {
    if (this.node(this.statement(annotation).term).kind === kind) return [annotation, null];
    const reduct = this.focus(this.graph.refl(annotation), "other");
    this.shape(reduct, kind);
    return [this.graph.side(reduct.ref.id, "other"), this.graph.symmetry(reduct.ref.id)];
  }
  restore(judgement, back) {
    if (!back) return judgement;
    return this.graph.convert(this.graph.replace(judgement, "term", [0], back), back);
  }

  // A motive over `domain`: a family P : Π(x : A). U(l) with A matching the
  // domain's type judgement.
  motive(judgement, domain) {
    const focus = this.focus(this.shape(this.focus(judgement, "type"), "Pi"), "type");
    this.shape(this.child(focus, 1), "U");
    const target = this.focus(this.graph.refl(domain), "other");
    if (!this.agree(this.child(focus, 0), target)) throw new Error("The motive is a family over another type.");
    // The domain now reads as the target's reduct; rewrite it back to A.
    const back = this.graph.symmetry(target.ref.id);
    return this.graph.replace(focus.ref.id, "type", [0], back);
  }

  // An interval point: a single dimension, an endpoint, or a compound formula.
  point(formula) {
    const { clauses } = this.kernel.inspectFormula(formula);
    if (!clauses.length) return { endpoint: 0 };
    if (clauses.length === 1 && !clauses[0][0] && !clauses[0][1]) return { endpoint: 1 };
    const [positive, negative] = clauses[0];
    if (clauses.length === 1 && !negative && (positive & (positive - 1n)) === 0n)
      return { dimension: positive.toString(2).length - 1 };
    return { compound: true };
  }
  // A typing judgement restricted to a face clause: its dimensions at their endpoints.
  restrict(judgement, [positive, negative]) {
    for (let dim = 0n; (positive | negative) >> dim; dim++) {
      const bit = 1n << dim;
      if ((positive | negative) & bit) judgement = this.graph.endpoint(judgement, this.graph.dimension(Number(dim)), positive & bit ? 1 : 0);
    }
    return judgement;
  }

  // A typing judgement for the type at a focus: derived again from its
  // syntax, in the context of its judgement.
  evidence(focus) {
    return this.asType(this.derive(this.subterm(focus), this.scope(focus.ref.id)));
  }
  asType(judgement) { return this.shape(this.focus(judgement, "type"), "U"); }

  // Reduce the focused subterm at its head until it has the given kind.
  shape(focus, kind) {
    for (let fuel = this.fuel; this.node(this.subterm(focus)).kind !== kind; fuel--) {
      const step = fuel > 0 && this.headStep(this.subterm(focus));
      if (step) this.reduce(focus, step);
      else if (fuel <= 0 || !this.whnf(focus)) throw new Error(`Expected ${kind}, found ${this.node(this.subterm(focus)).kind}.`);
    }
    return focus.ref.id;
  }

  // The kernel's weak head normal form of the focused subterm, for heads the
  // steps do not take: composition, transport, Glue, pushouts. False when it
  // is one already.
  whnf(focus) {
    const before = this.subterm(focus);
    // A constructor is a weak head already: the kernel would only contract it
    // by eta, undoing an expansion.
    if (this.stable.has(before) || CONSTRUCTORS.has(this.node(before).kind)) return false;
    this.reduce(focus, { path: [], rule: "whnf" });
    if (this.subterm(focus) !== before) return true;
    this.stable.add(before);
    return false;
  }
  // The glue move: Glue eta by the kernel's Glue step, when the weak head
  // leaves a Glue term. The weak head compares each piece with the base's
  // restriction by syntax, and the restriction can be a redex, as p @ i at
  // i = 0 is p's left endpoint; the Glue step compares the two normalized,
  // and normalizes nothing else of the term. Within its own step budget.
  // What it learns holds wherever the term occurs: that the term is no Glue
  // eta redex, or that its side conditions take more than the budget. The
  // same term at another focus may still need the move, and so may the base
  // it contracts to.
  glue(focus) {
    const before = this.subterm(focus);
    try { this.graph.within(GLUE_STEPS, () => this.reduce(focus, { path: [], rule: "glue" })); }
    catch (error) {
      // A deadline ends the comparison, as it would after any move. Anything
      // else is no progress, and the comparison goes on: the term is no
      // Glue eta redex, or its side conditions ran into the move's budget or
      // the depth of syntax.
      if (error.kind === "deadline") throw error;
      this.glueStuck.add(before);
      return false;
    }
    return true;
  }

  // The scope at a focus: its judgement's, with an entry for each term binder
  // on the way down, named as the binder so that Replace discharges it.
  // Null below a composition's tubes.
  scopeAt(focus) {
    let scope = this.scope(focus.ref.id), term = this.sideOf(focus.ref.id, focus.side);
    for (const child of focus.path) {
      const n = this.node(term);
      if ((n.kind === "Comp" && child === 1) || (n.kind === "HComp" && child === 1)) return null;
      if (TERM_BINDERS.has(n.kind) && child === 1) {
        const entry = LEVEL_BINDERS.has(n.kind) ? this.graph.levelEntry(n.payload)
          : this.bind(n.payload, this.asType(this.derive(n.children[0], scope)));
        if (this.graph.entry(entry).symbol !== n.payload) return null;
        scope = new Map(scope).set(n.payload, entry);
      }
      if (underBinder[n.kind]?.includes(child)) scope = withLive(scope, n.payload);
      term = n.children[child];
    }
    return scope;
  }

  // Eta: a lambda, path lambda or pair against a term of another kind. The
  // other term, derived again at its position, is expanded by Eta there.
  eta(a, b) {
    for (const [constructor, other] of [[a, b], [b, a]]) {
      const kind = this.node(this.subterm(constructor)).kind, type = etaTypes[kind];
      if (!type || this.node(this.subterm(other)).kind === kind) continue;
      try {
        const scope = this.scopeAt(other);
        if (!scope) continue;
        const typed = this.shape(this.focus(this.derive(this.subterm(other), scope), "type"), type);
        other.ref.id = this.graph.replace(other.ref.id, other.side, other.path, this.graph.eta(typed));
        return true;
      } catch { /* No expansion here: the search goes on without it. */ }
    }
    return false;
  }

  // judgement : A, and evidence B : U(l), give judgement : B.
  convertTo(judgement, evidence) {
    const g = this.graph, found = this.statement(judgement).type, wanted = this.statement(evidence).term;
    if (this.alpha(found, wanted)) return judgement;
    const a = this.focus(judgement, "type"), b = this.focus(g.refl(evidence), "other");
    const budget = { left: this.fuel };
    // A type mismatch, as the kernel reports one: the two types as they were.
    // Running out of time or budget is no answer, and is passed on as it is.
    const mismatch = error => ["budget", "deadline"].includes(error?.kind) ? error
      : Object.assign(new KernelError("Type mismatch.", "mismatch"), { mismatch: { found, expected: wanted }, search: error?.message });
    if (!this.agree(a, b, null, null, budget)) {
      // Too long, or stuck: compare normal forms, when they can be computed.
      try { for (const focus of [a, b]) this.reduce(focus, { path: [], rule: "normalize" }); }
      catch (error) { throw mismatch(error); }
    }
    if (!this.alpha(this.subterm(a), this.subterm(b))) {
      // Universes and families of universes are cumulative.
      let lifted;
      try { lifted = g.lift(a.ref.id, g.side(b.ref.id, "other")); }
      catch (error) { throw mismatch(error); }
      return g.convert(lifted, g.symmetry(b.ref.id));
    }
    return g.convert(a.ref.id, g.symmetry(b.ref.id));
  }

  // Whether two subterms are equal: true, false, or null when it cannot tell.
  // A guide for the search only. Without the oracle it is the driver's own
  // guide; with it, the term checker's conversion, after bound names that
  // differ are renamed on the right, innermost binder first.
  equal(x, y, terms, dims) {
    if (!this.oracle) return this.guide(x, y, terms, dims, { left: GUIDE_FUEL });
    try {
      for (const [bindings, dimension] of [[terms, false], [dims, true]]) {
        const renamed = new Set();
        for (let binding = bindings; binding; binding = binding.next) {
          if (renamed.has(binding.right)) continue;
          renamed.add(binding.right);
          if (binding.left !== binding.right) y = this.graph.rename(y, dimension, binding.right, binding.left);
        }
      }
    } catch (error) {
      // Out of time is passed on; a name that cannot be renamed leaves no answer.
      if (error?.kind === "deadline") throw error;
      return null;
    }
    const key = `${x},${y}`;
    if (!this.equalities.has(key)) this.equalities.set(key, this.graph.convertible(x, y, this.guideSteps));
    return this.equalities.get(key);
  }

  // The driver's own guide: two terms compared lazily through their weak head
  // normal forms, the kernel's trusted reduction asked as a query. Equal when
  // alpha-equal before or after taking heads; different when the heads are
  // constructors or neutral terms that differ, since normal forms are unique;
  // unknown when eta could relate them, a head is a cubical construction, or
  // the fuel runs out. Shared by one question: `fuel.left` pairs.
  guide(x, y, terms, dims, fuel) {
    if (this.alpha(x, y, terms, dims)) return true;
    if (--fuel.left < 0) return null;
    const key = `${x},${y},${this.chainId(terms)},${this.chainId(dims)}`;
    if (this.guesses.has(key)) return this.guesses.get(key);
    // A path at an endpoint of its annotated type is that endpoint, as the
    // path step takes it, with nothing computed.
    const ex = this.annotatedEndpoint(x), ey = this.annotatedEndpoint(y);
    if (ex || ey) {
      const answer = this.guide(ex || x, ey || y, terms, dims, fuel);
      if (answer !== null || fuel.left >= 0) this.guesses.set(key, answer);
      return answer;
    }
    const hx = this.headOf(x), hy = this.headOf(y);
    let answer = null;
    if (hx && hy) answer = (hx !== x || hy !== y) && this.alpha(hx, hy, terms, dims) ? true
      : this.compareHeads(this.node(hx), this.node(hy), terms, dims, fuel);
    // An answer cut short by the fuel is not kept: another question may have more.
    if (answer !== null || fuel.left >= 0) this.guesses.set(key, answer);
    return answer;
  }
  annotatedEndpoint(term) {
    const n = this.node(term);
    if (n.kind !== "PApp" || !n.children[1]) return 0;
    const point = this.point(n.payload), type = this.node(n.children[1]);
    return point.endpoint !== undefined && type.kind === "Path" ? type.children[1 + point.endpoint] : 0;
  }
  headOf(term) {
    if (!this.heads.has(term)) this.heads.set(term, this.graph.head(term, GUIDE_HEAD_STEPS));
    return this.heads.get(term);
  }
  compareHeads(nx, ny, terms, dims, fuel) {
    const known = n => RIGID.has(n.kind) || NEUTRAL.has(n.kind);
    if (nx.kind !== ny.kind) {
      if ((ETA_CONSTRUCTORS.has(nx.kind) && !RIGID.has(ny.kind)) || (ETA_CONSTRUCTORS.has(ny.kind) && !RIGID.has(nx.kind)))
        return null;
      return known(nx) && known(ny) ? false : null;
    }
    if (!known(nx)) return null;
    if (!this.sameHead(nx, ny, terms, dims)) return nx.kind === "PApp" ? null : false;
    let all = true;
    for (let i = 0; i < this.parts(nx); i++) {
      const a = nx.children[i], b = ny.children[i];
      if (!a || !b) { if (a !== b) all = false; continue; }
      let innerTerms = terms, innerDims = dims;
      if (TERM_BINDERS.has(nx.kind) && i === 1) innerTerms = { left: nx.payload, right: ny.payload, next: terms };
      if (dimensionBound(nx.kind, i)) innerDims = { left: nx.payload, right: ny.payload, next: dims };
      const answer = this.guide(a, b, innerTerms, innerDims, fuel);
      if (answer === false && ANNOTATION[nx.kind] !== i) return false;
      if (answer !== true) all = false;
    }
    return all ? true : null;
  }

  // Rewrite two focused subterms until they are alpha-equal: compare common
  // heads part by part when their parts are equal, and otherwise take
  // weak-head steps on either side.
  agree(a, b, terms = null, dims = null, budget = { left: this.fuel }) {
    // Pairs of terms congruence already failed on. A failed attempt can leave
    // an eta expansion that a step contracts again, so without this the same
    // attempt would repeat until the budget ran out.
    const failed = new Set();
    // A long closed computation, such as a numeral's arithmetic: unless the
    // term checker's conversion finds the two different, compute both normal
    // forms, one instruction each, rather than step by step. Each step
    // rebuilds the judgement's term; a normal form is computed once, in C.
    // Open terms keep to lazy steps: their normal forms can be enormous.
    //
    // Congruence splits a computation into many short comparisons, often
    // under a binder, where terms are open. So steps are counted over the
    // whole comparison. Past the limit, an open comparison inside a closed
    // one gives up, and the closed one tries normal forms. Each closed
    // comparison tries once; when that fails, the steps go on as before.
    let untried = this.closed(a) && this.closed(b);
    if (untried) budget.untried = (budget.untried ?? 0) + 1;
    const depth = this.depth++;
    try {
      for (;; budget.taken = (budget.taken ?? 0) + 1) {
        if (--budget.left < 0) return false;
        const x = this.subterm(a), y = this.subterm(b);
        if (this.alpha(x, y, terms, dims)) return true;
        let normalize = false;
        if ((budget.taken ?? 0) >= LONG_COMPUTATION) {
          if (untried) { untried = false; budget.untried--; normalize = true; }
          else if (budget.untried) return false;
        }
        const point = { driver: this, a, b, x, y, nx: this.node(x), ny: this.node(y), terms, dims,
          moves: null, round: 0, taken: budget.taken ?? 0, depth, normalize, descended: false, stuck: new Set(), failed,
          speculative: (budget.speculative ?? 0) > 0 };
        const outcome = this.branch(point, budget);
        if (outcome === "agreed") return true;
        if (outcome === "failed") return false;
      }
    } finally {
      this.depth--;
      if (untried) budget.untried--;
    }
  }

  // One branch point of `agree`: the moves open there, made in the chooser's
  // order until one applies. "agreed" when the sides now agree, "failed"
  // when no move applies, and otherwise the comparison goes round again.
  branch(point, budget) {
    for (;; point.round++) {
      point.moves = this.moves(point);
      let changed = false;
      for (const move of this.chooser.rank(point)) {
        if (!point.moves.includes(move)) throw new Error(`The chooser ${this.chooser.name} chose a move that is not open.`);
        let outcome;
        try { outcome = this.move(point, move, budget); }
        catch (error) {
          // The move's work is done, and observers hear of it; the error
          // ends the comparison as before.
          this.chooser.observe?.(point, move, "error", error);
          throw error;
        }
        this.chooser.observe?.(point, move, outcome);
        if (outcome === "stuck") continue;
        if (outcome === "changed") { changed = true; break; }
        return outcome;
      }
      // Normal forms are tried once, at the first listing.
      point.normalize = false;
      if (!changed) return "failed";
    }
  }
  // The moves open at a point (heuristicChooser, above). Congruence reads the
  // sides as the point found them; the rest reads them now, as a failed
  // attempt may have rewritten parts.
  moves(point) {
    const { a, b, nx, ny, terms, dims } = point, moves = [];
    if (point.normalize) moves.push({ move: "normalize" });
    if (!point.descended && nx.kind === ny.kind && !point.failed.has(`${point.x},${point.y}`) && this.sameHead(nx, ny, terms, dims))
      moves.push({ move: "descend" });
    const x = this.subterm(a), y = this.subterm(b), left = this.headStep(x), right = this.headStep(y);
    if (left) moves.push({ move: "step", side: "left", rule: left.rule, step: left, term: x });
    if (right) moves.push({ move: "step", side: "right", rule: right.rule, step: right, term: y });
    if (left?.rule === "delta" && right?.rule === "delta")
      moves.push({ move: "step", side: "both", rule: "delta", steps: [left, right] });
    // The kernel's weak head of a term not yet known to be one, and not a
    // constructor, which it would only contract by eta.
    for (const [side, term] of [["left", x], ["right", y]])
      if (!point.stuck.has(side) && !this.stable.has(term) && !CONSTRUCTORS.has(this.node(term).kind)) moves.push({ move: "whnf", side });
    const kx = this.node(x).kind, ky = this.node(y).kind;
    if (!point.stuck.has("eta") && kx !== ky && (etaTypes[kx] || etaTypes[ky])) moves.push({ move: "eta" });
    // Not inside a speculative descent: the enclosing comparison's lazy steps
    // come first, and should they fail, its last resort normalizes both sides.
    for (const [side, term] of [["left", x], ["right", y]])
      if (!point.speculative && this.node(term).kind === "GlueTerm" && !this.glueStuck.has(term) && !point.stuck.has(`glue:${side}`))
        moves.push({ move: "glue", side });
    return moves;
  }
  // Make a move: its outcome, as `branch` reads it.
  move(point, move, budget) {
    const { a, b, terms, dims } = point;
    switch (move.move) {
    case "normalize": return this.normalizeBoth(a, b, terms, dims) ? "agreed" : "changed";
    case "descend": {
      point.descended = true;
      // A descent is speculative while this point still has lazy steps to
      // try should it fail: inside it, the glue move waits (moves).
      const speculative = point.moves.some(open => open.move === "step");
      if (speculative) budget.speculative = (budget.speculative ?? 0) + 1;
      let agreed;
      try { agreed = this.agreeParts(a, b, point.nx, terms, dims, budget); }
      finally { if (speculative) budget.speculative--; }
      if (agreed) return "agreed";
      // A comparison inside gave up for an enclosing closed one to try
      // normal forms: congruence has not failed, and may be tried again.
      if (budget.untried && budget.taken >= LONG_COMPUTATION) return "deferred";
      point.failed.add(`${point.x},${point.y}`);
      return "changed";
    }
    case "step":
      if (move.side !== "right") this.reduce(a, move.side === "both" ? move.steps[0] : move.step);
      if (move.side !== "left") this.reduce(b, move.side === "both" ? move.steps[1] : move.step);
      return "progress";
    case "whnf":
      if (this.whnf(move.side === "left" ? a : b)) return "progress";
      point.stuck.add(move.side);
      return "stuck";
    case "eta":
      if (this.eta(a, b)) return "progress";
      point.stuck.add("eta");
      return "stuck";
    case "glue":
      if (this.glue(move.side === "left" ? a : b)) return "progress";
      point.stuck.add(`glue:${move.side}`);
      return "stuck";
    default: throw new Error(`Unknown move ${move.move}.`);
    }
  }
  // Whether the focused subterm has no free term variable: its judgement has
  // none in context, and the position is under no term binder.
  closed(focus) {
    if (this.statement(focus.ref.id).context.some(entry => !this.graph.entry(entry).dimension)) return false;
    let term = this.sideOf(focus.ref.id, focus.side);
    for (const child of focus.path) {
      const n = this.node(term);
      if (TERM_BINDERS.has(n.kind) && child === 1) return false;
      term = n.children[child];
    }
    return true;
  }
  normalizeBoth(a, b, terms, dims) {
    try { for (const focus of [a, b]) this.reduce(focus, { path: [], rule: "normalize" }); }
    catch { return false; }
    return this.alpha(this.subterm(a), this.subterm(b), terms, dims);
  }
  // The registry index of the definition a delta step unfolds.
  definitionAt(term, step) {
    for (const child of step.path) term = this.node(term).children[child];
    return this.node(term).payload;
  }
  sameHead(x, y, terms, dims) {
    if (x.kind === "Var") return this.sameName(x.payload, y.payload, terms);
    if (x.kind === "U") return this.levelsEqual(x.children[0], y.children[0], terms);
    if (x.kind === "LApp") return this.levelsEqual(x.children[1], y.children[1], terms);
    // An instance: its signature, and its recorded levels by normal form.
    if (x.kind === "Sort") {
      if (x.payload !== y.payload) return false;
      let a = x.children[1], b = y.children[1];
      for (; a && b; a = this.node(a).children[1], b = this.node(b).children[1])
        if (!this.levelsEqual(this.node(a).children[0], this.node(b).children[0], terms)) return false;
      return !a && !b;
    }
    if (FORMULA_PAYLOADS.has(x.kind)) return this.sameFormula(x.payload, y.payload, dims);
    if (TERM_BINDERS.has(x.kind) || ["PLam", "Path", "Comp", "HComp", "Trans"].includes(x.kind)) return true;
    return x.payload === y.payload;
  }
  nodeHandle(node) { return node.id; }
  // The operand slots compared: all but a path application's annotation, a
  // universe's level, an instantiation's level and an instance's recorded
  // levels, which sameHead compares.
  parts(n) { return n.kind === "U" ? 0 : n.kind === "PApp" || n.kind === "LApp" || n.kind === "Sort" ? 1 : 4; }
  // Two levels are equal when their normal forms are (G0 §2.4), each variable
  // bound on the way down named by its binder, so that the levels of
  // λ (x < ω). U(max(x, z)) and λ (y < ω). U(max(z, y)) agree though their
  // canonical nodes order the variables differently.
  levelsEqual(x, y, terms) {
    if (x === y && this.unrenamed(terms)) return true;
    const read = id => this.node(id), a = levelNormal(read, x), b = levelNormal(read, y);
    if (a.tier !== b.tier || a.constant !== b.constant || a.offsets.size !== b.offsets.size) return false;
    const key = (symbol, right) => {
      let depth = 0;
      for (let binding = terms; binding; binding = binding.next, depth++)
        if ((right ? binding.right : binding.left) === symbol) return `bound ${depth}`;
      return `free ${symbol}`;
    };
    const renamed = new Map([...b.offsets].map(([symbol, offset]) => [key(symbol, true), offset]));
    return [...a.offsets].every(([symbol, offset]) => renamed.get(key(symbol, false)) === offset);
  }
  // Whether congruence can work: no pair of parts is known to differ. Only
  // asked when a head could be reduced instead; parts under a binder are left
  // to the comparison itself.
  //
  // A computation step (beta, iota, path, face) is cheap and never a wrong
  // turn: it is taken rather than comparing parts it may discard, unless they
  // are known equal. Unfolding a definition is not cheap: there, parts not
  // known to differ are compared first.
  partsEqual(x, y, terms, dims) {
    const left = this.headStep(this.nodeHandle(x)), right = this.headStep(this.nodeHandle(y));
    if (!left && !right) return true;
    const computes = (left && left.rule !== "delta") || (right && right.rule !== "delta");
    for (let i = 0; i < this.parts(x); i++) {
      if (!x.children[i] || !y.children[i] || (TERM_BINDERS.has(x.kind) && i === 1) || dimensionBound(x.kind, i)) continue;
      const answer = this.equal(x.children[i], y.children[i], terms, dims);
      if (answer === false || (computes && answer !== true)) return false;
    }
    return true;
  }
  agreeParts(a, b, n, terms, dims, budget) {
    for (let i = 0; i < this.parts(n); i++) {
      const x = this.node(this.subterm(a)), y = this.node(this.subterm(b));
      if (!x.children[i] || !y.children[i]) {
        if (x.children[i] !== y.children[i]) return false;
        continue;
      }
      let innerTerms = terms, innerDims = dims;
      if (TERM_BINDERS.has(n.kind) && i === 1) innerTerms = { left: x.payload, right: y.payload, next: terms };
      if (dimensionBound(n.kind, i)) innerDims = { left: x.payload, right: y.payload, next: dims };
      if (!this.agree(this.child(a, i), this.child(b, i), innerTerms, innerDims, budget)) return false;
    }
    return true;
  }

  // The weak-head redex of a term, as the term checker's reduction finds it:
  // the function of an application first, then the scrutinee of an
  // eliminator. Null for a weak head normal form.
  headStep(term) {
    const n = this.node(term), under = (index, step) => step && { path: [index, ...step.path], rule: step.rule };
    const iota = { path: [], rule: "iota" };
    switch (n.kind) {
    case "DefRef": return { path: [], rule: "delta" };
    case "LApp":
      return this.node(n.children[0]).kind === "LLam" ? { path: [], rule: "beta" } : under(0, this.headStep(n.children[0]));
    case "App": {
      const fn = this.node(n.children[0]).kind;
      if (fn === "Lam") return { path: [], rule: "beta" };
      // The pushout eliminator computes on a point or a path.
      if (fn === "PushElim") {
        const kind = this.node(n.children[1]).kind;
        return ["PushLeft", "PushRight", "PushPath"].includes(kind) ? iota : under(1, this.headStep(n.children[1]));
      }
      // A declared type's eliminator computes on a constructor applied to
      // its arguments and at its dimensions (H1). A constructor at an
      // endpoint is its boundary first, by the path step inside.
      if (fn === "Elim") return this.constructed(n.children[1]) ? iota : under(1, this.headStep(n.children[1]));
      return under(0, this.headStep(n.children[0]));
    }
    // A pushout path at an endpoint is a point.
    case "PushPath": return this.point(n.payload).endpoint !== undefined ? iota : null;
    case "Fst": case "Snd":
      return this.node(n.children[0]).kind === "Pair" ? iota : under(0, this.headStep(n.children[0]));
    case "NatRec": {
      const kind = this.node(n.children[3]).kind;
      return kind === "Zero" || kind === "Succ" ? iota : under(3, this.headStep(n.children[3]));
    }
    case "SumRec": {
      const kind = this.node(n.children[3]).kind;
      return kind === "Inl" || kind === "Inr" ? iota : under(3, this.headStep(n.children[3]));
    }
    case "UnitRec":
      return this.node(n.children[2]).kind === "Point" ? iota : under(2, this.headStep(n.children[2]));
    case "WRec":
      return this.node(n.children[2]).kind === "Sup" ? iota : under(2, this.headStep(n.children[2]));
    case "PApp": {
      const fn = this.node(n.children[0]);
      if (fn.kind === "PLam") {
        // Substituting a compound formula can expand it exponentially, as in
        // 1 - (a ∧ b ∨ c ∧ d ∨ …): contract the body's own computing head
        // first, so that the formula meets a smaller term, often none.
        if (this.point(n.payload).compound) {
          const inner = this.headStep(fn.children[1]);
          if (inner && inner.rule !== "delta") return { path: [0, 1, ...inner.path], rule: inner.rule };
        }
        return { path: [], rule: "path" };
      }
      const point = this.point(n.payload);
      if (point.endpoint !== undefined && n.children[1] && this.node(n.children[1]).kind === "Path")
        return { path: [], rule: "path" };
      return under(0, this.headStep(n.children[0]));
    }
    // A composition with a tube on a face that holds is that tube at 1. Any
    // other composition computes by its type, which only Whnf takes.
    case "Comp": case "HComp": case "Trans":
      for (let tube = n.children[1]; tube; tube = this.node(tube).children[1]) {
        const { clauses } = this.kernel.inspectFormula(this.node(tube).payload);
        if (clauses.length === 1 && !clauses[0][0] && !clauses[0][1]) return { path: [], rule: "face" };
      }
      return null;
    default: return null;
    }
  }

  // Whether a term is a declared type's constructor applied, at dimensions
  // that are not endpoints: c(ts, qs) @ rs.
  constructed(term) {
    let n = this.node(term);
    for (; n.kind === "PApp"; n = this.node(n.children[0]))
      if (this.point(n.payload).endpoint !== undefined) return false;
    for (; n.kind === "App"; n = this.node(n.children[0]));
    return n.kind === "Con";
  }

  // Alpha equality, as the kernel decides it without reducing: bound names
  // correspond through `terms` and `dims`, lists of {left, right, next}.
  //
  // Terms are shared graphs, not trees: a subterm met twice under the same
  // renaming is compared once, and a term against itself under binders each
  // named as on the other side needs no comparison. Without both, a term
  // such as refl(refl(… refl(0))) takes time exponential in its depth. The
  // renaming of dimensions is cut to those the two terms mention, so that
  // a subterm met under many binders is still compared once.
  alpha(x, y, terms = null, dims = null) {
    if (dims) dims = this.prune(dims, freeDimensionMask(this.kernel, x, this.freeDims),
      freeDimensionMask(this.kernel, y, this.freeDims));
    if (x === y && this.unrenamed(terms) && this.unrenamed(dims)) return true;
    if (!x || !y) return x === y;
    const key = `${x},${y},${this.chainId(terms)},${this.chainId(dims)}`, known = this.alphaMemo.get(key);
    if (known !== undefined) return known;
    const nx = this.node(x), ny = this.node(y);
    let equal = nx.kind === ny.kind && this.sameHead(nx, ny, terms, dims);
    for (let i = 0; equal && i < this.parts(nx); i++) {
      let innerTerms = terms, innerDims = dims;
      if (TERM_BINDERS.has(nx.kind) && i === 1) innerTerms = { left: nx.payload, right: ny.payload, next: terms };
      if (dimensionBound(nx.kind, i)) innerDims = { left: nx.payload, right: ny.payload, next: dims };
      equal = this.alpha(nx.children[i], ny.children[i], innerTerms, innerDims);
    }
    this.alphaMemo.set(key, equal);
    return equal;
  }
  // A renaming of dimensions without the pairs neither side mentions: no
  // lookup from either side can reach those, as names bound inside are
  // found first. Equal cuts are one object, so they share memo keys.
  prune(bindings, left, right) {
    if (!bindings) return null;
    const key = `${this.chainId(bindings)},${left},${right}`;
    let result = this.pruned.get(key);
    if (result === undefined) {
      const next = this.prune(bindings.next, left, right);
      const used = (left >> BigInt(bindings.left) & 1n) || (right >> BigInt(bindings.right) & 1n);
      result = !used ? next : next === bindings.next ? bindings : { left: bindings.left, right: bindings.right, next };
      this.pruned.set(key, result);
    }
    return result;
  }
  // Whether a renaming maps every name to itself: odd ids are identities.
  unrenamed(bindings) { return !bindings || this.chainId(bindings) % 2 === 1; }
  // A renaming by its content, as a small number, so equal renamings built
  // apart share memo keys.
  chainId(bindings) {
    if (!bindings) return 1;
    let id = this.chainIds.get(bindings);
    if (id === undefined) {
      const next = this.chainId(bindings.next), content = `${bindings.left}:${bindings.right}:${next}`;
      id = this.chainNumbers.get(content);
      if (id === undefined) {
        // Keep identities odd: this link maps its name to itself, and so did the rest.
        const identity = bindings.left === bindings.right && next % 2 === 1;
        id = 2 * (this.chainNumbers.size + 1) + (identity ? 1 : 0);
        this.chainNumbers.set(content, id);
      }
      this.chainIds.set(bindings, id);
    }
    return id;
  }
  sameName(left, right, bindings) {
    for (let binding = bindings; binding; binding = binding.next)
      if (binding.left === left || binding.right === right) return binding.left === left && binding.right === right;
    return left === right;
  }
  sameFormula(left, right, dims) {
    if (left === right && !dims) return true;
    const rename = (clauses, side) => clauses.map(([positive, negative]) => [positive, negative].map(bits => {
      let renamed = 0n;
      for (let index = 0n; bits >> index; index++) {
        if (!((bits >> index) & 1n)) continue;
        let target = index;
        for (let binding = dims; binding; binding = binding.next)
          if (BigInt(side ? binding.right : binding.left) === index) { target = BigInt(binding.left); break; }
        renamed |= 1n << target;
      }
      return renamed.toString();
    }).join(":")).sort().join(",");
    const a = this.kernel.inspectFormula(left), b = this.kernel.inspectFormula(right);
    return a.sort === b.sort && rename(a.clauses, 0) === rename(b.clauses, 1);
  }
}
