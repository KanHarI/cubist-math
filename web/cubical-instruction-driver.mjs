// The untrusted driver of the instruction kernel. It replays a term the
// elaborator built as instructions, one per node, and searches for the
// equality steps that make types agree where a rule needs them to:
// congruence on common heads, weak-head steps as the term checker's
// conversion takes them, the kernel's weak head normal form for heads those
// steps do not take, eta, and a normalization when that runs long. It steers
// by asking the term checker's conversion which parts are equal. The kernel
// checks every instruction; a wrong search only fails, it cannot prove
// anything.
import { InstructionGraph } from "./cubical-instructions.mjs";
import { KernelError } from "./cubical-kernel.mjs";
import { freeDimensionMask } from "./cubical-syntax.mjs";

const TERM_BINDERS = new Set(["Pi", "Lam", "Sigma", "W"]);
// Nodes whose payload is an interval or face formula.
const FORMULA_PAYLOADS = new Set(["PApp", "Tube", "GlueSystem", "PushPath"]);
const unsupported = kind => new Error(`${kind} is not in instruction mode yet.`);
// Whether child i of a node is under its dimension binder (the payload).
const dimensionBound = (kind, i) => kind === "PLam" || ((kind === "Path" || kind === "Trans") && i === 0) ||
  (kind === "Comp" && i < 2) || (kind === "HComp" && i === 1);
// Weak heads that only compute by eta, or not at all.
const CONSTRUCTORS = new Set(["U", "Pi", "Lam", "Sigma", "Pair", "Nat", "Zero", "Succ", "Unit", "Point", "Void",
  "Sum", "Inl", "Inr", "Path", "PLam", "W", "Sup", "Pushout", "PushLeft", "PushRight"]);
// The type former a constructor's eta expansion needs.
const etaTypes = { Lam: "Pi", PLam: "Path", Pair: "Sigma" };
// Steps after which a comparison the oracle finds true computes normal forms.
const LONG_COMPUTATION = 64;
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

export class InstructionDriver {
  constructor(kernel, { graph = new InstructionGraph(kernel), fuel = 20000, guideSteps = 20000 } = {}) {
    this.kernel = kernel;
    this.graph = graph;
    this.fuel = fuel;
    this.guideSteps = guideSteps;
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
    this.equalities = new Map();
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
      const scope = new Map([[LIVE, dimensions]]);
      for (const [symbol, assumption] of context)
        scope.set(symbol, this.bind(symbol, this.asType(this.derive(assumption, scope))));
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
      this.mentions.set(key, [...scope].some(([symbol, entry]) => symbol !== LIVE &&
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
    case "U": return g.universe(n.payload);
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
    default: throw unsupported(n.kind);
    }
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

  // The scope at a focus: its judgement's, with an entry for each term binder
  // on the way down, named as the binder so that Replace discharges it.
  // Null below a composition's tubes.
  scopeAt(focus) {
    let scope = this.scope(focus.ref.id), term = this.sideOf(focus.ref.id, focus.side);
    for (const child of focus.path) {
      const n = this.node(term);
      if ((n.kind === "Comp" && child === 1) || (n.kind === "HComp" && child === 1)) return null;
      if (TERM_BINDERS.has(n.kind) && child === 1) {
        const entry = this.bind(n.payload, this.asType(this.derive(n.children[0], scope)));
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

  // Whether two subterms are equal, by the term checker's conversion: true,
  // false, or null when it cannot tell. Bound names that differ are renamed
  // on the right first, innermost binder first. A guide for the search only.
  equal(x, y, terms, dims) {
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
    try {
      for (;; budget.taken = (budget.taken ?? 0) + 1) {
        if (--budget.left < 0) return false;
        const x = this.subterm(a), y = this.subterm(b);
        if (this.alpha(x, y, terms, dims)) return true;
        if ((budget.taken ?? 0) >= LONG_COMPUTATION) {
          if (untried) {
            untried = false; budget.untried--;
            if (this.equal(x, y, terms, dims) !== false && this.normalizeBoth(a, b, terms, dims)) return true;
          } else if (budget.untried) return false;
        }
        const nx = this.node(x), ny = this.node(y);
        if (nx.kind === ny.kind && !failed.has(`${x},${y}`) && this.sameHead(nx, ny, terms, dims) &&
            this.partsEqual(nx, ny, terms, dims)) {
          if (this.agreeParts(a, b, nx, terms, dims, budget)) return true;
          // A comparison inside gave up for an enclosing closed one to try
          // normal forms: congruence has not failed, and may be tried again.
          if (budget.untried && budget.taken >= LONG_COMPUTATION) continue;
          failed.add(`${x},${y}`);
        }
        // Computation before unfolding: beta, iota, path and face steps first.
        // Then unfold the later definition, as it is likely defined through the
        // other, and both when they are the same (lazy delta reduction).
        // A congruence attempt that failed may have rewritten parts: read again.
        const x2 = this.subterm(a), y2 = this.subterm(b);
        const left = this.headStep(x2), right = this.headStep(y2);
        if (left && left.rule !== "delta") { this.reduce(a, left); continue; }
        if (right && right.rule !== "delta") { this.reduce(b, right); continue; }
        if (left && right) {
          const order = this.definitionAt(x2, left) - this.definitionAt(y2, right);
          if (order >= 0) this.reduce(a, left);
          if (order <= 0) this.reduce(b, right);
          continue;
        }
        if (left) { this.reduce(a, left); continue; }
        if (right) { this.reduce(b, right); continue; }
        if (this.whnf(a) || this.whnf(b) || this.eta(a, b)) continue;
        return false;
      }
    } finally { if (untried) budget.untried--; }
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
    if (FORMULA_PAYLOADS.has(x.kind)) return this.sameFormula(x.payload, y.payload, dims);
    if (TERM_BINDERS.has(x.kind) || ["PLam", "Path", "Comp", "HComp", "Trans"].includes(x.kind)) return true;
    return x.payload === y.payload;
  }
  nodeHandle(node) { return node.id; }
  // The operand slots compared: all but a path application's annotation.
  parts(n) { return n.kind === "PApp" ? 1 : 4; }
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
    case "App": {
      const fn = this.node(n.children[0]).kind;
      if (fn === "Lam") return { path: [], rule: "beta" };
      // The pushout eliminator computes on a point or a path.
      if (fn === "PushElim") {
        const kind = this.node(n.children[1]).kind;
        return ["PushLeft", "PushRight", "PushPath"].includes(kind) ? iota : under(1, this.headStep(n.children[1]));
      }
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
