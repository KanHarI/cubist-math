// The untrusted driver of the instruction kernel. It replays a term the
// elaborator built as instructions, one per node, and searches for the
// equality steps that make types agree where a rule needs them to: weak-head
// steps, as the term checker's conversion takes them, congruence on common
// heads, and a normalization when that runs long. The kernel checks every
// instruction; a wrong search only fails, it cannot prove anything.
import { InstructionGraph } from "./cubical-instructions.mjs";

const TERM_BINDERS = new Set(["Pi", "Lam", "Sigma", "W"]);
const unsupported = kind => new Error(`${kind} is not in instruction mode yet.`);

export class InstructionDriver {
  constructor(kernel, { graph = new InstructionGraph(kernel), fuel = 20000 } = {}) {
    this.kernel = kernel;
    this.graph = graph;
    this.fuel = fuel;
    this.nodes = new Map();
  }

  // The judgement `expression : type` for a checked term and its type, in a
  // context of [symbol, type] assumptions, each over the ones before it.
  check(expression, type, context = []) {
    const scope = new Map();
    for (const [symbol, assumption] of context)
      scope.set(symbol, this.bind(symbol, this.asType(this.derive(assumption, scope))));
    return this.convertTo(this.derive(expression, scope), this.asType(this.derive(type, scope)));
  }

  node(handle) {
    if (!this.nodes.has(handle)) this.nodes.set(handle, this.kernel.node(handle));
    return this.nodes.get(handle);
  }
  statement(id) { return this.graph.judgement(id); }
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
    const scope = new Map();
    for (const entry of this.statement(id).context) {
      const info = this.graph.entry(entry);
      if (!info.dimension) scope.set(info.symbol, entry);
    }
    return scope;
  }
  // A context entry for a binder: its own name unless another entry of a
  // different type has it, then the first free variant.
  bind(symbol, type) { return this.entry(type, this.kernel.symbolName(symbol), false); }
  freshEntry(type, stem) { return this.entry(type, stem, true); }
  entry(type, stem, fresh) {
    for (let suffix = fresh ? 1 : 0; ; suffix++) {
      try { return this.graph.extend(type, suffix ? `${stem}'${suffix}` : stem); }
      catch (error) { if (!/already names/.test(error.message)) throw error; }
    }
  }

  derive(handle, scope) {
    const g = this.graph, n = this.node(handle), [a, b, c, d] = n.children;
    const derive = (child, inner = scope) => this.derive(child, inner);
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
    case "Pi": case "Sigma": case "Lam": {
      const entry = this.bind(n.payload, this.asType(derive(a)));
      const inner = new Map(scope).set(n.payload, entry);
      if (n.kind === "Lam") return g.lambda(entry, derive(b, inner));
      const body = this.asType(derive(b, inner));
      return n.kind === "Pi" ? g.pi(entry, body) : g.sigma(entry, body);
    }
    case "App": {
      const fn = this.shape(this.focus(derive(a), "type"), "Pi");
      return g.apply(fn, this.convertTo(derive(b), this.evidence(this.focus(fn, "type", [0]))));
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
      const dimension = g.dimension(n.payload), family = this.asType(derive(a));
      return g.path(dimension, family, this.convertTo(derive(b), g.endpoint(family, dimension, 0)),
        this.convertTo(derive(c), g.endpoint(family, dimension, 1)));
    }
    case "PLam": return g.pathLambda(g.dimension(n.payload), derive(b));
    case "PApp": {
      const path = this.shape(this.focus(derive(a), "type"), "Path");
      const point = this.point(n.payload);
      if (point.dimension !== undefined) return g.pathApply(path, g.dimension(point.dimension), 0);
      return g.pathApply(path, 0, point.endpoint);
    }
    default: throw unsupported(n.kind);
    }
  }

  // A constructor's annotation as a type former of the given kind: the
  // annotation itself, or its reduct with the equality back to it, so the
  // constructed term can be given the annotation as its type again.
  former(annotation, kind) {
    if (this.node(this.statement(annotation).term).kind === kind) return [annotation, null];
    const reduct = this.focus(this.graph.refl(annotation), "other");
    this.shape(reduct, kind);
    return [this.graph.side(reduct.ref.id, "other"), this.graph.symmetry(reduct.ref.id)];
  }
  restore(judgement, back) { return back ? this.graph.convert(judgement, back) : judgement; }

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

  // An interval point: a single dimension, or an endpoint.
  point(formula) {
    const { clauses } = this.kernel.inspectFormula(formula);
    if (!clauses.length) return { endpoint: 0 };
    if (clauses.length === 1 && !clauses[0][0] && !clauses[0][1]) return { endpoint: 1 };
    const [positive, negative] = clauses[0];
    if (clauses.length === 1 && !negative && (positive & (positive - 1n)) === 0n)
      return { dimension: positive.toString(2).length - 1 };
    throw unsupported("A compound interval formula");
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
      if (!step) throw new Error(`Expected ${kind}, found ${this.node(this.subterm(focus)).kind}.`);
      this.reduce(focus, step);
    }
    return focus.ref.id;
  }

  // judgement : A, and evidence B : U(l), give judgement : B.
  convertTo(judgement, evidence) {
    const g = this.graph, found = this.statement(judgement).type, wanted = this.statement(evidence).term;
    if (this.alpha(found, wanted)) return judgement;
    const a = this.focus(judgement, "type"), b = this.focus(g.refl(evidence), "other");
    const budget = { left: this.fuel };
    if (!this.agree(a, b, null, null, budget)) {
      // Too long, or stuck: compare normal forms.
      for (const focus of [a, b]) this.reduce(focus, { path: [], rule: "normalize" });
    }
    if (!this.alpha(this.subterm(a), this.subterm(b))) {
      // Universes and families of universes are cumulative.
      const lifted = g.lift(a.ref.id, g.side(b.ref.id, "other"));
      return g.convert(lifted, g.symmetry(b.ref.id));
    }
    return g.convert(a.ref.id, g.symmetry(b.ref.id));
  }

  // Rewrite two focused subterms until they are alpha-equal: compare common
  // heads part by part first, then take weak-head steps on either side.
  agree(a, b, terms = null, dims = null, budget = { left: this.fuel }) {
    for (;;) {
      if (--budget.left < 0) return false;
      const x = this.subterm(a), y = this.subterm(b);
      if (this.alpha(x, y, terms, dims)) return true;
      const nx = this.node(x), ny = this.node(y);
      if (nx.kind === ny.kind && this.sameHead(nx, ny, terms, dims) && this.agreeParts(a, b, nx, terms, dims, budget))
        return true;
      const left = this.headStep(this.subterm(a));
      if (left) { this.reduce(a, left); continue; }
      const right = this.headStep(this.subterm(b));
      if (right) { this.reduce(b, right); continue; }
      return false;
    }
  }
  sameHead(x, y, terms, dims) {
    if (x.kind === "Var") return this.sameName(x.payload, y.payload, terms);
    if (x.kind === "PApp") return this.sameFormula(x.payload, y.payload, dims);
    if (TERM_BINDERS.has(x.kind) || x.kind === "PLam" || x.kind === "Path") return true;
    return x.payload === y.payload;
  }
  agreeParts(a, b, n, terms, dims, budget) {
    const count = n.kind === "PApp" ? 1 : n.children.filter(Boolean).length;
    for (let i = 0; i < count; i++) {
      const x = this.node(this.subterm(a)), y = this.node(this.subterm(b));
      let innerTerms = terms, innerDims = dims;
      if (TERM_BINDERS.has(n.kind) && i === 1) innerTerms = { left: x.payload, right: y.payload, next: terms };
      if ((n.kind === "PLam") || (n.kind === "Path" && i === 0)) innerDims = { left: x.payload, right: y.payload, next: dims };
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
    case "App":
      return this.node(n.children[0]).kind === "Lam" ? { path: [], rule: "beta" } : under(0, this.headStep(n.children[0]));
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
    case "PApp": {
      if (this.node(n.children[0]).kind === "PLam") return { path: [], rule: "path" };
      const point = this.point(n.payload);
      if (point.endpoint !== undefined && n.children[1] && this.node(n.children[1]).kind === "Path")
        return { path: [], rule: "path" };
      return under(0, this.headStep(n.children[0]));
    }
    default: return null;
    }
  }

  // Alpha equality, as the kernel decides it without reducing: bound names
  // correspond through `terms` and `dims`, lists of {left, right, next}.
  alpha(x, y, terms = null, dims = null) {
    if (x === y && !terms && !dims) return true;
    if (!x || !y) return x === y;
    const nx = this.node(x), ny = this.node(y);
    if (nx.kind !== ny.kind || !this.sameHead(nx, ny, terms, dims)) return false;
    const count = nx.kind === "PApp" ? 1 : nx.children.length;
    for (let i = 0; i < count; i++) {
      let innerTerms = terms, innerDims = dims;
      if (TERM_BINDERS.has(nx.kind) && i === 1) innerTerms = { left: nx.payload, right: ny.payload, next: terms };
      if (nx.kind === "PLam" || (nx.kind === "Path" && i === 0)) innerDims = { left: nx.payload, right: ny.payload, next: dims };
      if (!this.alpha(nx.children[i], ny.children[i], innerTerms, innerDims)) return false;
    }
    return true;
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
