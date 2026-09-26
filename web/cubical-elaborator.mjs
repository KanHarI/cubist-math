import { CubicalSyntax } from "./cubical-syntax.mjs";
import { T, substituteTerm } from "./dist/cubical-runtime/core.mjs";
import { interval as I } from "./dist/cubical-runtime/lattice.mjs";
import { NameSupply } from "./dist/cubical-runtime/names.mjs";
import { sourceText } from "./cubical-source-text.mjs";

const speculativeFailures = new Set(["mismatch", "budget", "deadline"]);
const namedBinders = new Set(["Var", "Pi", "Lam", "Sigma", "W"]);

// For messages only: reduce beta-redexes, within a budget, and give generated
// names back their source stems (`A3` → `A`, `native10` → `x`) where no two
// names would clash. The result is never checked or stored.
export function displayTerm(term, budget = 256) {
  const shown = betaReduce(term, budget);
  return scopedNames(shown) ?? globalNames(shown);
}

// Beta-reduce within a budget of substitutions, keeping every name.
export function betaReduce(term, budget = 256) {
  const reduced = new WeakMap();
  const beta = t => {
    if (!t || typeof t !== "object") return t;
    if (reduced.has(t)) return reduced.get(t);
    let result = Array.isArray(t) ? t.map(beta) : Object.fromEntries(Object.entries(t).map(([key, value]) => [key, beta(value)]));
    while (result.tag === "App" && result.fn?.tag === "Lam" && budget-- > 0)
      result = beta(substituteTerm(result.fn.body, result.fn.name, result.arg));
    reduced.set(t, result);
    return result;
  };
  return beta(term);
}

const stem = name => name.startsWith("__") ? name : /^native\d+$/.test(name) ? "x" : name.replace(/\d+$/, "") || name;
const binders = new Set(["Pi", "Lam", "Sigma", "W"]);

// Each binder shows its stem, n for n11, unless a binder around it already
// shows that name or its body uses the name for another variable; then it
// shows the stem numbered from 1, n1. The copy is a tree, so a term that
// shares much structure is left to globalNames.
function scopedNames(term, limit = 2000) {
  let work = 0;
  const freeMemo = new WeakMap();
  const free = t => {
    if (!t || typeof t !== "object") return new Set();
    if (freeMemo.has(t)) return freeMemo.get(t);
    let names;
    if (t.tag === "Var") names = new Set([t.name]);
    else {
      names = new Set();
      for (const [key, value] of Object.entries(t)) {
        if (binders.has(t.tag) && key === "body") for (const name of free(value)) { if (name !== t.name) names.add(name); }
        else for (const name of free(value)) names.add(name);
      }
    }
    freeMemo.set(t, names);
    return names;
  };
  const go = (t, shownAs, inScope) => {
    if (++work > limit) throw scopedNames;
    if (!t || typeof t !== "object") return t;
    if (Array.isArray(t)) return t.map(item => go(item, shownAs, inScope));
    if (t.tag === "Var") return shownAs.has(t.name) ? { ...t, name: shownAs.get(t.name) } : t;
    const result = {};
    if (binders.has(t.tag) && typeof t.name === "string") {
      const others = new Set([...free(t.body)].filter(name => name !== t.name).map(name => shownAs.get(name) ?? name));
      const taken = candidate => inScope.has(candidate) || others.has(candidate);
      let name = stem(t.name);
      for (let index = 1; taken(name); index++) name = `${stem(t.name)}${index}`;
      for (const [key, value] of Object.entries(t))
        result[key] = key === "body" ? go(value, new Map(shownAs).set(t.name, name), new Set(inScope).add(name))
          : key === "name" ? name : go(value, shownAs, inScope);
      return result;
    }
    for (const [key, value] of Object.entries(t)) result[key] = go(value, shownAs, inScope);
    return result;
  };
  // Free variables, such as a goal's context, show their stems when no two
  // share one; binders then avoid those names.
  const outer = [...free(term)], count = new Map();
  for (const name of outer) count.set(stem(name), (count.get(stem(name)) ?? 0) + 1);
  const shownAs = new Map(outer.map(name => [name,
    count.get(stem(name)) === 1 && !(outer.includes(stem(name)) && stem(name) !== name) ? stem(name) : name]));
  try { return go(term, shownAs, new Set(shownAs.values())); }
  catch (error) { if (error === scopedNames) return null; throw error; }
}

// Every generated name whose stem no other name shares shows its stem.
function globalNames(shown) {
  const names = new Set(), seen = new WeakSet();
  const collect = t => {
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    if (namedBinders.has(t.tag) && typeof t.name === "string") names.add(t.name);
    Object.values(t).forEach(collect);
  };
  collect(shown);
  const count = new Map();
  for (const name of names) count.set(stem(name), (count.get(stem(name)) ?? 0) + 1);
  const rename = name => count.get(stem(name)) === 1 && !(names.has(stem(name)) && stem(name) !== name) ? stem(name) : name;
  const renamed = new WeakMap();
  const apply = t => {
    if (!t || typeof t !== "object") return t;
    if (renamed.has(t)) return renamed.get(t);
    const result = Array.isArray(t) ? t.map(apply) : Object.fromEntries(Object.entries(t).map(([key, value]) => [key, apply(value)]));
    if (namedBinders.has(t.tag) && typeof t.name === "string") result.name = rename(t.name);
    renamed.set(t, result);
    return result;
  };
  return apply(shown);
}

// Elaboration queries use the native checker and demand only a type's outer
// constructor. JavaScript neither normalizes proofs nor approves conversions.
export class NativeCubicalElaborator {
  constructor(kernel) {
    this.kernel = kernel;
    this.syntax = new CubicalSyntax(kernel);
    this.steps = 0;
    // Elaboration passes its own name supply and dimensions to each query;
    // these defaults serve inspection and other callers outside a source unit.
    this.names = new NameSupply({ taken: name => this.assumptions.has(name) });
    this.dimensions = new Map();
    this.assumptions = new Map();
    this.libraryAssumptions = new Map();
    this.assumptionLabels = new Map();
    this.assumptionOrigins = new Map();
    this.definitionViews = new Map();
    this.schemaSpecializations = new Map();
    this.schemaSourceNames = new Map();
    this.scopeDefinitions = new Set();
  }
  context(local = new Map()) { return new Map([...this.assumptions, ...local]); }
  assume(name, type, avoid = new Set()) {
    while (avoid.has(name) || this.kernel.names.has(name)) name += "_";
    const dimensions = this.dimensions;
    let checked;
    try { this.dimensions = new Map(); checked = this.infer(type); }
    finally { this.dimensions = dimensions; }
    if (this.nf(checked.type).tag !== "U") throw new Error("An assumption needs a checked type.");
    this.kernel.symbol(name);
    this.assumptions.set(name, type);
    return { tag: "Var", name };
  }
  requiredAssumptions(...terms) {
    const names = new Set();
    // Compute free names once per shared subtree. Removing the local binder
    // after visiting its body keeps this independent of the surrounding scope.
    const memo = new WeakMap();
    const free = term => {
      if (!term || typeof term !== "object") return new Set();
      if (memo.has(term)) return memo.get(term);
      const result = new Set();
      if (term.tag === "Var") result.add(term.name);
      else if (["Pi", "Lam", "Sigma", "W"].includes(term.tag)) {
        for (const name of free(term.domain)) result.add(name);
        for (const name of free(term.body)) if (name !== term.name) result.add(name);
      } else for (const child of Object.values(term)) for (const name of free(child)) result.add(name);
      memo.set(term, result); return result;
    };
    const visit = term => { for (const name of free(term)) names.add(name); };
    terms.forEach(visit);
    // Context types can depend on earlier assumptions; close that dependency set.
    for (const [name, type] of [...this.assumptions].reverse()) if (names.has(name)) visit(type);
    return new Map([...this.assumptions].filter(([name]) => names.has(name)));
  }
  // A type mismatch names both types in Cubist source syntax. The kernel's handles
  // are read at once, before any rollback can invalidate them.
  describeMismatch(error, dimensions) {
    if (error?.kind !== "mismatch" || !error.mismatch?.found || error.described) return error;
    error.described = true;
    try {
      const [found, expected] = [error.mismatch.found, error.mismatch.expected]
        .map(handle => this.displayText(this.syntax.decode(handle, dimensions)));
      error.message = `Type mismatch: found ${found}, expected ${expected}.`;
    } catch { /* Keep the kernel's message. */ }
    return error;
  }
  // Definitions show their source names, without the module prefix, and
  // assumptions their labels.
  get displayNames() {
    return this.displaySymbols ??= new Proxy({}, { get: (_, name) => typeof name !== "string" ? undefined
      : this.assumptionLabels.has(name) ? { name: this.assumptionLabels.get(name), kind: "axiom" }
      : name.includes("__") && !name.startsWith("__") ? { name: name.slice(name.indexOf("__") + 2) } : undefined });
  }
  displayText(term, width = 160) {
    const text = sourceText(displayTerm(term), this.displayNames);
    return text.length > width ? `${text.slice(0, width - 1)}…` : text;
  }
  // A goal, and the term a statement built for it, shown with one renaming,
  // so the context's names, the target and the term agree.
  // `print` is sourceText by default; cubicalText gives mathematical notation.
  // A derivation shows its terms as they are: `reduce` false keeps redexes.
  displayGoal(context, target, built = null, width = 400, print = null, reduce = true) {
    // Goals can share large terms; the printer stops after `width` nodes too.
    const printed = term => print ? print(term, this.displayNames) : sourceText(term, this.displayNames, width);
    const show = term => { const text = printed(term); return text.length > width ? `${text.slice(0, width - 1)}…` : text; };
    let chained = { tag: "Pair", first: target, second: built ?? { tag: "Point" } };
    for (const [name, type] of [...context].reverse()) chained = T.pi(name, type, chained);
    let shown = displayTerm(chained, reduce ? 256 : 0);
    const locals = [];
    while (locals.length < context.size && shown.tag === "Pi") {
      locals.push({ name: shown.name, type: show(shown.domain) });
      shown = shown.body;
    }
    return { locals, goal: show(shown.first), built: built ? show(shown.second) : null };
  }
  checkSyntax(term, expected, context, dimensions, describe = true) {
    try { return this.syntax.check(term, expected, [...this.context(context)], dimensions); }
    catch (error) { throw describe ? this.describeMismatch(error, dimensions) : error; }
  }
  infer(term, context = new Map(), dimensions = this.dimensions) {
    const checked = this.checkSyntax(term, null, context, dimensions);
    this.steps += checked.checkingSteps;
    return { term: checked.term, type: checked.type, native: { ok: true,
      arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes, unfoldingHints: [...this.kernel.unfoldingHints], axioms: [...this.requiredAssumptions(checked.term, checked.type).keys()] } };
  }
  check(term, expected, context = new Map(), dimensions = this.dimensions, describe = true) {
    const checked = this.checkSyntax(term, expected, context, dimensions, describe);
    this.steps += checked.checkingSteps;
    return checked.term;
  }
  ascribe(term, type, names = this.names) {
    // Application of the identity at the declared type retains that exact
    // signature in the kernel's inferred result. The next native check checks
    // the conversion; this is no unchecked annotation or new kernel rule.
    const name = names.fresh("ascription");
    return { tag: "App", fn: { tag: "Lam", name, domain: type, body: { tag: "Var", name } }, arg: term };
  }
  nf(term, dimensions = this.dimensions) {
    // Translator's nf calls ask for Pi/Sigma/Path heads, not full normal forms.
    return this.syntax.decode(this.kernel.head(this.syntax.encode(term, dimensions)), dimensions);
  }
  equal(left, right, context = new Map(), dimensions = this.dimensions, names = this.names) {
    const type = this.infer(left, context, dimensions).type;
    // This binder scopes over both terms. A generated name is not a live
    // coordinate, so it cannot capture one.
    const dim = names.fresh("conversion");
    const constant = { tag: "PLam", dim, family: type, body: left };
    const expected = { tag: "Path", dim, family: type, left, right };
    const result = this.attempt(constant, expected, context, dimensions);
    if (result.ok) return true;
    if (result.failure === "mismatch") return false;
    throw result.error;
  }
  // A speculative check answers with a value: {ok: true, term}, or
  // {ok: false, failure, error} when the kernel reports a type mismatch or
  // runs out of steps or time. Any other rejection throws, as in check().
  attempt(term, expected, context = new Map(), dimensions = this.dimensions) {
    // Speculative failures are answers, not diagnostics: they are not described.
    try { return { ok: true, term: this.check(term, expected, context, dimensions, false) }; }
    catch (error) {
      if (!speculativeFailures.has(error?.kind)) throw error;
      return { ok: false, failure: error.kind, error };
    }
  }
  expect(actual, expected, context = new Map(), dimensions = this.dimensions, names = this.names) {
    // Ask the kernel whether an arbitrary inhabitant of the actual type also
    // inhabits the expected type. This uses directed cumulative typing, while
    // equal() continues to ask for definitional equality.
    const name = names.fresh("expected");
    this.check({ tag: "Var", name }, expected, new Map(context).set(name, actual), dimensions);
  }
  define(name, term, type) {
    const assumptions = this.requiredAssumptions(term, type);
    let body = term, signature = type;
    for (const [parameter, domain] of [...assumptions].reverse()) {
      body = { tag: "Lam", name: parameter, domain, body };
      signature = { tag: "Pi", name: parameter, domain, body: signature };
    }
    let reference;
    try { reference = this.kernel.define(name, this.syntax.encode(body), this.syntax.encode(signature)); }
    catch (error) { throw this.describeMismatch(error, new Map()); }
    this.definitionViews.set(name, { term, type, assumptions, unfoldingHints: [...this.kernel.unfoldingHints] });
    let result = this.syntax.decode(reference);
    for (const parameter of assumptions.keys()) result = { tag: "App", fn: result, arg: { tag: "Var", name: parameter } };
    return result;
  }
  specializeSchema(name, levels, elaborate) {
    const key = `${name}__${levels.map(level => `U${level}`).join("_")}`;
    if (this.schemaSpecializations.has(key)) return this.schemaSpecializations.get(key);
    // A concrete universe instantiation is a closed function, even if it was
    // requested from inside another proof. Check and name that function once;
    // ordinary application still checks every subsequent argument and result.
    const term = elaborate(), checked = this.infer(term);
    const value = NativeCubicalElaborator.prototype.define.call(this, key, checked.term, checked.type);
    this.schemaSpecializations.set(key, value);
    return value;
  }
  scopedUnfolding(names, elaborate, context, expected = null, dimensions = this.dimensions, supply = this.names) {
    const expanded = new Set(names), visited = new Set(), syntaxSeen = new WeakSet();
    const visitTerm = term => {
      if (!term || typeof term !== "object" || syntaxSeen.has(term)) return;
      syntaxSeen.add(term);
      if (term.tag === "DefRef" && this.scopeDefinitions.has(term.name)) visitDefinition(term.name);
      Object.values(term).forEach(visitTerm);
    };
    const visitDefinition = name => {
      if (visited.has(name)) return;
      visited.add(name); expanded.add(name);
      visitTerm(this.definitionViews.get(name)?.term);
    };
    // A selected source definition includes its compiler-created blocks.
    // Otherwise that implementation detail would obstruct unfolding its body.
    // Other user definitions remain folded, and all references are checked.
    names.forEach(visitDefinition);
    return this.kernel.withUnfoldingHints([...this.kernel.unfoldingHints, ...expanded], () => {
      const raw = elaborate();
      const checked = expected ? { term: this.check(raw, expected, context, dimensions), type: expected }
        : this.infer(raw, context, dimensions);
      let term = checked.term, type = checked.type;
      // Close over local variables before interval coordinates: a variable's
      // type may itself depend on a coordinate. The helper is then checked as
      // an ordinary closed definition, not installed as an unchecked promise.
      for (const [name, domain] of [...context].reverse()) {
        term = T.lam(name, domain, term); type = T.pi(name, domain, type);
      }
      for (const dim of [...dimensions.keys()].reverse()) {
        term = T.line(dim, type, term);
        type = T.path(dim, type, T.at(term, I.zero), T.at(term, I.one));
      }
      this.kernel.unfoldingSerial = (this.kernel.unfoldingSerial ?? 0) + 1;
      const name = `${this.bindingName?.("unfolding") ?? "unfolding"}_${this.kernel.unfoldingSerial}`;
      let result = NativeCubicalElaborator.prototype.define.call(this, name, this.ascribe(term, type, supply), type);
      this.scopeDefinitions.add(name);
      for (const dim of dimensions.keys()) result = T.at(result, I.variable(dim));
      for (const name of context.keys()) result = T.app(result, T.variable(name));
      return result;
    });
  }

  verify(term, expected = null, assumptions = []) {
    const checked = this.checkSyntax(term, expected, new Map(assumptions), this.dimensions);
    const normal = this.syntax.decode(this.kernel.normalize(checked.expression), this.dimensions);
    return { ...checked, normal, native: { ok: true, arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes, unfoldingHints: [...this.kernel.unfoldingHints], axioms: [...this.requiredAssumptions(checked.term, checked.type).keys()] } };
  }
}
