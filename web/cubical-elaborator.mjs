import { CubicalSyntax } from "./cubical-syntax.mjs";
import { T } from "./dist/cubical-runtime/core.mjs";
import { interval as I } from "./dist/cubical-runtime/lattice.mjs";

// Elaboration queries use the native checker and demand only a type's outer
// constructor. JavaScript neither normalizes proofs nor approves conversions.
export class NativeCubicalElaborator {
  constructor(kernel) {
    this.kernel = kernel;
    this.syntax = new CubicalSyntax(kernel);
    this.steps = 0;
    this.serial = 0;
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
  infer(term, context = new Map()) {
    const checked = this.syntax.check(term, null, [...this.context(context)], this.dimensions);
    this.steps += checked.checkingSteps;
    return { term: checked.term, type: checked.type, native: { ok: true,
      arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes, unfoldingHints: [...this.kernel.unfoldingHints], axioms: [...this.requiredAssumptions(checked.term, checked.type).keys()] } };
  }
  check(term, expected, context = new Map()) {
    const checked = this.syntax.check(term, expected, [...this.context(context)], this.dimensions);
    this.steps += checked.checkingSteps;
    return checked.term;
  }
  ascribe(term, type) {
    // Application of the identity at the declared type retains that exact
    // signature in the kernel's inferred result. The next native check checks
    // the conversion; this is no unchecked annotation or new kernel rule.
    const name = `ascription${++this.serial}`;
    return { tag: "App", fn: { tag: "Lam", name, domain: type, body: { tag: "Var", name } }, arg: term };
  }
  nf(term) {
    // Translator's nf calls ask for Pi/Sigma/Path heads, not full normal forms.
    return this.syntax.decode(this.kernel.head(this.syntax.encode(term, this.dimensions)), this.dimensions);
  }
  equal(left, right, context = new Map()) {
    const type = this.infer(left, context).type;
    // This binder scopes over both terms, so it must not capture a live
    // coordinate; every free coordinate of a checked term is in scope here.
    let dim = `conversion${++this.serial}`;
    while (this.dimensions.has(dim)) dim += "_";
    const constant = { tag: "PLam", dim, family: type, body: left };
    const expected = { tag: "Path", dim, family: type, left, right };
    try { this.check(constant, expected, context); return true; }
    catch (error) {
      if (error.message === "Type mismatch.") return false;
      throw error;
    }
  }
  expect(actual, expected, context = new Map()) {
    // Ask the kernel whether an arbitrary inhabitant of the actual type also
    // inhabits the expected type. This uses directed cumulative typing, while
    // equal() continues to ask for definitional equality.
    let name = `expected${++this.serial}`;
    while (context.has(name) || this.assumptions.has(name)) name += "_";
    this.check({ tag: "Var", name }, expected, new Map(context).set(name, actual));
  }
  define(name, term, type) {
    const assumptions = this.requiredAssumptions(term, type);
    let body = term, signature = type;
    for (const [parameter, domain] of [...assumptions].reverse()) {
      body = { tag: "Lam", name: parameter, domain, body };
      signature = { tag: "Pi", name: parameter, domain, body: signature };
    }
    const reference = this.kernel.define(name, this.syntax.encode(body), this.syntax.encode(signature));
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
  scopedUnfolding(names, elaborate, context, expected = null) {
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
      const checked = expected ? { term: this.check(raw, expected, context), type: expected } : this.infer(raw, context);
      let term = checked.term, type = checked.type;
      // Close over local variables before interval coordinates: a variable's
      // type may itself depend on a coordinate. The helper is then checked as
      // an ordinary closed definition, not installed as an unchecked promise.
      for (const [name, domain] of [...context].reverse()) {
        term = T.lam(name, domain, term); type = T.pi(name, domain, type);
      }
      for (const dim of [...this.dimensions.keys()].reverse()) {
        term = T.line(dim, type, term);
        type = T.path(dim, type, T.at(term, I.zero), T.at(term, I.one));
      }
      this.kernel.unfoldingSerial = (this.kernel.unfoldingSerial ?? 0) + 1;
      const name = `${this.bindingName?.("unfolding") ?? "unfolding"}_${this.kernel.unfoldingSerial}`;
      let result = NativeCubicalElaborator.prototype.define.call(this, name, this.ascribe(term, type), type);
      this.scopeDefinitions.add(name);
      for (const dim of this.dimensions.keys()) result = T.at(result, I.variable(dim));
      for (const name of context.keys()) result = T.app(result, T.variable(name));
      return result;
    });
  }

  verify(term, expected = null, assumptions = []) {
    const checked = this.syntax.check(term, expected, [...this.context(new Map(assumptions))], this.dimensions);
    const normal = this.syntax.decode(this.kernel.normalize(checked.expression), this.dimensions);
    return { ...checked, normal, native: { ok: true, arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes, unfoldingHints: [...this.kernel.unfoldingHints], axioms: [...this.requiredAssumptions(checked.term, checked.type).keys()] } };
  }
}
