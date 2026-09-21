import { CubicalSyntax } from "./cubical-syntax.mjs";

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
    this.definitionViews = new Map();
    this.schemaSpecializations = new Map();
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
    const visit = (term, bound = new Set()) => {
      if (!term || typeof term !== "object") return;
      if (term.tag === "Var") { if (!bound.has(term.name)) names.add(term.name); return; }
      if (["Pi", "Lam", "Sigma", "W"].includes(term.tag)) {
        visit(term.domain, bound); visit(term.body, new Set(bound).add(term.name)); return;
      }
      Object.values(term).forEach(value => visit(value, bound));
    };
    terms.forEach(term => visit(term));
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
    const type = this.infer(left, context).type, dim = `conversion${++this.serial}`;
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

  verify(term, expected = null, assumptions = []) {
    const checked = this.syntax.check(term, expected, [...this.context(new Map(assumptions))], this.dimensions);
    const normal = this.syntax.decode(this.kernel.normalize(checked.expression), this.dimensions);
    return { ...checked, normal, native: { ok: true, arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes, unfoldingHints: [...this.kernel.unfoldingHints], axioms: [...this.requiredAssumptions(checked.term, checked.type).keys()] } };
  }
}
