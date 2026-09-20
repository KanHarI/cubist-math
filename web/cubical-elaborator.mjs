import { CubicalSyntax } from "./cubical-syntax.mjs";

// Elaboration queries use the native checker and demand only a type's outer
// constructor. JavaScript neither normalizes proofs nor approves conversions.
export class NativeCubicalElaborator {
  constructor(kernel) {
    this.kernel = kernel;
    this.syntax = new CubicalSyntax(kernel);
    this.steps = 0;
    this.serial = 0;
  }
  infer(term, context = new Map()) {
    const checked = this.syntax.check(term, null, [...context]);
    this.steps += checked.checkingSteps;
    return { term: checked.term, type: checked.type, native: { ok: true,
      arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes } };
  }
  check(term, expected, context = new Map()) {
    const checked = this.syntax.check(term, expected, [...context]);
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
    return this.syntax.decode(this.kernel.head(this.syntax.encode(term)));
  }
  equal(left, right, context = new Map()) {
    const type = this.infer(left, context).type, dim = `conversion${++this.serial}`;
    const constant = { tag: "PLam", dim, family: type, body: left };
    const expected = { tag: "Path", dim, family: type, left, right };
    try { this.check(constant, expected, context); return true; }
    catch { return false; }
  }
  expect(actual, expected, context = new Map()) {
    const a = this.nf(actual), b = this.nf(expected);
    if (a.tag === "U" && b.tag === "U" && a.level <= b.level) return;
    if (!this.equal(actual, expected, context)) throw new Error("Type mismatch.");
  }
  define(name, term, type) {
    const reference = this.kernel.define(name, this.syntax.encode(term), this.syntax.encode(type));
    return this.syntax.decode(reference);
  }
  verify(term, expected = null, assumptions = []) {
    const checked = this.syntax.check(term, expected, assumptions);
    const normal = this.syntax.decode(this.kernel.normalize(checked.expression));
    return { ...checked, normal, native: { ok: true, arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes } };
  }
}
