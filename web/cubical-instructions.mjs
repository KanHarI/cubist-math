// The instruction kernel's graphs (kernel/include/cubical_kernel.h): each
// method issues one instruction and returns the judgement it derived, and the
// readers expose the judgement graph and its context entries. Instructions
// check their side conditions in C; nothing here certifies anything.
import { KernelError } from "./cubical-kernel.mjs";

// cc_instruction, in order.
export const instructions = ["", "universe", "nat", "zero", "succ", "natElim", "unit", "point", "unitElim",
  "void", "abort", "sum", "inject", "sumElim", "variable", "pi", "lambda", "apply", "sigma", "pair", "first",
  "second", "domain", "family", "path", "pathLambda", "pathApply", "define", "lookup", "refl", "step", "replace",
  "eta", "side", "symmetry", "transitivity", "convert", "lift", "endpoint", "pathAt", "system", "systemTube", "comp", "systemOverlap",
  "pushout", "pushPoint", "pushPath", "pushElim", "w", "sup", "wElim", "hcomp", "trans",
  "glueBase", "gluePiece", "glueOverlap", "glue", "glueTermBase", "glueTermPiece", "glueTerm", "unglue"];
// THTH's names for the rules, for display.
export const ththNames = { universe: "UIntro", nat: "NatForm", zero: "NatIntroZ", succ: "NatIntroS",
  natElim: "NatElim", unit: "UnitForm", point: "UnitIntro", unitElim: "UnitElim", void: "VoidForm",
  abort: "VoidElim", sum: "SumForm", inject: "SumIntro", sumElim: "SumElim", variable: "Vble", pi: "PiForm",
  lambda: "PiIntro", apply: "PiElim", sigma: "SigmaForm", pair: "SigmaIntro", first: "SigmaFst",
  second: "SigmaSnd", domain: "Domain", family: "Family", path: "PathForm", pathLambda: "PathIntro",
  pathApply: "PathElim", define: "Def", lookup: "DefLookup", refl: "DefEqRefl", step: "Step",
  replace: "HighSubs", eta: "Eta", side: "DefEqExt", symmetry: "DefEqSwp", transitivity: "DefEqTrans",
  convert: "Conv", lift: "Lift", endpoint: "Endpoint", pathAt: "PathElim", system: "CompBase", systemTube: "CompTube",
  comp: "Comp", systemOverlap: "CompOverlap", pushout: "PushoutForm", pushPoint: "PushoutIntro",
  pushPath: "PushoutPath", pushElim: "PushoutElim", w: "WForm", sup: "WIntro", wElim: "WElim",
  hcomp: "HComp", trans: "Transp", glueBase: "GlueBase", gluePiece: "GluePiece", glueOverlap: "GlueOverlap",
  glue: "GlueForm", glueTermBase: "GlueIntroBase", glueTermPiece: "GlueIntroPiece", glueTerm: "GlueIntro",
  unglue: "GlueElim" };
export const stepRules = ["", "beta", "delta", "iota", "path", "normalize", "whnf", "face"];
// A judgement's sides: its term, an equality's other term, its type.
export const sides = ["term", "other", "type"];
const EXTEND = 100, DIMENSION = 101;

const side = value => {
  const index = typeof value === "number" ? value : sides.indexOf(value);
  if (index < 0 || index > 2) throw new TypeError(`Unknown judgement side: ${value}`);
  return index;
};

export class InstructionGraph {
  constructor(kernel) {
    this.kernel = kernel;
    this.module = kernel.module;
  }
  issue(name, ...operands) {
    this.kernel.assertOpen();
    const code = typeof name === "number" ? name : instructions.indexOf(name);
    while (operands.length < 4) operands.push(0);
    const id = this.module._cb_instr(this.kernel.handle, code, ...operands.map(operand => operand >>> 0)) >>> 0;
    if (!id) {
      const error = this.kernel.failure(`${name} failed.`);
      this.module._cb_clear_error(this.kernel.handle);
      throw error;
    }
    return id;
  }
  position(path) {
    this.module._cb_position_clear(this.kernel.handle);
    for (const child of path)
      if (!this.module._cb_position_push(this.kernel.handle, child)) throw new KernelError("Invalid position.");
  }
  universe(level) { return this.issue("universe", level); }
  nat() { return this.issue("nat"); }
  zero() { return this.issue("zero"); }
  succ(n) { return this.issue("succ", n); }
  natElim(motive, zero, step, value) { return this.issue("natElim", motive, zero, step, value); }
  unit() { return this.issue("unit"); }
  point() { return this.issue("point"); }
  unitElim(motive, point, value) { return this.issue("unitElim", motive, point, value); }
  void() { return this.issue("void"); }
  abort(type, impossible) { return this.issue("abort", type, impossible); }
  sum(left, right) { return this.issue("sum", left, right); }
  inject(type, value, right) { return this.issue("inject", type, value, right ? 1 : 0); }
  sumElim(motive, left, right, value) { return this.issue("sumElim", motive, left, right, value); }
  extend(type, name) { return this.issue(EXTEND, type, this.kernel.symbol(name)); }
  dimension(index) { return this.issue(DIMENSION, index); }
  variable(entry) { return this.issue("variable", entry); }
  pi(entry, codomain) { return this.issue("pi", entry, codomain); }
  lambda(entry, body) { return this.issue("lambda", entry, body); }
  apply(fn, argument) { return this.issue("apply", fn, argument); }
  sigma(entry, family) { return this.issue("sigma", entry, family); }
  pair(type, first, second) { return this.issue("pair", type, first, second); }
  first(pair) { return this.issue("first", pair); }
  second(pair) { return this.issue("second", pair); }
  domain(type) { return this.issue("domain", type); }
  family(type, argument) { return this.issue("family", type, argument); }
  path(dimension, family, left, right) { return this.issue("path", dimension, family, left, right); }
  pathLambda(dimension, body) { return this.issue("pathLambda", dimension, body); }
  pathApply(path, dimension, endpoint = 0) { return this.issue("pathApply", path, dimension, endpoint); }
  endpoint(judgement, dimension, endpoint) { return this.issue("endpoint", judgement, dimension, endpoint); }
  pathAt(path, formula) { return this.issue("pathAt", path, formula); }
  system(dimension, family, base) { return this.issue("system", dimension, family, base); }
  systemTube(system, face, tube, adjacency) { return this.issue("systemTube", system, face, tube, adjacency); }
  // The last tube agrees with the tube at `position` where their faces meet.
  systemOverlap(system, position, agreement) { return this.issue("systemOverlap", system, position, agreement); }
  comp(system) { return this.issue("comp", system); }
  hcomp(system) { return this.issue("hcomp", system); }
  trans(system, face) { return this.issue("trans", system, face); }
  glueBase(base) { return this.issue("glueBase", base); }
  gluePiece(system, face, type, equivalence) { return this.issue("gluePiece", system, face, type, equivalence); }
  glueOverlap(system, position, types, equivalences) { return this.issue("glueOverlap", system, position, types, equivalences); }
  glue(system) { return this.issue("glue", system); }
  glueTermBase(type, base) { return this.issue("glueTermBase", type, base); }
  glueTermPiece(system, value, image) { return this.issue("glueTermPiece", system, value, image); }
  glueTerm(system) { return this.issue("glueTerm", system); }
  unglue(value) { return this.issue("unglue", value); }
  pushout(source, left, right, maps) { return this.issue("pushout", source, left, right, maps); }
  pushPoint(type, value, right) { return this.issue("pushPoint", type, value, right ? 1 : 0); }
  pushPath(type, value, interval) { return this.issue("pushPath", type, value, interval); }
  pushElim(motive, left, right, bridge) { return this.issue("pushElim", motive, left, right, bridge); }
  w(entry, arities) { return this.issue("w", entry, arities); }
  sup(type, label, children) { return this.issue("sup", type, label, children); }
  wElim(motive, step, value) { return this.issue("wElim", motive, step, value); }
  define(name, closed) { return this.issue("define", this.kernel.symbol(name), closed); }
  lookup(reference) { return this.issue("lookup", reference); }
  refl(typing) { return this.issue("refl", typing); }
  // Contract the redex at `path` in a side of a judgement, by `rule`.
  step(judgement, where, path, rule) {
    const code = stepRules.indexOf(rule);
    if (code < 1) throw new TypeError(`Unknown step rule: ${rule}`);
    this.position(path);
    return this.issue("step", judgement, side(where), code);
  }
  // Replace the subterm at `path` in a side of a judgement by the right side
  // of the equality `by`, whose left side it is.
  replace(judgement, where, path, by) {
    this.position(path);
    return this.issue("replace", judgement, side(where), by);
  }
  eta(typing) { return this.issue("eta", typing); }
  side(equality, which) { return this.issue("side", equality, side(which)); }
  symmetry(equality) { return this.issue("symmetry", equality); }
  transitivity(first, second) { return this.issue("transitivity", first, second); }
  convert(typing, equality) { return this.issue("convert", typing, equality); }
  lift(typing, type) { return this.issue("lift", typing, type); }

  // A search aid, never evidence: whether the term checker's conversion finds
  // two terms equal within `steps`; null when it could not tell.
  convertible(a, b, steps = 0) {
    const answer = this.module._cb_convertible(this.kernel.handle, a, b, steps);
    return answer === 2 ? null : answer === 1;
  }
  // Syntax only: Equiv(a, b) as the Glue rules state it.
  equivType(a, b) {
    const type = this.module._cb_equiv_type(this.kernel.handle, a, b) >>> 0;
    if (!type) throw new Error("Could not build an equivalence type.");
    return type;
  }
  // Syntax only, for the same search: a free name or dimension renamed.
  rename(term, dimension, from, to) { return this.module._cb_rename(this.kernel.handle, term, dimension ? 1 : 0, from, to) >>> 0; }
  get count() { return this.module._cb_judgement_count(this.kernel.handle) >>> 0; }
  get entryCount() { return this.module._cb_entry_count(this.kernel.handle) >>> 0; }
  // A judgement: its statement, the instruction that derived it, and its
  // context entries in creation order.
  judgement(id) {
    const field = index => this.module._cb_judgement(this.kernel.handle, id, index) >>> 0;
    const kind = field(0);
    if (!kind) throw new Error(`Unknown judgement ${id}.`);
    const rule = instructions[field(4)];
    const depth = field(12);
    const context = [];
    for (let index = 0, entry; (entry = this.module._cb_judgement_context(this.kernel.handle, id, index) >>> 0); index++)
      context.push(entry);
    const judgement = { id, kind: ["", "typing", "equality", "system"][kind], term: field(1), type: field(3), rule,
      premises: [5, 6, 7, 8].map(field).filter(Boolean), entry: field(9), operands: [field(10), field(11)], context };
    if (kind === 2) judgement.other = field(2);
    if (rule === "step" || rule === "replace") {
      judgement.side = sides[judgement.operands[0]];
      judgement.position = Array.from({ length: depth }, (_, index) => field(13 + index));
      if (rule === "step") judgement.stepRule = stepRules[judgement.operands[1]];
    }
    return judgement;
  }
  entry(id) {
    const field = index => this.module._cb_entry(this.kernel.handle, id, index) >>> 0;
    const dimension = !!field(2), symbol = field(0);
    if (!dimension && !symbol) throw new Error(`Unknown context entry ${id}.`);
    return { id, dimension, symbol, name: dimension ? `d${symbol}` : this.kernel.symbolName(symbol),
      type: field(1), source: field(3) };
  }
}
