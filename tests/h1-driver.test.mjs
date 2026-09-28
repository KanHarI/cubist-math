// Declared types (H1) through the untrusted driver, work-plan K2.3
// (docs/roadmaps/h1-signature-specification.md, section 6): admission from a
// normal form, the syntax codec, instances whose parameters are converted to
// their telescope types, constructors, eliminators whose clauses are
// converted to their clause types, and the conversion search: Iota, the path
// step at an endpoint, Whnf on a formal composition, and the guide's answers
// for distinct constructors.
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { CubicalDeclarationTransaction } from "../web/cubical-transaction.mjs";
import { admitSignature, modifierCode } from "../web/cubical-signatures.mjs";
import { cubicalText } from "../web/cubical-notation.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";

const module = await createCubical();

const v = name => ({ tag: "Var", name });
const U = level => ({ tag: "U", level });
const pi = (name, domain, body) => ({ tag: "Pi", name, domain, body });
const lam = (name, domain, body) => ({ tag: "Lam", name, domain, body });
const app = (fn, ...args) => args.reduce((f, arg) => ({ tag: "App", fn: f, arg }), fn);
const sort = (signature, parameters = [], levels = []) => ({ tag: "Sort", signature, parameters, levels });
const con = (instance, index) => ({ tag: "Con", index, sort: instance });
const elim = (signature, motive, clauses) => ({ tag: "Elim", signature, motive, clauses });
const path = (family, left, right) => ({ tag: "Path", dim: "i", family, left, right });
const line = (family, body) => ({ tag: "PLam", dim: "i", family, body });
const at = (p, dimension) => ({ tag: "PApp", path: p, arg: [[`${dimension}:1`]] });
const atEnd = (p, end) => ({ tag: "PApp", path: p, arg: end ? [[]] : [] });

// inductive N { zero; succ(n : N); }
const natural = { name: "N", constructors: [{ name: "zero", type: v("N") }, { name: "succ", type: pi("n", v("N"), v("N")) }] };
const N = sort("N"), zero = con(N, 0), succ = n => app(con(N, 1), n);
const numeral = k => k ? succ(numeral(k - 1)) : zero;
// inductive List(U < UU0, A : U) : U { nil; cons(x : A, xs : List); }
const list = { name: "List", levels: [{ name: "U" }], parameters: [{ name: "A", type: U(v("U")) }], level: v("U"),
  constructors: [{ name: "nil", type: v("List") }, { name: "cons", type: pi("x", v("A"), pi("xs", v("List"), v("List"))) }] };
// inductive Plus(U < UU0, A, B : U) : U { inl(a : A); inr(b : B); }
const plus = { name: "Plus", levels: [{ name: "U" }], parameters: [{ name: "A", type: U(v("U")) }, { name: "B", type: U(v("U")) }],
  level: v("U"), constructors: [{ name: "inl", type: pi("a", v("A"), v("Plus")) }, { name: "inr", type: pi("b", v("B"), v("Plus")) }] };
// inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }, its level recorded.
const pointed = { name: "Pointed", levels: [{ name: "U", recorded: true }], level: { tag: "LSucc", count: 1, level: v("U") },
  constructors: [{ name: "pt", type: pi("X", U(v("U")), pi("x", v("X"), v("Pointed"))) }] };
// inductive Trunc(U < UU0, A : U) : prop { point(a : A); }
const trunc = { name: "Trunc", levels: [{ name: "U" }], parameters: [{ name: "A", type: U(v("U")) }], level: v("U"),
  modifier: "prop", constructors: [{ name: "point", type: pi("a", v("A"), v("Trunc")) }] };
// inductive At(U < UU0, A : U, a : A) : U { here; }: a parameter whose type
// is an earlier parameter, not a universe.
const atPoint = { name: "At", levels: [{ name: "U" }], parameters: [{ name: "A", type: U(v("U")) }, { name: "a", type: v("A") }],
  level: v("U"), constructors: [{ name: "here", type: v("At") }] };
// inductive S1 { base; loop : base = base; }
const circle = { name: "S1", constructors: [{ name: "base", type: v("S1") },
  { name: "loop", type: path(v("S1"), v("base"), v("base")) }] };
const S1 = sort("S1"), base = con(S1, 0), loop = con(S1, 1);

function session(t) {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  kernel.setExtensions({ h1: true });
  const syntax = new CubicalSyntax(kernel), driver = new InstructionDriver(kernel);
  const admit = spec => admitSignature(kernel, spec, { syntax, driver });
  const context = assumptions => assumptions.map(([name, type]) => [kernel.symbol(name), syntax.encode(type)]);
  const check = (term, type, assumptions = []) =>
    driver.check(syntax.encode(term), syntax.encode(type), context(assumptions));
  // The step rules of the judgements a check derives.
  const steps = (...args) => {
    const before = driver.graph.count;
    check(...args);
    const rules = new Set();
    for (let id = before; id < driver.graph.count; id++) {
      const j = driver.graph.judgement(id);
      if (j.rule === "step") rules.add(j.stepRule);
    }
    return rules;
  };
  return { kernel, syntax, driver, g: driver.graph, admit, check, steps };
}

test("the modifier codes are the kernel's: 0 untruncated, n + 2 for trunc(n)", () => {
  assert.deepEqual(["type", "prop", "set", { trunc: 1 }, { trunc: 14 }, undefined].map(modifierCode), [0, 1, 2, 3, 16, 0]);
  assert.throws(() => modifierCode({ trunc: -2 }), /n ≥ -1/);
  assert.throws(() => modifierCode({ trunc: 1.5 }), /n ≥ -1/);
  // Levels past the kernel's bound are refused before they reach an
  // instruction, where 2^32 - 2 + 2 would have wrapped to 0, untruncated.
  for (const n of [15, 4294967294, 4294967295]) assert.throws(() => modifierCode({ trunc: n }), /up to n = 14/);
});

test("an instruction refuses an operand that is not a 32-bit unsigned integer", t => {
  const { g, syntax, admit } = session(t);
  admit(natural);
  const u0 = g.universe(syntax.encodeLevel(0));
  for (const modifier of [2 ** 32, 2 ** 32 + 1, -1, 1.5])
    assert.throws(() => g.signatureBegin(u0, modifier, "Wrapped"), /32-bit unsigned integer/);
  assert.throws(() => g.construct(g.sortBegin(1), 2 ** 32), /32-bit unsigned integer/);
});

test("admission derives a signature from its normal form and registers it by name", t => {
  const { kernel, admit } = session(t);
  const n = admit(natural);
  assert.equal(kernel.signatures.get("N"), n);
  assert.deepEqual(n.constructors, ["zero", "succ"]);
  assert.equal(kernel.signature(n.index).admitted, true);
  // A truncation gets its generated squash, named for inspection.
  const tr = admit(trunc);
  assert.deepEqual(tr.constructors, ["point", "squash"]);
  assert.equal(kernel.signature(tr.index).modifier, 1);
  assert.throws(() => admit(natural), /already exists/);
  // The kernel still checks positivity: the sort in an arity's domain.
  assert.throws(() => admit({ name: "Bad", constructors: [{ name: "bad", type: pi("f", pi("x", v("Bad"), v("N")), v("Bad")) }] }));
  assert.equal(kernel.signatures.has("Bad"), false);
});

// R5: the codec's round trip.
test("the codec round-trips instances, constructors and eliminators, with their names", t => {
  const { syntax, admit } = session(t);
  // A decoded object is cached with its handle: a copy is encoded afresh,
  // from its fields, so a wrong field gives another handle.
  const again = term => syntax.encode(JSON.parse(JSON.stringify(term)));
  admit(natural);
  admit(list);
  const two = numeral(2);
  const decoded = syntax.decode(syntax.encode(two));
  assert.equal(decoded.fn.name, "succ");
  assert.deepEqual(decoded.fn.sort, { tag: "Sort", signature: "N", parameters: [], levels: [] });
  assert.equal(again(decoded), syntax.encode(two));
  const listN = sort("List", [N]);
  const cons = app(con(listN, 1), zero, con(listN, 0));
  assert.equal(again(syntax.decode(syntax.encode(cons))), syntax.encode(cons));
  const double = elim("N", lam("z", N, N), [zero, lam("m", N, lam("h", N, succ(succ(v("h")))))]);
  const back = syntax.decode(syntax.encode(double));
  assert.equal(back.signature, "N");
  assert.equal(back.clauses.length, 2);
  assert.equal(again(back), syntax.encode(double));
  assert.throws(() => syntax.encode(sort("Nope")), /Unknown declared type: Nope/);
  assert.throws(() => syntax.encode({ tag: "Con", sort: N }), /needs its number/);
});

test("constructors check at their instances, and parameters are converted to their telescope types", t => {
  const { kernel, g, syntax, driver, admit, check } = session(t);
  admit(natural);
  admit(list);
  admit(plus);
  admit(pointed);
  const judged = check(numeral(2), N);
  assert.equal(g.judgement(judged).term, syntax.encode(numeral(2)), "the derived term is the source's");
  const listN = sort("List", [N]);
  check(app(con(listN, 1), zero, con(listN, 0)), listN);
  // A parameter whose type is a redex: it is reduced to U(…) to read the
  // erased level, and converted to the telescope's type.
  const redex = app(lam("X", U(1), v("X")), U(0));
  check(con(sort("List", [v("B")]), 0), sort("List", [v("B")]), [["B", redex]]);
  // A parameter typed by an earlier one: b : (λ X. X)(N) is converted to N.
  admit(atPoint);
  const atB = sort("At", [N, v("b")]);
  check(con(atB, 0), atB, [["b", app(lam("X", U(0), v("X")), N)]]);
  assert.throws(() => check(con(sort("At", [N, v("b")]), 0), atB, [["b", U(0)]]), /Type mismatch/);
  // Plus(N, U0): the erased level is read from both parameters, U0 and U1;
  // N is lifted to U1, so the instance lives in U1.
  const mixed = sort("Plus", [N, U(0)]);
  const instance = driver.infer(syntax.encode(mixed));
  assert.deepEqual(syntax.decode(g.judgement(instance).type), U(1));
  check(app(con(mixed, 1), N), mixed);
  // A recorded level is carried: Pointed{0} lives in U1, and differs from Pointed{1}.
  const p0 = sort("Pointed", [], [0]), p1 = sort("Pointed", [], [1]);
  assert.deepEqual(syntax.decode(g.judgement(driver.infer(syntax.encode(p0))).type), U(1));
  check(app(con(p0, 0), N, zero), p0);
  assert.throws(() => check(app(con(p0, 0), N, zero), p1), /Type mismatch/);
  // A constructor's argument of the wrong type, and a wrong number of parameters.
  assert.throws(() => check(succ(con(listN, 0)), N), /Type mismatch/);
  assert.throws(() => check(sort("List"), U(0)), /each of its signature's parameters/);
  assert.equal(kernel.signatures.size, 5);
});

test("an eliminator computes on constructors, by Iota steps the search takes", t => {
  const { syntax, driver, admit, check, steps } = session(t);
  admit(natural);
  // double = elim_{λ z. N}[zero, λ m h. succ(succ(h))]: each clause is
  // converted to its clause type, M(zero) and Π (n : N). Π (h : M(n)). M(succ(n)).
  const double = elim("N", lam("z", N, N), [zero, lam("m", N, lam("h", N, succ(succ(v("h")))))]);
  check(app(double, numeral(2)), N);
  assert.ok(steps(line(N, numeral(4)), path(N, app(double, numeral(2)), numeral(4))).has("iota"));
  assert.throws(() => check(line(N, numeral(3)), path(N, app(double, numeral(2)), numeral(3))), /Type mismatch/);
  // A dependent motive: the clause for succ sees the motive at succ(n).
  const P = lam("z", N, path(N, v("z"), v("z")));
  const refls = elim("N", P, [line(N, zero), lam("m", N, lam("h", path(N, v("m"), v("m")), line(N, succ(v("m")))))]);
  check(app(refls, numeral(1)), path(N, numeral(1), numeral(1)));
  // A clause at the wrong type is refused.
  assert.throws(() => check(elim("N", lam("z", N, N), [zero, lam("m", N, v("m"))]), pi("z", N, N)), /Type mismatch/);
  // The guide: distinct constructors differ, and equal computations agree.
  // A constructor is not a rigid head: against a lambda it is eta's to
  // decide, and here the lambda's weak head is the constructor itself.
  const e = term => syntax.encode(term);
  assert.equal(driver.equal(e(zero), e(numeral(1)), null, null), false);
  assert.equal(driver.equal(e(numeral(1)), e(app(v("f"), zero)), null, null), false);
  assert.equal(driver.equal(e(app(double, numeral(1))), e(numeral(2)), null, null), true);
  assert.notEqual(driver.equal(e(con(N, 1)), e(lam("n", N, succ(v("n")))), null, null), false);
});

// N1: loop @ 0 and loop @ 1 are base.
test("a path constructor: its endpoints are its boundary, and an eliminator computes on it at a dimension", t => {
  const { admit, check, steps } = session(t);
  admit(natural);
  admit(circle);
  assert.ok(steps(line(S1, base), path(S1, atEnd(loop, 0), base)).has("path"));
  check(line(S1, base), path(S1, base, atEnd(loop, 1)));
  // Into N: base ↦ zero, loop ↦ the constant path at zero.
  const count = elim("S1", lam("z", S1, N), [zero, line(N, zero)]);
  assert.ok(steps(line(N, app(count, at(loop, "i"))), path(N, zero, zero)).has("iota"));
  check(line(N, zero), path(N, app(count, atEnd(loop, 1)), zero));
  // The loop clause must start and end at the base clause.
  assert.throws(() => check(elim("S1", lam("z", S1, N), [zero, line(N, numeral(1))]), pi("z", S1, N)), /Type mismatch/);
});

// E5: an eliminator on a formal composition.
test("the kernel's weak head computes an eliminator on a formal composition", t => {
  const { admit, check, steps } = session(t);
  admit(natural);
  admit(circle);
  const count = elim("S1", lam("z", S1, N), [zero, line(N, zero)]);
  const box = { tag: "HComp", dim: "j", family: S1, system: [], base };
  check(box, S1);
  assert.ok(steps(line(N, zero), path(N, app(count, box), zero)).has("whnf"));
  assert.throws(() => check(line(N, numeral(1)), path(N, app(count, box), numeral(1))), /Type mismatch/);
});

test("a rolled back declaration takes its signature with it; a committed one stays", t => {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  kernel.setExtensions({ h1: true });
  const syntax = new CubicalSyntax(kernel);
  const checker = { syntax, definitionViews: new Map(), genericDefinitions: new Map(), scopeDefinitions: new Map(), definitionExtensions: new Map(), inductives: new Map(),
    assumptions: new Map(), assumptionLabels: new Map(), assumptionOrigins: new Map(), libraryAssumptions: new Map() };
  let transaction = new CubicalDeclarationTransaction(kernel, checker);
  const { index } = admitSignature(kernel, natural, { syntax });
  transaction.finish(false);
  assert.equal(kernel.signatures.has("N"), false);
  assert.equal(kernel.signature(index).constructors.length, 0, "the kernel dropped it too");
  transaction = new CubicalDeclarationTransaction(kernel, checker);
  admitSignature(kernel, natural, { syntax });
  transaction.finish(true);
  assert.equal(kernel.signatures.has("N"), true);
  const driver = new InstructionDriver(kernel);
  assert.ok(driver.check(syntax.encode(numeral(1)), syntax.encode(N)));
});

test("displays name instances, constructors and eliminators as the source does", t => {
  const { syntax, admit } = session(t);
  admit(natural);
  admit(list);
  admit(pointed);
  const shown = term => syntax.decode(syntax.encode(term));
  const listN = sort("List", [N]);
  assert.equal(sourceText(shown(app(con(listN, 1), numeral(1), con(listN, 0)))), "cons(succ(zero), nil)");
  assert.equal(sourceText(shown(listN)), "List(N)");
  assert.equal(sourceText(shown(sort("Pointed", [], [0]))), "Pointed(U0)");
  assert.equal(cubicalText(shown(sort("Pointed", [], [1]))), "Pointed(U1)");
  const double = elim("N", lam("z", N, N), [zero, lam("m", N, lam("h", N, succ(succ(v("h")))))]);
  assert.equal(cubicalText(shown(app(double, zero))), "N.elim(λ (z : N). N, zero, λ (m : N). λ (h : N). succ(succ(h)))(zero)");
});

// N3: the torus's square, at its faces.
test("higher constructors: the torus and the sphere are admitted, and their faces compute", t => {
  const { admit, check } = session(t);
  // inductive Torus { b; p, q : b = b; surf : Path(i; Path(j; Torus, p @ i, p @ i), q, q); }
  const square = (family, left, right) => ({ tag: "Path", dim: "j", family, left, right });
  admit({ name: "Torus", constructors: [{ name: "b", type: v("Torus") },
    { name: "p", type: path(v("Torus"), v("b"), v("b")) }, { name: "q", type: path(v("Torus"), v("b"), v("b")) },
    { name: "surf", type: path(square(v("Torus"), at(v("p"), "i"), at(v("p"), "i")), v("q"), v("q")) }] });
  const T = sort("Torus"), b = con(T, 0), p = con(T, 1), q = con(T, 2), surf = con(T, 3);
  // The square's faces, compared as paths: surf @ 0 is q, and the path
  // i ↦ surf @ i @ 0 is p. Each is an equality of loops, inhabited by a
  // constant path only if the two loops are the same.
  const loops = path(T, b, b);
  const same = (x, y) => check({ tag: "PLam", dim: "k", family: loops, body: x }, { tag: "Path", dim: "k", family: loops, left: x, right: y });
  same(q, atEnd(surf, 0));
  same(q, atEnd(surf, 1));
  same(p, { tag: "PLam", dim: "i", family: T, body: { tag: "PApp", path: at(surf, "i"), arg: [] } });
  same(p, { tag: "PLam", dim: "i", family: T, body: { tag: "PApp", path: at(surf, "i"), arg: [[]] } });
  // The loops swapped are refused: the faces are not the other loops.
  assert.throws(() => same(p, atEnd(surf, 0)), /Type mismatch/);
  assert.throws(() => same(q, { tag: "PLam", dim: "i", family: T, body: { tag: "PApp", path: at(surf, "i"), arg: [] } }), /Type mismatch/);
  // inductive S2 { base; surf : Path(i; Path(j; S2, base, base), ⟨j⟩ base, ⟨j⟩ base); }
  const constant = { tag: "PLam", dim: "j", family: v("S2"), body: v("base") };
  admit({ name: "S2", constructors: [{ name: "base", type: v("S2") },
    { name: "surf", type: path(square(v("S2"), v("base"), v("base")), constant, constant) }] });
  const S2 = sort("S2");
  // surf @ 0 is ⟨j⟩ base, so surf @ 0 @ 1 is base.
  check(line(S2, con(S2, 0)), path(S2, atEnd(atEnd(con(S2, 1), 0), 1), con(S2, 0)));
  // A boundary naming a later constructor, or the sort in an arity, is refused.
  assert.throws(() => admit({ name: "Ahead", constructors: [{ name: "a", type: path(v("Ahead"), v("b"), v("b")) },
    { name: "b", type: v("Ahead") }] }), /Unbound variable b/);
});

test("an instance derives in a context whose variables share the signature's level names", t => {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  kernel.setExtensions({ h1: true });
  const syntax = new CubicalSyntax(kernel);
  const checker = { syntax, definitionViews: new Map(), genericDefinitions: new Map(), scopeDefinitions: new Map(), definitionExtensions: new Map(), inductives: new Map(),
    assumptions: new Map(), assumptionLabels: new Map(), assumptionOrigins: new Map(), libraryAssumptions: new Map() };
  const transaction = new CubicalDeclarationTransaction(kernel, checker);
  admitSignature(kernel, list, { syntax });
  transaction.finish(true);
  // List's level parameter is U; here U'1, the name a counter would pick
  // first for a renamed U, is a type of the caller's, and then U is.
  for (const name of ["U'1", "U"]) {
    const driver = new InstructionDriver(kernel), listU = sort("List", [v(name)]);
    const context = [[kernel.symbol(name), syntax.encode(U(0))]];
    assert.ok(driver.check(syntax.encode(con(listU, 0)), syntax.encode(listU), context));
    assert.ok(driver.check(syntax.encode(app(con(listU, 1), v("u"), con(listU, 0))), syntax.encode(listU),
      [...context, [kernel.symbol("u"), syntax.encode(v(name))]]));
  }
});
