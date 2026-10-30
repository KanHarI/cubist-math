import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { forSource } from "../web/display-naming.mjs";
import { localName } from "../web/translator/names.mjs";
import { naturalSort as unat, numeral as number } from "../web/translator/numerals.mjs";

const U0 = { tag: "U", level: 0 }, unit = { tag: "Unit" }, v = { tag: "Void" };
const variable = name => ({ tag: "Var", name });
const pi = (name, domain, body) => ({ tag: "Pi", name, domain, body });
const sigma = (name, domain, body) => ({ tag: "Sigma", name, domain, body });
const sum = (left, right) => ({ tag: "Sum", left, right });
const app = (fn, ...args) => args.reduce((f, arg) => ({ tag: "App", fn: f, arg }), fn);
const succ = value => app({ tag: "Con", index: 1, sort: unat, name: "succ" }, value);
// The source UNat's eliminator applied, which prints as `induction`.
const induction = ({ motive, zero, step, value }) => app({ tag: "Elim", signature: "unat__UNat", motive, clauses: [zero, step] }, value);
const add = (a, b) => app({ tag: "DefRef", name: "unat__add" }, a, b);
const equal = (left, right) => ({ tag: "Path", dim: "i", family: unat, left, right });

test("types print as they are written, with only the parentheses the parser needs", () => {
  assert.equal(sourceText(sum(unit, sum(unit, unat))), "Unit or Unit or UNat");
  assert.equal(sourceText(sum(sum(unit, unit), unat)), "(Unit or Unit) or UNat");
  assert.equal(sourceText(pi("_", unat, pi("_", unat, unat))), "UNat -> UNat -> UNat");
  assert.equal(sourceText(pi("_", pi("_", unat, unat), unat)), "(UNat -> UNat) -> UNat");
  // `and` binds tighter than `or`, which binds tighter than `->`.
  assert.equal(sourceText(pi("_", sigma("_", unat, unit), sum(unit, v))), "UNat and Unit -> Unit or Void");
  assert.equal(sourceText(sigma("_", sum(unat, unit), unit)), "(UNat or Unit) and Unit");
  assert.equal(sourceText(pi("A", U0, pi("_", variable("A"), sigma("_", variable("A"), variable("A"))))),
    "forall A : U0. A -> A and A");
  assert.equal(sourceText(sigma("m", unat, app({ tag: "DefRef", name: "reference_example__lt" }, variable("n"), variable("m")))),
    "exists m : UNat. lt(n, m)");
  assert.equal(sourceText(pi("_", pi("n", unat, equal(variable("n"), variable("n"))), unit)), "(forall n : UNat. n = n) -> Unit");
});

// Where unat's notation is selected, as after use unat;. A scope's lookups
// say which notation each name selects (notationContext); a numeral prints
// abbreviated only where they establish it.
const scoped = identities => ({ reads: name => identities[name] ?? null, opens: () => false });
const unarySymbols = { unat__UNat: { printing: [{ notation: "unat", identity: "unary-view", identityNumeral: true }] } };
const unaryScope = scoped({ unat: "unary-view" });
const natText = term => sourceText(term, unarySymbols, 4000, { selection: "unat", selectionIdentity: "unary-view", ...unaryScope });

test("values and arithmetic print in source syntax", () => {
  assert.equal(natText(equal(add(number(2), number(2)), number(5))), "2 + 2 = 5");
  assert.equal(natText(add(add(number(1), number(2)), number(3))), "1 + 2 + 3");
  assert.equal(natText(add(number(1), add(number(2), number(3)))), "1 + (2 + 3)");
  assert.equal(natText(app({ tag: "DefRef", name: "unat__mul" }, add(number(1), number(2)), number(3))), "(1 + 2) * 3");
  assert.equal(natText(app({ tag: "DefRef", name: "unat__isLt" }, variable("n"), succ(variable("n")))), "n < succ(n)");
  assert.equal(natText({ tag: "Pair", first: number(3), second: { tag: "Pair", first: { tag: "Point" }, second: number(1) } }), "(3, tt, 1)");
  assert.equal(sourceText({ tag: "Inl", as: sum(unit, unat), value: { tag: "Point" } }), "left(tt)");
  assert.equal(natText({ tag: "Lam", name: "m", domain: unat, body: { tag: "Lam", name: "n", domain: unat,
    body: { tag: "Lam", name: "p", domain: unit, body: add(variable("m"), variable("n")) } } }), "fun (m, n : UNat, p : Unit) => m + n");
  assert.equal(natText(app({ tag: "Lam", name: "x", domain: unat, body: variable("x") }, number(1))), "(fun (x : UNat) => x)(1)");
  // Where nothing is selected, unat's operations and numerals are qualified,
  // so the text reads back (L2.10j).
  assert.equal(sourceText(equal(add(number(2), number(2)), number(5)), unarySymbols, 4000, unaryScope), "unat.(2 + 2) = unat.(5)");
  assert.equal(sourceText(add(variable("m"), variable("n"))), "unat.(m + n)");
  // Without a scope that establishes unat's notation, a numeral prints as
  // its constructors, which read back anywhere UNat's do.
  assert.equal(sourceText(number(2), unarySymbols), "succ(succ(zero))");
  assert.equal(sourceText(number(2), unarySymbols, 4000, scoped({ unat: "shadow" })), "succ(succ(zero))");
});

// Messages, evaluations and prints in source syntax are
// cubist-tests/source_text_messages.cubist (tests/cubist-tests.test.mjs).

test("paths print as equalities when their type does not vary, and path application as @", () => {
  const p = variable("p");
  const at = arg => ({ tag: "PApp", path: p, arg });
  assert.equal(sourceText(equal(at([["i:1"]]), at([]))), "p @ i = p @ 0");
  // Coordinates print in the source's notation: ~i, & and |.
  assert.equal(sourceText(at([["i:0", "j:1"]])), "p @ ~i & j");
  assert.equal(sourceText(at([["i:1"], ["j:1"]])), "p @ i | j");
  assert.equal(sourceText(at([["i:1", "j:1"], ["k:0"]])), "p @ i & j | ~k");
  assert.equal(sourceText(at([[]])), "p @ 1");
  const varying = { tag: "Path", dim: "i", family: { tag: "PApp", path: variable("q"), arg: [["i:1"]] }, left: variable("a"), right: variable("b") };
  assert.doesNotMatch(sourceText(varying), / = /);
  // A path prints as path i => …, and one that does not vary as refl.
  const line = { tag: "PLam", dim: "i", family: variable("A"), body: at([["i:1"]]) };
  assert.equal(sourceText(line), "path i => p @ i");
  assert.equal(sourceText({ tag: "PLam", dim: "i", family: variable("A"), body: variable("x") }), "refl(x)");
});

test("binary-natural normal forms print only through a known reader", () => {
  const constructor = (type, index, name) => ({ tag: "Con", index, name, sort: { tag: "Sort", signature: `bnat__${type}` } });
  const zero = constructor("BNat", 0, "b_zero"), positive = p => app(constructor("BNat", 1, "b_positive"), p);
  const one = constructor("BPositive", 0, "bp_one");
  const odd = p => app(constructor("BPositive", 2, "bp_odd"), p);
  const symbols = { bnat_notation__bnat_literal: { printing: [{ notation: "bnat", identity: "bnat-reader", literal: true }] } };
  const scope = scoped({ bnat: "bnat-reader" });
  assert.equal(sourceText(zero), "b_zero");
  assert.equal(sourceText(positive(one), {}, 4000, { selection: "bnat", ...scope }), "b_positive(bp_one)");
  assert.equal(sourceText(zero, symbols, 4000, scope), "bnat.(0)");
  assert.equal(sourceText(positive(one), symbols, 4000, { selection: "unat", ...scope }), "bnat.(1)");
  assert.equal(sourceText(positive(odd(one)), symbols, 4000, { selection: "bnat", selectionIdentity: "bnat-reader", ...scope }), "3");
  assert.equal(sourceText(positive(variable("p")), symbols, 4000, scope), "b_positive(p)");
  assert.equal(sourceText(positive(odd(variable("p"))), symbols, 4000, scope), "b_positive(bp_odd(p))");
  const unrelated = { other__parse: { printing: [{ notation: "bnat", identity: "bnat-reader", literal: true }] } };
  assert.equal(sourceText(zero, unrelated, 4000, { selection: "bnat", selectionIdentity: "bnat-reader", ...scope }), "b_zero");
  // Without a scope, or where bnat names another notation, the reader cannot
  // be established, and the value prints as its constructors.
  assert.equal(sourceText(zero, symbols), "b_zero");
  assert.equal(sourceText(positive(odd(one)), symbols, 4000, scoped({ bnat: "shadow" })), "b_positive(bp_odd(bp_one))");
});

test("recursion and case analysis print as induction and match", () => {
  const recursion = { motive: { tag: "Lam", name: "b", domain: unat, body: unat }, zero: variable("n"),
    step: { tag: "Lam", name: "k", domain: unat, body: { tag: "Lam", name: "h", domain: unat, body: succ(variable("h")) } },
    value: variable("m") };
  // The motive's variable and the predecessor print as one name, `as k`,
  // where forSource named them alike (display-naming.mjs,
  // inductionBinders); unnamed, they print as they are.
  const named = term => forSource([term], { definitions: { type: () => null, value: () => null, label: localName },
    symbols: {}, dimensions: [], reduce: 0 })[0];
  // A constant motive, and a successor clause that does not use the
  // predecessor, need no `as`.
  assert.equal(sourceText(named(induction(recursion))), "induction m return UNat { zero => n; succ h => succ(h); }");
  assert.match(sourceText(induction(recursion)), /^unat__UNat\.elim\(/);
  const predecessor = { ...recursion, step: { ...recursion.step, body: { ...recursion.step.body, body: variable("k") } } };
  assert.equal(sourceText(named(induction(predecessor))), "induction m as k return UNat { zero => n; succ h => k; }");
  // The motive's variable reads as the name `as` binds.
  const dependent = { ...recursion, motive: { tag: "Lam", name: "b", domain: unat, body: equal(variable("b"), variable("b")) } };
  assert.match(sourceText(named(induction(dependent))), /^induction m as k return k = k \{/);
  const cases = { tag: "SumRec", motive: { tag: "Lam", name: "z", domain: sum(unit, unit), body: U0 },
    left: { tag: "Lam", name: "a", domain: unit, body: unat }, right: { tag: "Lam", name: "b", domain: unit, body: unit }, value: variable("v") };
  // As the linter asks, `as z` is written only where the return type uses z.
  assert.equal(sourceText(cases), "match v return U0 { left a => UNat; right b => Unit; }");
  const dependentCases = { ...cases, motive: { ...cases.motive, body: equal(variable("z"), variable("z")) } };
  assert.match(sourceText(dependentCases), /^match v as z return z = z \{ left a => /);
  assert.equal(natText(named(add(induction(recursion), number(1)))), "(induction m return UNat { zero => n; succ h => succ(h); }) + 1");
});

test("messages name unnamed dimensions once, keep sharing, and avoid the names they show", async () => {
  const { readableDimensions, displayTerm } = await import("../web/cubical-elaborator.mjs");
  // A compact shared type: each level uses the one below twice.
  let shared = { tag: "PApp", path: variable("p"), arg: [["d0:1"]] };
  for (let depth = 0; depth < 60; depth++) shared = { tag: "App", fn: shared, arg: shared };
  const [renamed] = readableDimensions([shared], []);
  assert.equal(renamed.fn, renamed.arg, "shared subterms stay shared");
  // i2 is shown as i: the dimension takes another name.
  const line = { tag: "PLam", dim: "d0", family: variable("A"), body: { tag: "PApp", path: variable("i2"), arg: [["d0:1"]] } };
  assert.equal(sourceText(readableDimensions([displayTerm(line)], [])[0]), "path j => i @ j");
  // A declared type named i, shown without its module: the dimension is j.
  const typed = { tag: "PLam", dim: "d0", family: variable("A"),
    body: { tag: "App", fn: { tag: "PApp", path: variable("p"), arg: [["d0:1"]] }, arg: { tag: "Sort", signature: "main__i", parameters: [], levels: [] } } };
  assert.equal(sourceText(readableDimensions([displayTerm(typed)], [])[0], { main__i: { name: "i" } }), "path j => (p @ j)(i)");
  // Seven dimensions in two terms: one renaming for both, past the letters.
  const at = (...dims) => ({ tag: "PApp", path: variable("p"), arg: [dims.map(d => `d${d}:1`)] });
  const [found, expected] = readableDimensions([at(0, 6), at(1, 2, 3, 4, 5, 6)], []);
  assert.equal(sourceText(found), "p @ i & i1");
  assert.equal(sourceText(expected), "p @ j & k & l & m & n & i1");
});

test("Glue, glue and unglue print as the source writes them", () => {
  const A = variable("A"), e = variable("e"), g = variable("g");
  const G = { tag: "Glue", base: A, system: [
    { face: [["k:0"]], type: A, equiv: e },
    { face: [["k:1", "j:0"], ["i:1"]], type: A, equiv: e }] };
  assert.equal(sourceText(G), "Glue(A, face(k, 0, A, e), face_when(on(k, 1) and on(j, 0) or on(i, 1), A, e))");
  const unglued = { tag: "Unglue", as: G, value: g };
  assert.equal(sourceText(unglued), "unglue(g)");
  assert.equal(sourceText({ tag: "GlueTerm", as: G, base: unglued, system: [{ face: [["k:0"]], term: g }] }),
    "glue(unglue(g), face(k, 0, g))");
});
