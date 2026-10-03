import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { naturalSort as nat, numeral as number } from "../web/translator/numerals.mjs";

const U0 = { tag: "U", level: 0 }, unit = { tag: "Unit" }, v = { tag: "Void" };
const variable = name => ({ tag: "Var", name });
const pi = (name, domain, body) => ({ tag: "Pi", name, domain, body });
const sigma = (name, domain, body) => ({ tag: "Sigma", name, domain, body });
const sum = (left, right) => ({ tag: "Sum", left, right });
const app = (fn, ...args) => args.reduce((f, arg) => ({ tag: "App", fn: f, arg }), fn);
const succ = value => app({ tag: "Con", index: 1, sort: nat, name: "succ" }, value);
// The source Nat's eliminator applied, which prints as `induction`.
const induction = ({ motive, zero, step, value }) => app({ tag: "Elim", signature: "nat__Nat", motive, clauses: [zero, step] }, value);
const add = (a, b) => app({ tag: "DefRef", name: "naturals__add" }, a, b);
const equal = (left, right) => ({ tag: "Path", dim: "i", family: nat, left, right });

test("types print as they are written, with only the parentheses the parser needs", () => {
  assert.equal(sourceText(sum(unit, sum(unit, nat))), "Unit or Unit or Nat");
  assert.equal(sourceText(sum(sum(unit, unit), nat)), "(Unit or Unit) or Nat");
  assert.equal(sourceText(pi("_", nat, pi("_", nat, nat))), "Nat -> Nat -> Nat");
  assert.equal(sourceText(pi("_", pi("_", nat, nat), nat)), "(Nat -> Nat) -> Nat");
  // `and` binds tighter than `or`, which binds tighter than `->`.
  assert.equal(sourceText(pi("_", sigma("_", nat, unit), sum(unit, v))), "Nat and Unit -> Unit or Void");
  assert.equal(sourceText(sigma("_", sum(nat, unit), unit)), "(Nat or Unit) and Unit");
  assert.equal(sourceText(pi("A", U0, pi("_", variable("A"), sigma("_", variable("A"), variable("A"))))),
    "forall A : U0. A -> A and A");
  assert.equal(sourceText(sigma("m", nat, app({ tag: "DefRef", name: "reference_example__lt" }, variable("n"), variable("m")))),
    "exists m : Nat. lt(n, m)");
  assert.equal(sourceText(pi("_", pi("n", nat, equal(variable("n"), variable("n"))), unit)), "(forall n : Nat. n = n) -> Unit");
});

test("values and arithmetic print in source syntax", () => {
  assert.equal(sourceText(equal(add(number(2), number(2)), number(5))), "2 + 2 = 5");
  assert.equal(sourceText(add(add(number(1), number(2)), number(3))), "1 + 2 + 3");
  assert.equal(sourceText(add(number(1), add(number(2), number(3)))), "1 + (2 + 3)");
  assert.equal(sourceText(app({ tag: "DefRef", name: "naturals__mul" }, add(number(1), number(2)), number(3))), "(1 + 2) * 3");
  assert.equal(sourceText(app({ tag: "DefRef", name: "naturals__isLt" }, variable("n"), succ(variable("n")))), "n < succ(n)");
  assert.equal(sourceText({ tag: "Pair", first: number(3), second: { tag: "Pair", first: { tag: "Point" }, second: number(1) } }), "(3, tt, 1)");
  assert.equal(sourceText({ tag: "Inl", as: sum(unit, nat), value: { tag: "Point" } }), "left(tt)");
  assert.equal(sourceText({ tag: "Lam", name: "m", domain: nat, body: { tag: "Lam", name: "n", domain: nat,
    body: { tag: "Lam", name: "p", domain: unit, body: add(variable("m"), variable("n")) } } }), "fun (m, n : Nat, p : Unit) => m + n");
  assert.equal(sourceText(app({ tag: "Lam", name: "x", domain: nat, body: variable("x") }, number(1))), "(fun (x : Nat) => x)(1)");
});

test("messages and evaluate results use source syntax", async t => {
  const program = new CubicalProgram(await createCubical(), async name => name === "naturals"
    ? (await import("node:fs/promises")).readFile(new URL("../library/naturals.cubist", import.meta.url), "utf8") : "",
  { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(`import naturals;
def wrong_sum : 2 + 2 = 5 {
  exact refl(4);
}
def three_ways : Unit or Unit or Nat {
  exact 3;
}
def sum_and_point : Nat and Unit := (1 + 2, tt);
def three_and_point : Nat and Unit := (3, tt);
evaluate sum_and_point expecting three_and_point;
evaluate 2 + 2 expecting 5;
`, "source_messages");
  const reason = name => result.outputs.find(output => output.name === name).reason;
  assert.equal(reason("wrong_sum"), "Type mismatch: found 4 = 4, expected 2 + 2 = 5.");
  assert.equal(reason("three_ways"), "Type mismatch: found Nat, expected Unit or Unit or Nat.");
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["(3, tt)"]);
  assert.deepEqual(result.gaps.filter(gap => gap.directive).map(gap => gap.reason), ["The term evaluates to 4, not 5."]);
});

test("paths print as equalities when their type does not vary, and path application as @", () => {
  const p = variable("p");
  const at = arg => ({ tag: "PApp", path: p, arg });
  assert.equal(sourceText(equal(at([["i:1"]]), at([]))), "p @ i = p @ 0");
  // Coordinates print in the source's notation: -i, & and |.
  assert.equal(sourceText(at([["i:0", "j:1"]])), "p @ -i & j");
  assert.equal(sourceText(at([["i:1"], ["j:1"]])), "p @ i | j");
  assert.equal(sourceText(at([["i:1", "j:1"], ["k:0"]])), "p @ i & j | -k");
  assert.equal(sourceText(at([[]])), "p @ 1");
  const varying = { tag: "Path", dim: "i", family: { tag: "PApp", path: variable("q"), arg: [["i:1"]] }, left: variable("a"), right: variable("b") };
  assert.doesNotMatch(sourceText(varying), / = /);
  // A path prints as path i => …, and one that does not vary as refl.
  const line = { tag: "PLam", dim: "i", family: variable("A"), body: at([["i:1"]]) };
  assert.equal(sourceText(line), "path i => p @ i");
  assert.equal(sourceText({ tag: "PLam", dim: "i", family: variable("A"), body: variable("x") }), "refl(x)");
});

test("binary numbers print as binary literals", () => {
  // binary_naturals declares BinaryNat and BinaryPositive by their constructors.
  const constructor = (type, index, name) => ({ tag: "Con", index, name, sort: { tag: "Sort", signature: `binary_naturals__${type}` } });
  const zero = constructor("BinaryNat", 0, "binary_zero"), positive = p => ({ tag: "App", fn: constructor("BinaryNat", 1, "binary_positive"), arg: p });
  const one = constructor("BinaryPositive", 0, "binary_one");
  const bit = (digit, p) => ({ tag: "App", fn: constructor("BinaryPositive", digit ? 2 : 1, `binary_bit${digit}`), arg: p });
  assert.equal(sourceText(zero), "0b0");
  assert.equal(sourceText(positive(bit(0, bit(1, one)))), "0b110");
  // Anything else in the same type prints as it is built.
  assert.match(sourceText(positive(variable("p"))), /^binary_positive\(p\)$/);
  assert.match(sourceText(positive(bit(1, variable("p")))), /^binary_positive\(binary_bit1\(p\)\)$/);
});

test("recursion and case analysis print as induction and match", () => {
  const recursion = { motive: { tag: "Lam", name: "b", domain: nat, body: nat }, zero: variable("n"),
    step: { tag: "Lam", name: "k", domain: nat, body: { tag: "Lam", name: "h", domain: nat, body: succ(variable("h")) } },
    value: variable("m") };
  // A constant motive, and a successor clause that does not use the
  // predecessor, need no `as`.
  assert.equal(sourceText(induction(recursion)), "induction m return Nat { zero => n; succ h => succ(h); }");
  const predecessor = { ...recursion, step: { ...recursion.step, body: { ...recursion.step.body, body: variable("k") } } };
  assert.equal(sourceText(induction(predecessor)), "induction m as k return Nat { zero => n; succ h => k; }");
  // The motive's variable reads as the name `as` binds.
  const dependent = { ...recursion, motive: { tag: "Lam", name: "b", domain: nat, body: equal(variable("b"), variable("b")) } };
  assert.match(sourceText(induction(dependent)), /^induction m as k return k = k \{/);
  const cases = { tag: "SumRec", motive: { tag: "Lam", name: "z", domain: sum(unit, unit), body: U0 },
    left: { tag: "Lam", name: "a", domain: unit, body: nat }, right: { tag: "Lam", name: "b", domain: unit, body: unit }, value: variable("v") };
  assert.equal(sourceText(cases), "match v as z return U0 { left a => Nat; right b => Unit; }");
  assert.equal(sourceText(add(induction(recursion), number(1))), "(induction m return Nat { zero => n; succ h => succ(h); }) + 1");
});

test("messages name unnamed dimensions once, keep sharing, and avoid the names they show", async () => {
  const { readableDimensions, displayTerm } = await import("../web/cubical-elaborator.mjs");
  // A compact shared type: each level uses the one below twice.
  let shared = { tag: "PApp", path: variable("p"), arg: [["d0:1"]] };
  for (let depth = 0; depth < 60; depth++) shared = { tag: "App", fn: shared, arg: shared };
  const [renamed] = readableDimensions([shared]);
  assert.equal(renamed.fn, renamed.arg, "shared subterms stay shared");
  // i2 is shown as i: the dimension takes another name.
  const line = { tag: "PLam", dim: "d0", family: variable("A"), body: { tag: "PApp", path: variable("i2"), arg: [["d0:1"]] } };
  assert.equal(sourceText(readableDimensions([displayTerm(line)])[0]), "path j => i @ j");
  // A declared type named i, shown without its module: the dimension is j.
  const typed = { tag: "PLam", dim: "d0", family: variable("A"),
    body: { tag: "App", fn: { tag: "PApp", path: variable("p"), arg: [["d0:1"]] }, arg: { tag: "Sort", signature: "main__i", parameters: [], levels: [] } } };
  assert.equal(sourceText(readableDimensions([displayTerm(typed)])[0], { main__i: { name: "i" } }), "path j => (p @ j)(i)");
  // Seven dimensions in two terms: one renaming for both, past the letters.
  const at = (...dims) => ({ tag: "PApp", path: variable("p"), arg: [dims.map(d => `d${d}:1`)] });
  const [found, expected] = readableDimensions([at(0, 6), at(1, 2, 3, 4, 5, 6)]);
  assert.equal(sourceText(found), "p @ i & i1");
  assert.equal(sourceText(expected), "p @ j & k & l & m & n & i1");
});
