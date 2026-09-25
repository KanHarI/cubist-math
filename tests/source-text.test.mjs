import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";

const U0 = { tag: "U", level: 0 }, nat = { tag: "Nat" }, unit = { tag: "Unit" }, v = { tag: "Void" };
const variable = name => ({ tag: "Var", name });
const pi = (name, domain, body) => ({ tag: "Pi", name, domain, body });
const sigma = (name, domain, body) => ({ tag: "Sigma", name, domain, body });
const sum = (left, right) => ({ tag: "Sum", left, right });
const app = (fn, ...args) => args.reduce((f, arg) => ({ tag: "App", fn: f, arg }), fn);
const number = n => n ? { tag: "Succ", value: number(n - 1) } : { tag: "Zero" };
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
  assert.equal(sourceText(app({ tag: "DefRef", name: "naturals__isLt" }, variable("n"), { tag: "Succ", value: variable("n") })), "n < succ(n)");
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
def choice : Unit or Unit or Nat {
  exact 3;
}
def sum_and_point : Nat and Unit := (1 + 2, tt);
def three_and_point : Nat and Unit := (3, tt);
evaluate sum_and_point expecting three_and_point;
evaluate 2 + 2 expecting 5;
`, "source_messages");
  const reason = name => result.outputs.find(output => output.name === name).reason;
  assert.equal(reason("wrong_sum"), "Type mismatch: found 4 = 4, expected 2 + 2 = 5.");
  assert.equal(reason("choice"), "Type mismatch: found Nat, expected Unit or Unit or Nat.");
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["(3, tt)"]);
  assert.deepEqual(result.gaps.filter(gap => gap.directive).map(gap => gap.reason), ["The term evaluates to 4, not 5."]);
});

test("paths print as equalities when their type does not vary, and path application as @", () => {
  const p = variable("p");
  const at = arg => ({ tag: "PApp", path: p, arg });
  assert.equal(sourceText(equal(at([["i:1"]]), at([]))), "p @ i = p @ 0");
  assert.equal(sourceText(at([["i:0", "j:1"]])), "p @ meet(flip(i), j)");
  assert.equal(sourceText(at([["i:1"], ["j:1"]])), "p @ join(i, j)");
  assert.equal(sourceText(at([[]])), "p @ 1");
  const varying = { tag: "Path", dim: "i", family: { tag: "PApp", path: variable("q"), arg: [["i:1"]] }, left: variable("a"), right: variable("b") };
  assert.doesNotMatch(sourceText(varying), / = /);
});

test("binary numbers print as binary literals", () => {
  const label = { tag: "Sum", left: unit, right: { tag: "Sum", left: unit, right: unit } };
  const positive = { tag: "W", name: "b", domain: label, body: unit };
  const binaryNat = { tag: "Sum", left: unit, right: positive };
  const tt = { tag: "Point" };
  const one = { tag: "Sup", as: positive, label: { tag: "Inl", as: label, value: tt },
    children: { tag: "Lam", name: "v", domain: v, body: { tag: "Abort", as: positive, impossible: variable("v") } } };
  const bit = (digit, p) => ({ tag: "Sup", as: positive,
    label: { tag: "Inr", as: label, value: { tag: digit ? "Inr" : "Inl", as: label.right, value: tt } },
    children: { tag: "Lam", name: "u", domain: unit, body: p } });
  assert.equal(sourceText({ tag: "Inl", as: binaryNat, value: tt }), "0b0");
  assert.equal(sourceText({ tag: "Inr", as: binaryNat, value: bit(0, bit(1, one)) }), "0b110");
  // Anything else in the same type prints as it is built.
  assert.match(sourceText({ tag: "Inr", as: binaryNat, value: variable("p") }), /^right\(p\)$/);
});

test("recursion and case analysis print as induction and match", () => {
  const recursion = { tag: "NatRec", motive: { tag: "Lam", name: "b", domain: nat, body: nat }, zero: variable("n"),
    step: { tag: "Lam", name: "k", domain: nat, body: { tag: "Lam", name: "h", domain: nat, body: { tag: "Succ", value: variable("h") } } },
    value: variable("m") };
  assert.equal(sourceText(recursion), "induction m as k return Nat { zero => n; succ h => succ(h); }");
  // The motive's variable reads as the name `as` binds.
  const dependent = { ...recursion, motive: { tag: "Lam", name: "b", domain: nat, body: equal(variable("b"), variable("b")) } };
  assert.match(sourceText(dependent), /^induction m as k return k = k \{/);
  const cases = { tag: "SumRec", motive: { tag: "Lam", name: "z", domain: sum(unit, unit), body: U0 },
    left: { tag: "Lam", name: "a", domain: unit, body: nat }, right: { tag: "Lam", name: "b", domain: unit, body: unit }, value: variable("v") };
  assert.equal(sourceText(cases), "match v as z return U0 { left a => Nat; right b => Unit; }");
  assert.equal(sourceText(add(recursion, number(1))), "(induction m as k return Nat { zero => n; succ h => succ(h); }) + 1");
});
