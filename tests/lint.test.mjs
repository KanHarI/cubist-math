import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { moduleFiles } from "../tools/module-sources.mjs";
import { lint } from "../web/cubist/lint.mjs";

const messages = source => lint(source).map(warning => warning.message);
const warned = (source, pattern) => assert.ok(messages(source).some(message => pattern.test(message)),
  `expected a warning ${pattern} for ${source}, got ${JSON.stringify(messages(source))}`);
const clean = source => assert.deepEqual(messages(source), [], source);

test("an as name that neither the motive nor a clause uses is reported", () => {
  warned("def copy(n : UNat) := induction n as k return UNat { zero => 0; succ h => succ(h); };",
    /^k is unused: the return type does not mention it and the successor clause does not use it\. Omit as k: induction n return …\.$/);
  warned("def to_number(v : Unit or UNat) := match v as z return UNat { left u => 0; right n => n; };",
    /^z is unused: the return type does not mention it\. Omit as z: match v return …\.$/);
  // Used in the motive, or as the predecessor in the successor clause.
  clean("def f(n : UNat) := induction n as k return (k = k) { zero => refl(0); succ h => refl(succ(k)); };");
  clean("def g(n : UNat) := induction n as k return UNat { zero => 0; succ h => k; };");
  clean("def d(v : Unit or Unit) := match v as z return Shape(z) { left a => 0; right b => tt; };");
  clean("def c(n : UNat) := induction n return UNat { zero => 0; succ h => h; };");
});

test("a quantified variable the body does not mention is reported, with its plain form", () => {
  warned("def T(A, B : U0) := forall x : A. B;", /^x is unused in the body: write A -> … instead of forall x : A\. …\.$/);
  warned("def S(A, B : U0) := exists a : A. B;", /^a is unused in the body: write A and … instead of exists a : A\. …\.$/);
  warned("def G(A : U0, P : A -> U0) := forall x, y : A. P(y);", /^x is unused in the body: take it out of the group and write A -> … for it\.$/);
  clean("def T(A : U0, P : A -> U0) := forall x : A. P(x);");
  clean("def G(A : U0, P : A -> A -> U0) := forall x, y : A. P(x, y);");
  // A universe variable has no unnamed form, and fun binders are required.
  clean("def I := forall U < UU0. forall A : U. A -> A;");
  clean("def K(A, B : U0) := fun (a : A) => fun (b : B) => a;");
});

test("let and obtain whose names nothing after them uses are reported", () => {
  warned("def f(n : UNat) : UNat { let unused := succ(n); exact n; }", /^unused is never used after this let: remove it\.$/);
  warned("def f(n : UNat) : UNat { let h : UNat := n; exact n; }", /^h is never used after this let: remove it\.$/);
  warned("def f(n : UNat) : UNat { let h : n = n { rfl; } exact n; }", /^h is never used after this let: remove it\.$/);
  const unusedObtain = "def f(p : UNat and UNat) : UNat { obtain (a, b) := p; exact 0; }";
  warned(unusedObtain, /^None of a, b is used after this obtain: remove it\.$/);
  assert.deepEqual(lint(unusedObtain).map(warning => warning.code), ["W701"]);
  clean("def f(n : UNat) : UNat { let m := succ(n); exact m; }");
  clean("def f(p : UNat and UNat) : UNat { obtain (a, b) := p; exact a; }");
  // Used inside a nested block.
  clean("def f(n : UNat) : n = n { let h : n = n { rfl; } let g : n = n { exact h; } exact g; }");
  // hlevel and generated squash clauses use the context without naming it.
  clean("def f(A : U0, p : IsProp(U0, A)) : IsSet(U0, A) { let h : IsProp(U0, A) := p; hlevel; }");
});

test("clause arguments, coordinates, hypotheses and parameters are never reported", () => {
  clean(`inductive Circle : U0 { base; loop : base = base; }
def flat(c : Circle, unused : UNat) : UNat := match c { base => 0; loop @ i => 0; };
def pred(n : UNat) : UNat := match n { zero => 0; succ(k) => 0; };
def ignore(n : UNat) := induction n return UNat { zero => 0; succ ignored => 0; };
def intro_unused : UNat -> UNat { intro n; exact 0; }`);
});

test("a warning names its declaration, line and column", () => {
  const [warning] = lint("def one := 1;\ndef copy(n : UNat) :=\n  induction n as k return UNat { zero => 0; succ h => h; };");
  assert.deepEqual({ line: warning.line, column: warning.column, declaration: warning.declaration }, { line: 3, column: 18, declaration: "copy" });
});

test("the rebuilt library has no unused bindings", async () => {
  for (const file of moduleFiles("library"))
    assert.deepEqual(messages(await readFile(file, "utf8")), [], file);
});
