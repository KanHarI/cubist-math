import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { lint } from "../web/mathscript/lint.mjs";

const messages = source => lint(source).map(warning => warning.message);
const warned = (source, pattern) => assert.ok(messages(source).some(message => pattern.test(message)),
  `expected a warning ${pattern} for ${source}, got ${JSON.stringify(messages(source))}`);
const clean = source => assert.deepEqual(messages(source), [], source);

test("an as name that neither the motive nor a clause uses is reported", () => {
  warned("def copy(n : Nat) := induction n as k return Nat { zero => 0; succ h => succ(h); };",
    /^k is unused: the return type does not mention it and the successor clause does not use it\. Omit as k: induction n return …\.$/);
  warned("def to_number(v : Unit or Nat) := match v as z return Nat { left u => 0; right n => n; };",
    /^z is unused: the return type does not mention it\. Omit as z: match v return …\.$/);
  // Used in the motive, or as the predecessor in the successor clause.
  clean("def f(n : Nat) := induction n as k return (k = k) { zero => refl(0); succ h => refl(succ(k)); };");
  clean("def g(n : Nat) := induction n as k return Nat { zero => 0; succ h => k; };");
  clean("def d(v : Unit or Unit) := match v as z return Shape(z) { left a => 0; right b => tt; };");
  clean("def c(n : Nat) := induction n return Nat { zero => 0; succ h => h; };");
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

test("let, have and obtain whose names nothing after them uses are reported", () => {
  warned("def f(n : Nat) : Nat { let unused := succ(n); exact n; }", /^unused is never used after this let: remove it\.$/);
  warned("def f(n : Nat) : Nat { have h : Nat := n; exact n; }", /^h is never used after this have: remove it\.$/);
  warned("def f(n : Nat) : Nat { have h : n = n { rfl; } exact n; }", /^h is never used after this have: remove it\.$/);
  warned("def f(p : Nat and Nat) : Nat { obtain (a, b) := p; exact 0; }", /^None of a, b is used after this obtain: remove it\.$/);
  clean("def f(n : Nat) : Nat { let m := succ(n); exact m; }");
  clean("def f(p : Nat and Nat) : Nat { obtain (a, b) := p; exact a; }");
  // Used inside a nested block.
  clean("def f(n : Nat) : n = n { have h : n = n { rfl; } have g : n = n { exact h; } exact g; }");
  // hlevel and generated squash clauses use the context without naming it.
  clean("def f(A : U0, p : IsProp(U0, A)) : IsSet(U0, A) { have h : IsProp(U0, A) := p; hlevel; }");
});

test("clause arguments, coordinates, hypotheses and parameters are never reported", () => {
  clean(`inductive Circle : U0 { base; loop : base = base; }
def flat(c : Circle, unused : Nat) : Nat := match c { base => 0; loop @ i => 0; };
def pred(n : Nat) : Nat := match n { zero => 0; succ(k) => 0; };
def ignore(n : Nat) := induction n return Nat { zero => 0; succ ignored => 0; };
def intro_unused : Nat -> Nat { intro n; exact 0; }`);
});

test("a warning names its declaration, line and column", () => {
  const [warning] = lint("def one := 1;\ndef copy(n : Nat) :=\n  induction n as k return Nat { zero => 0; succ h => h; };");
  assert.deepEqual({ line: warning.line, column: warning.column, declaration: warning.declaration }, { line: 3, column: 18, declaration: "copy" });
});

test("the rebuilt library has no unused bindings", async () => {
  const library = new URL("../library/", import.meta.url);
  for (const file of (await readdir(library)).filter(name => name.endsWith(".cubist")))
    assert.deepEqual(messages(await readFile(new URL(file, library), "utf8")), [], file);
});
