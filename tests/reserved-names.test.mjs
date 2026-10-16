// Reserved names (web/cubist/parser.mjs, reservedNames): the keywords that
// begin a term or a statement, or join terms, the built-in types Unit and
// Void, and Unit's element tt cannot be bound, at any binding site. A
// user's own Unit would otherwise pass a theory's law check while holding
// data, and a user's own tt would be read as a literal's evidence. Contextual
// keywords and generated interface names are reserved everywhere. That the real Unit and Void
// still state laws is cubist-tests/theories.cubist's Nontrivial.
import test from "node:test";
import assert from "node:assert/strict";
import { parse, reservedNames, languageKeywords, generatedNames } from "../web/cubist/parser.mjs";

const parseError = source => { try { parse(source); return null; } catch (error) { return error.message; } };
const reserved = word => `${word} is reserved${generatedNames.has(word) ? " for the generated interface (docs/guides/keywords.md)" : ", as a keyword or a built-in type of the language"}; pick another name.`;

test("Unit, Void and tt cannot be declared or bound at any binding site", () => {
  for (const word of ["Unit", "Void", "tt"]) {
    const sites = {
      definition: `def ${word} : U0 := Nat;`,
      parameter: `def f(${word} : U0) : U0 := Nat;`,
      implicit: `def f{{${word} : U0}}(n : Nat) : Nat := n;`,
      lambda: `def f := fun (${word} : U0) => Nat;`,
      forall: `def F := forall ${word} : U0. Nat;`,
      exists: `def F := exists ${word} : U0. Nat;`,
      let: `def f(n : Nat) : Nat {\n  let ${word} := n;\n  exact n;\n}`,
      pattern: `def f(p : Nat and Nat) : Nat {\n  obtain (${word}, b) := p;\n  exact b;\n}`,
      clause: `def f(n : Nat) : Nat := match n {\n  zero => n;\n  succ(${word}) => n;\n};`,
      motive: `def f(n : Nat) : Nat := match n as ${word} {\n  zero => n;\n  succ(k) => n;\n};`,
      inductive: `inductive ${word} {\n  c;\n}`,
      constructor: `inductive T {\n  ${word};\n}`,
      theory: `theory T(U < UU0) {\n  M : set U;\n  ${word} : M;\n}`,
      carrier: `theory T(U < UU0) {\n  ${word} : set U;\n}`,
      universe: `theory T(${word} < UU0) {\n  M : set U;\n}`,
      section: `section (${word} : U0) {\n  def x := 0;\n}`,
    };
    for (const [site, source] of Object.entries(sites))
      assert.equal(parseError(source), reserved(word), `${word} as a ${site}`);
  }
});

test("keywords and generated interface names cannot be bound at any naming site", () => {
  for (const word of languageKeywords) {
    for (const source of [
      `def ${word} : Unit := tt;`,
      `def f(${word} : Unit) : Unit := tt;`,
      `def f{{${word} : Unit}} : Unit := tt;`,
      `def f : Unit -> Unit := fun (${word} : Unit) => tt;`,
      `def P := forall ${word} : Unit. Unit;`,
      `def P := exists ${word} : Unit. Unit;`,
      `def f : Unit { let ${word} := tt; exact tt; }`,
      `def f : Unit -> Unit { intro ${word}; exact tt; }`,
      `def f : Unit := match tt { ${word} => tt; };`,
      `def f(n : Nat) := match n { succ(${word}) => tt; };`,
      `inductive T { ${word}; }`,
      `theory T(U < UU0) { M : set U; ${word} : M; }`,
      `section (${word} : Unit) { def f := tt; }`,
      `import ${word};`,
      `notation ${word} { x + y := x; }`,
      `simp_set ${word} := [];`,
      `theory T(U < UU0) extends ${word} : Parent { M : set U; }`,
    ]) assert.equal(parseError(source), reserved(word), `${word}: ${source}`);
  }
  for (const word of ["Nat", "zero", "succ", "axiom", "opaque"]) {
    assert.equal(parseError(`def f(${word} : Nat) : Nat := 0;`), null, word);
  }
});

test("generated members remain usable in calls, labels and constructor patterns", () => {
  for (const word of generatedNames) assert.equal(parseError(`def ${word} := tt;`), reserved(word));
  assert.equal(parseError("def h := T.Hom.make(map := fun (x : Unit) => x);"), null);
  assert.equal(parseError("def h := T.Iso.make(to := f, from := g);"), null);
  assert.equal(parseError("def h := T.Hom.compose(T.Hom.id(m), f);"), null);
  assert.equal(parseError("def f(t : T) := match t { gen(x) => x; squash(x, y, p, q) @ i @ j => p @ i; };"), null);
  assert.equal(parseError("def f(t : T) := match t { T.squash(x, y, p, q) @ i @ j => p @ i; };"), null);
});

test("initial and free headers diagnose unsupported parameter forms at the header", () => {
  for (const [source, message, at] of [
    ["initial N(A : U0) : Monoid(U0);", /initial takes no parameters; use free/, "("],
    ["free W{{A : U0}} : Monoid(U0) on A;", /free takes explicit parameters in parentheses/, "{"],
  ]) assert.throws(() => parse(source), error => message.test(error.message) && error.offset === source.indexOf(at));
  assert.doesNotThrow(() => parse("free W(V < UU0, A : V) : Monoid(V) on A;"));
});
