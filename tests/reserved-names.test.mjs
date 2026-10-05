// Reserved names (web/cubist/parser.mjs, reservedNames): the language's
// keywords and its built-in types Unit and Void cannot be bound, at any
// binding site. A user's own Unit would otherwise pass a theory's law check
// while holding data. Contextual keywords stay names outside their
// constructs. That the real Unit and Void still state laws is
// cubist-tests/theories.cubist's Nontrivial.
import test from "node:test";
import assert from "node:assert/strict";
import { parse, reservedNames } from "../web/cubist/parser.mjs";

const parseError = source => { try { parse(source); return null; } catch (error) { return error.message; } };
const reserved = word => `${word} is reserved, as a keyword or a built-in type of the language; pick another name.`;

test("Unit and Void cannot be declared or bound at any binding site", () => {
  for (const word of ["Unit", "Void"]) {
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
      theory: `theory T {\n  sort M : set;\n  ${word} : M;\n}`,
      sort: `theory T {\n  sort ${word} : set;\n}`,
    };
    for (const [site, source] of Object.entries(sites))
      assert.equal(parseError(source), reserved(word), `${word} as a ${site}`);
  }
});

test("every keyword is reserved, and contextual keywords stay names", () => {
  for (const word of reservedNames) assert.equal(parseError(`def f(${word} : Nat) : Nat := 0;`), reserved(word), word);
  // Words with a meaning only inside one construct, which the library binds.
  for (const word of ["computable", "evaluate", "expecting", "print", "typeof", "inspect", "simp_rule", "simp_set",
    "prop", "set", "law", "sort", "notation", "extends", "type", "trunc", "with", "at", "by", "from", "over",
    "along", "only", "using", "path", "left", "right", "zero", "succ"])
    assert.equal(parseError(`def f(${word} : Nat) : Nat := 0;`), null, word);
  assert.equal(parse("theory T { law : Unit; sort : Unit; }").declarations[0].fields.map(f => f.name.text).join(), "law,sort");
});
