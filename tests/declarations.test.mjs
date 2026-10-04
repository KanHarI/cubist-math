import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { checkTestModule } from "./check-program.mjs";

test("removed theorem declarations are rejected in both source forms", () => {
  for (const source of [
    "theorem identity(A : U0, x : A) = x;",
    "theorem identity : forall A : U0. A -> A { intro A; intro x; exact x; }",
  ]) {
    assert.throws(() => parse(source), /Expected a declaration or directive/);
    assert.throws(() => formatCubist(source), /Expected a declaration or directive/);
  }
});

test("axiom and opaque are not declarations, and imports come first", () => {
  assert.throws(() => parse("axiom assumed : Nat;"), /Expected a declaration or directive: def, computable def/);
  assert.throws(() => parse("opaque def boxed := 0;"), /Expected a declaration or directive: def, computable def/);
  assert.throws(() => parse("def zero_again := 0;\nimport primes;"), /^Error: Imports must come before declarations\.$/);
  // `axiom` and `opaque` are ordinary names elsewhere.
  assert.equal(parse("def axiom(n : Nat) := n;").declarations[0].name.text, "axiom");
  assert.equal(parse("def opaque(n : Nat) := n;").declarations[0].name.text, "opaque");
});

// `print(evaluate|typeof|inspect(term));` is a top-level directive; `print`,
// `typeof` and `inspect` are ordinary names elsewhere.
test("print directives show evaluate, typeof or inspect of a term", () => {
  const { directives } = parse("print(evaluate(2));\nprint(typeof(id));\nprint(inspect(id(0)));");
  assert.deepEqual(directives.map(d => [d.kind, d.show]), [["print", "evaluate"], ["print", "typeof"], ["print", "inspect"]]);
  assert.deepEqual(directives.map(d => d.start), [0, 20, 39]);
  assert.throws(() => parse("print(normalize(2));"), /^Error: print shows evaluate\(term\), typeof\(term\) or inspect\(term\)\.$/);
  assert.throws(() => parse("print(evaluate(2);"), /Expected '\)'/);
  assert.throws(() => parse("print;"), /Expected a declaration or directive: def, computable def, inductive, evaluate, print/);
  assert.equal(parse("def print(typeof : Nat) := typeof;").declarations[0].name.text, "print");
});

// The definitions are cubist-tests/declarations_definitions.cubist, whose
// comments state the refusal (tests/cubist-tests.test.mjs).
test("definitions expose their checked bodies, and a refused one admits nothing", async t => {
  const { program } = await checkTestModule(t, "declarations_definitions");
  const view = program.inspect("declarations_definitions__identity_proof");
  assert.equal(view.folded.reference.name, "declarations_definitions__identity_proof");
  assert.equal(view.folded.expression.tag, "Lam");
  assert.equal(view.statement.parameters.length, 0);
  assert.equal(program.inspect("declarations_definitions__identity").folded.reference, undefined);
  assert.equal(program.kernel.definitions.has("declarations_definitions__false_claim"), false);
});
