import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/mathscript/parser.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

test("removed theorem declarations are rejected in both source forms", () => {
  for (const source of [
    "theorem identity(A : U0, x : A) = x;",
    "theorem identity : forall A : U0, A -> A { intro A; intro x; exact x; }",
  ]) {
    assert.throws(() => parse(source), /Expected a declaration or directive/);
    assert.throws(() => formatMathScript(source), /Expected a declaration or directive/);
  }
});

test("axiom is not a declaration, and imports come first", () => {
  assert.throws(() => parse("axiom assumed : Nat;"), /Expected a declaration or directive: def, opaque def/);
  assert.throws(() => parse("def zero_again = 0;\nimport primes;"), /^Error: Imports must come before declarations\.$/);
  // `axiom` is an ordinary name elsewhere.
  assert.equal(parse("def axiom(n : Nat) = n;").declarations[0].name.text, "axiom");
});

test("definitions check constructions and proofs and expose their checked bodies", async t => {
  const program = new CubicalProgram(await createCubical(), async () => "");
  t.after(() => program.dispose());
  const result = await program.check(`
    def identity(A : U0, x : A) = x;
    def identity_proof : forall A : U0, A -> A {
      intro A; intro x; exact x;
    }
    def computes : identity_proof(Nat, 0) = identity(Nat, 0) { exact refl(0); }
  `, "definitions");
  assert.equal(result.complete, true);
  assert.ok(result.outputs.every(d => d.kind === "def" && d.verified));
  const view = program.inspect("definitions__identity_proof");
  assert.equal(view.folded.reference.name, "definitions__identity_proof");
  assert.equal(view.folded.expression.tag, "Lam");
  assert.equal(view.statement.parameters.length, 0);
  assert.equal(program.inspect("definitions__identity").folded.reference, undefined);

  const invalid = await program.check("def false_claim : 0 = 1 { exact refl(0); }", "invalid");
  assert.equal(invalid.complete, false);
  assert.equal(invalid.outputs.find(d => d.name === "false_claim").verified, false);
  assert.equal(program.kernel.definitions.has("invalid__false_claim"), false);
});
