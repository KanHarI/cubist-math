import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { currentSyntax } from "../web/cubist/legacy-syntax.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { cubicalMathTree, cubicalText } from "../web/cubical-notation.mjs";
import { testModule } from "./check-program.mjs";

// L1.5 (HoTT A8 and B4): projections p.1 and p.2, and let's stated type and
// proof block, which replaced have, show and suffices on 2026-09-30. Each
// elaborates to existing kernel syntax through the instruction driver:
// projections to Fst and Snd, and a typed let to its checked value kept at
// the stated type.
const module = await createCubical();
// The cases are cubist-tests/projections.cubist, projections_archive_helpers
// and let_statements, whose comments state each refusal
// (tests/cubist-tests.test.mjs); here, the checked terms, positions, goals
// and links a verdict does not show.
const projections = testModule("projections", { module }), lets = testModule("let_statements", { module });
const parseError = source => { try { parse(source); return null; } catch (error) { return error.message; } };
// The checked term of a declaration, under its parameters' lambdas and the
// ascription that keeps a stated result type.
const body = (program, name) => {
  const ascription = term => term.tag === "App" && term.fn.tag === "Lam" && term.fn.body.tag === "Var" && term.fn.body.name === term.fn.name;
  let term = program.inspect(`projections__${name}`).expression;
  while (term.tag === "Lam" || ascription(term)) term = term.tag === "Lam" ? term.body : term.arg;
  return term;
};
// The line:column where errors report the first `text` after `anchor` in `source`.
const at = (source, text, anchor = "") => {
  const before = source.slice(0, source.indexOf(text, source.indexOf(anchor)));
  return `${before.split("\n").length}:${before.length - before.lastIndexOf("\n")}`;
};

test("p.1 and p.2 are the kernel's projections, with the family read from the pair's type", async () => {
  const { program } = await projections();
  assert.deepEqual(body(program, "first_of"), { tag: "Fst", pair: { tag: "Var", name: body(program, "first_of").pair.name } });
  assert.equal(body(program, "second_of").tag, "Snd");
  assert.equal(body(program, "third").tag, "Snd");
  assert.equal(body(program, "third").pair.tag, "Snd");
  assert.equal(program.checker.displayText(program.inspect("projections__evidence").type),
    "forall A : U0. forall B : A -> U0. forall p : exists x : A. B(x). B(p.1)");
  assert.deepEqual(program.evaluations.map(item => item.value), ["5"]);
});

test("misused projections are rejected with precise messages", async () => {
  const tuple = "A pair has only the projections .1 and .2. A tuple nests pairs to the right: the third component of (a, b, c) is .2.2.";
  assert.equal(parseError("def third(t : Nat and Nat and Nat) : Nat := t.3;"), tuple);
  assert.equal(parseError("def zeroth(t : Nat and Nat) : Nat := t.0;"), tuple);
  // Only a tight dot projects: a quantifier's dot is followed by a space.
  assert.match(parseError("def spaced(p : Nat and Nat) : Nat := p. 1;"), /Expected ';', found '\.'/);
  assert.equal(parseError("def fine := forall n : Nat. n = n;"), null);
  const { source, verdicts } = await projections();
  // Reported at the projection itself.
  assert.equal(verdicts.not_a_pair, `Projection .1 requires a dependent pair; found a value of type Nat. at ${at(source, ".1;", "def not_a_pair")}`);
  assert.match(verdicts.function_projection, /^Projection \.2 requires a dependent pair; found a value of type Nat -> Nat\./);
});

test("projections print as p.1 and p.2 in source text and in mathematical notation", () => {
  const p = { tag: "Var", name: "p" }, f = { tag: "Var", name: "f" };
  const lambda = { tag: "Lam", name: "x", domain: { tag: "Unit" }, body: { tag: "Var", name: "x" } };
  assert.equal(sourceText({ tag: "Fst", pair: p }), "p.1");
  assert.equal(sourceText({ tag: "Snd", pair: { tag: "Snd", pair: p } }), "p.2.2");
  assert.equal(sourceText({ tag: "Fst", pair: { tag: "App", fn: f, arg: p } }), "f(p).1");
  assert.equal(sourceText({ tag: "App", fn: { tag: "Snd", pair: p }, arg: f }), "p.2(f)");
  assert.equal(sourceText({ tag: "Fst", pair: lambda }), "(fun (x : Unit) => x).1");
  assert.deepEqual(cubicalMathTree({ tag: "Snd", pair: p }), { kind: "Projection", index: 2, value: { kind: "Name", name: "p", local: true } });
  assert.equal(cubicalText({ tag: "Fst", pair: { tag: "Snd", pair: p } }), "p.2.1");
  assert.equal(cubicalText({ tag: "Fst", pair: lambda }), "(λ (x : Unit). x).1");
  // The source text reads back as the same projections.
  const text = sourceText({ tag: "Fst", pair: { tag: "App", fn: { tag: "Snd", pair: p }, arg: f } });
  assert.equal(text, "p.2(f).1");
  assert.equal(parse(text, true).kind, "projection");
});

test("HoTT B4 by let: a restated goal, reasoning backwards, and a stated type", async () => {
  const { source, program, verdicts } = await lets();
  // The block's result is checked against the stated type at the let.
  assert.equal(verdicts.wrong_block, `Type mismatch: found A, expected B. at ${at(source, "let x : B", "def wrong_block")}`);
  assert.equal(verdicts.not_a_type, `let states a type after the colon; found a value of type A. at ${at(source, "a :=", "def not_a_type")}`);
  // The block proves its type without the name it defines.
  assert.match(verdicts.out_of_scope, /^Untranslated name: x/);
  // The block sees the stated type as its goal. A let names a term rather
  // than a context entry, so the displayed context does not list b; the
  // final exact uses it all the same.
  const steps = program.steps("let_statements").filter(step => step.declaration === "contrapositive");
  assert.deepEqual(steps.map(step => [step.kind, step.goal, step.locals.map(local => local.name).join(",")]),
    [["intro", "A -> Void", "A,B,f,not_b"], ["let", "Void", "A,B,f,not_b,a"], ["exact", "B", "A,B,f,not_b,a"],
     ["exact", "Void", "A,B,f,not_b,a"]]);
});

test("have, show and suffices are refused with their let forms", () => {
  assert.equal(parseError("def a(A : U0, x : A) : A { have h : A := x; exact h; }"),
    "have was removed: write let name : T := term; or prove the claim in a block, let name : T { … }.");
  assert.equal(parseError("def a(A : U0, x : A) : A { show A; exact x; }"),
    "show was removed: prove the restated goal in a block, let h : T { … }, then exact h;.");
  assert.equal(parseError("def a(A : U0, x : A) : A { suffices h : A by h; exact x; }"),
    "suffices was removed: prove the claim first, let h : T { … }, then prove the goal from h.");
});

test("a historical source reads in today's syntax: have statements become let, prose does not", () => {
  assert.equal(currentSyntax("def a(A : U0, x : A) : A { have h : A := x; have g : A { exact h; } exact g; } // we have g"),
    "def a(A : U0, x : A) : A { let h : A := x; let g : A { exact h; } exact g; } // we have g");
  assert.equal(parseError(currentSyntax("def a(A : U0, x : A) : A { have h : A := x; exact h; }")), null);
});

test("projections link to their checked terms", async () => {
  const { program } = await projections();
  const roles = program.links.map(link => [link.name, link.role]);
  assert.ok(roles.some(([name]) => name === ".1"), JSON.stringify(roles));
});
