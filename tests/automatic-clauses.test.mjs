import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { testModule } from "./check-program.mjs";

// Automatic squash clauses and explicit obligations. The cases are
// cubist-tests/automatic_clauses*.cubist, whose comments state each refusal
// (tests/cubist-tests.test.mjs); E11's groupoid eliminator computes by an
// evaluate there. Here, what a verdict does not show.
const quotients = testModule("automatic_clauses");

// E4: the generated squash is the declaration's coherence obligation.
test("E4: a quotient's dependent eliminator generates its set squash", async () => {
  const { result } = await quotients();
  assert.ok(result.links.some(link => link.name === "Quotient.squash" && link.role === "coherence obligation"));
});

test("obligations by takes hlevel, a term or a proof block", () => {
  assert.throws(() => parse("def f(x : Circle) : Nat := match x { base => 0; } obligations by simp;"),
    /obligations by supports hlevel.*proof block/);
});
