import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { testModule } from "./check-program.mjs";

// Automatic squash clauses and explicit obligations. The cases are
// cubist-tests/automatic_clauses*.cubist, whose comments state each refusal
// (tests/cubist-tests.test.mjs); here, what a verdict does not show.
const quotients = testModule("automatic_clauses"), groupoids = testModule("automatic_clauses_groupoid");

// E4: the generated squash is the declaration's coherence obligation.
test("E4: a quotient's dependent eliminator generates its set squash", async () => {
  const { result } = await quotients();
  assert.ok(result.links.some(link => link.name === "Quotient.squash" && link.role === "coherence obligation"));
});

// E11: all three generated dimensions, with a dependent groupoid motive; the
// eliminator computes.
test("E11: a groupoid's dependent eliminator generates its three-dimensional squash", async () => {
  const { result } = await groupoids();
  assert.deepEqual(result.evaluations.map(item => item.value), ["3"]);
});

test("obligations by takes hlevel, a term or a proof block", () => {
  assert.throws(() => parse("def f(x : Circle) : Nat := match x { base => 0; } obligations by simp;"),
    /obligations by supports hlevel.*proof block/);
});
