import test from "node:test";
import assert from "node:assert/strict";
import {T} from "../../web/translator/core.mjs";
import {headBeta} from "../../web/translator/hlevel.mjs";
import {syntaxGraphBudget} from "../../web/translator/syntax-graph.mjs";

test("h-level head reduction follows term and universe applications without unfolding definitions", () => {
  const reference = {tag: "DefRef", name: "hlevels__IsProp"};
  const generic = T.levelLambda("u", T.lam("A", T.universe(T.variable("u")),
    T.app(T.levelApply(reference, T.variable("u")), T.variable("A"))));
  const term = T.app(T.levelApply(generic, 0), T.unit);
  assert.deepEqual(headBeta(term), T.app(T.levelApply(reference, 0), T.unit));
});

test("h-level head reduction bounds self-reproducing syntax and long neutral spines", () => {
  const self = T.lam("x", T.unit, T.app(T.variable("x"), T.variable("x")));
  const omega = T.app(self, self);
  let spine = T.variable("f");
  for (let n = 0; n < 20; n++) spine = T.app(spine, T.point);
  for (const term of [omega, spine])
    assert.throws(() => headBeta(term, {budget: syntaxGraphBudget({maxVisits: 10})}),
      error => error.kind === "budget");
  assert.equal(headBeta(spine), spine, "a neutral spine is retained without reduction");
});
