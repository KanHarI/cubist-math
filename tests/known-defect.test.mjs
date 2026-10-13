import test from "node:test";
import assert from "node:assert/strict";
import { assertStage } from "./known-defect.mjs";

test("known defects cannot hide a new failure, missing observation or unexpected fix", () => {
  const known = { phase: "CB2", observed: { accepted: ["captured"], errors: ["intended"] } };
  const desired = { accepted: ["intended"], errors: ["captured"] };
  for (const observed of [desired, {}, { accepted: [], errors: ["intended", "captured"] }]) {
    const todos = [];
    assert.throws(() => assertStage({ todo: value => todos.push(value) },
      { observed, desired, known, id: "witness", strict: false }), { code: "ERR_ASSERTION" });
    assert.deepEqual(todos, []);
  }
});

test("only an exact known defect gets TODO; strict mode still refuses it", () => {
  const known = { phase: "CB2", observed: { errors: ["E845"] } }, desired = { errors: [] };
  for (const strict of [false, true]) {
    const todos = [];
    assert.throws(() => assertStage({ todo: value => todos.push(value) },
      { observed: known.observed, desired, known, id: "witness", strict }), { code: "ERR_ASSERTION" });
    assert.equal(todos.length, strict ? 0 : 1);
  }
});

test("active contracts and retired records must satisfy the desired observation", () => {
  const todo = () => assert.fail("an active or unexpectedly fixed contract cannot be TODO");
  assertStage({ todo }, { observed: [], desired: [], id: "active" });
  assert.throws(() => assertStage({ todo }, { observed: ["wrong"], desired: [], id: "active" }), { code: "ERR_ASSERTION" });
  assert.throws(() => assertStage({ todo }, {
    observed: [], desired: [], known: { phase: "CB2", observed: [] }, id: "retired", strict: false,
  }), { code: "ERR_ASSERTION" });
});
