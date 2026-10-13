import test from "node:test";
import assert from "node:assert/strict";
import { assertStage, classifyStage } from "./known-defect.mjs";
import { configuration, generate, minimize } from "./fixtures/frontend-invariants.mjs";
import { knownPreservation } from "./fixtures/frontend-invariants-baseline.mjs";

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

test("strict mode accepts repaired behavior while normal mode requests record retirement", () => {
  const stage = { observed: [], desired: [], known: { phase: "CB2", observed: ["wrong"] }, id: "fixed" };
  assert.equal(classifyStage({ ...stage, strict: false }).kind, "fixed");
  assert.equal(classifyStage({ ...stage, strict: true }).kind, "pass");
  assertStage({ todo: () => assert.fail("strict mode has no TODO") }, { ...stage, strict: true });
  assert.throws(() => assertStage({ todo: assert.fail }, { ...stage, strict: false }), /fixed; retire/);
});

test("shrinking compares candidates with their own contract and preserves an inheritance-only regression", async () => {
  const config = { ...configuration(3), recursive: false, paths: false, capture: true };
  const classify = candidate => {
    const spec = generate(candidate);
    const desired = { gaps: [["main", "captured", "E606"]], assumes: [],
      accepted: Object.fromEntries(spec.accepted.map(name => [name, true])) };
    const known = knownPreservation(candidate, desired), observed = structuredClone(known.observed);
    if (candidate.inherited) observed.accepted.child_selection = false;
    return classifyStage({ desired, observed, known, strict: false });
  };
  const original = classify(config);
  assert.equal(original.kind, "regression");
  assert.equal(classify({ ...config, inherited: false }).kind, "known-defect");
  const reduced = await minimize(config, async candidate => {
    const result = classify(candidate);
    return result.kind === "regression" && result.signature === original.signature;
  });
  assert.equal(reduced.config.inherited, true, "dropping child_selection cannot masquerade as the same regression");
  assert.ok(reduced.attempts <= 12);
});

test("shrinking records a candidate error without replacing the original witness", async () => {
  const config = {...configuration(3), recursive:false, paths:false, capture:false};
  const reduced = await minimize(config, async candidate => {
    if (!candidate.noise) throw new TypeError("candidate import failed");
    return candidate.inherited;
  });
  assert.equal(reduced.config.noise, true);
  assert.equal(reduced.config.inherited, true);
  assert.equal(reduced.errors.length, 1);
  assert.equal(reduced.errors[0].config.noise, false);
  assert.deepEqual(reduced.errors[0].error, {name:"TypeError",code:undefined,message:"candidate import failed"});
});
