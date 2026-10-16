import test from "node:test";
import assert from "node:assert/strict";
import { isDeepStrictEqual } from "node:util";
import { configuration, generate, minimize, observationDifferences } from "./fixtures/frontend-invariants.mjs";

test("shrinking compares candidates with their own contract and preserves an inheritance-only regression", async () => {
  const config = { ...configuration(3), recursive: false, paths: false, capture: true };
  const differences = candidate => {
    const spec = generate(candidate);
    const desired = { gaps: [["main", "captured", "E606"]], assumes: [],
      accepted: Object.fromEntries(spec.accepted.map(name => [name, true])) };
    const observed = structuredClone(desired);
    if (candidate.inherited) observed.accepted.child_selection = false;
    return observationDifferences(observed, desired);
  };
  const original = differences(config);
  assert.deepEqual(original, [{path:["accepted","child_selection"],actual:false,expected:true}]);
  assert.deepEqual(differences({ ...config, inherited: false }), []);
  const reduced = await minimize(config, async candidate => {
    return isDeepStrictEqual(differences(candidate), original);
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
