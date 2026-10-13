import assert from "node:assert/strict";

// Call only after checking imports and observation infrastructure. A known
// defect exempts one exact observation, never an arbitrary failed assertion.
export function assertStage(t, { observed, desired, known, id, strict = process.env.CUBIST_GENERATION_STRICT === "1" }) {
  if (known && !strict) {
    assert.deepEqual(observed, known.observed, `${id}: baseline changed; investigate and retire or revise its known-defect record`);
    assert.notDeepEqual(observed, desired, `${id}: fixed; retire its known-defect record`);
    t.todo(`${known.phase}: documented open contract, not completion`);
  }
  assert.deepEqual(observed, desired, id);
}
