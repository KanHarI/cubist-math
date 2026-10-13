import assert from "node:assert/strict";
import { isDeepStrictEqual } from "node:util";

// Differences, rather than a fixed assertion message, identify a regression
// during shrinking. Matching them may conservatively reject a smaller case;
// it must never accept a different failure merely because both assertions fail.
function differences(actual, expected, path = []) {
  if (isDeepStrictEqual(actual, expected)) return [];
  if (actual && expected && typeof actual === "object" && typeof expected === "object")
    return [...new Set([...Object.keys(actual), ...Object.keys(expected)])].sort().flatMap(key =>
      differences(Object.hasOwn(actual, key) ? actual[key] : { absent: true },
        Object.hasOwn(expected, key) ? expected[key] : { absent: true }, [...path, key]));
  return [{ path, actual, expected }];
}

export function classifyStage({ observed, desired, known, strict = process.env.CUBIST_GENERATION_STRICT === "1" }) {
  const correct = isDeepStrictEqual(observed, desired);
  const kind = strict ? correct ? "pass" : "regression"
    : correct ? known ? "fixed" : "pass"
    : known && isDeepStrictEqual(observed, known.observed) ? "known-defect" : "regression";
  const expected = !strict && known ? known.observed : desired;
  return { kind, expected, signature: JSON.stringify(differences(observed, expected)) };
}

// Call only after checking imports and observation infrastructure. A known
// defect exempts one exact observation, never an arbitrary failed assertion.
export function assertStage(t, stage) {
  const { observed, desired, known, id } = stage, classification = classifyStage(stage);
  if (classification.kind === "fixed") assert.fail(`${id}: fixed; retire its known-defect record`);
  if (classification.kind === "regression")
    assert.deepEqual(observed, classification.expected, `${id}: changed semantic observation`);
  if (classification.kind === "known-defect") {
    t.todo(`${known.phase}: documented open contract, not completion`);
  }
  assert.deepEqual(observed, desired, id);
}
