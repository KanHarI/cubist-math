// The temporary expected-failure lifecycle: a pure function of a contract
// observation and its case's defect record, if any. Assertions and exceptions
// are never classified as known defects; only an exact record of the
// observation's facts can take the TODO path. Contracts and their audit never
// call this module, so activating a case is only the removal of its record.
// RC0 deletes this module, the records and the lifecycle tests together, and
// the runner then calls assertCase, which this module already asserts for
// unrecorded and strict cases.
import assert from "node:assert/strict";
import {isDeepStrictEqual, inspect} from "node:util";
import {assertCase, unmet} from "./frontend-generation-contracts.mjs";

export function classifyCase(observation, {id, record, strict = false}) {
  const missing = unmet(observation);
  if (!missing.length) {
    if (record && !strict) throw Error(`${id} unexpectedly passed: remove its knownDefects entry in fixtures/frontend-generation-defects.mjs to activate this case`);
    return "pass";
  }
  const detail = `${id}: unmet ${missing.join(", ")}\n${inspect(observation.facts, {depth: null})}`;
  // Active semantic regressions remain assertions for the FG6 mutation gate.
  if (strict || !record) assertCase({id}, observation);
  if (!isDeepStrictEqual(observation.facts, record))
    throw Error(`Unrecognized defect observation; update evidence only after investigation.\n${detail}\nRecorded: ${inspect(record, {depth: null})}`);
  return "known-defect";
}
export function recordCase(t, fixture, observation, options) {
  if (classifyCase(observation, {id: fixture.id, ...options}) === "known-defect") {
    t.todo(`${fixture.phase}: documented ${fixture.id} defect; never counts as completion`);
    assert.fail(`${fixture.id}: ${inspect(observation.facts, {depth: null})}`);
  }
}
