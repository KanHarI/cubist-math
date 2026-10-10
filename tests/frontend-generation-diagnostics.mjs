// Public diagnostics currently expose their semantic payload through text.
// Decode it once for both historical observations and desired requirements.
// Locations and attached dependency causes are deliberately separate evidence.
import assert from "node:assert/strict";
import {isDeepStrictEqual} from "node:util";

export function diagnosticCause({code, reason}) {
  reason = reason.replace(/ at \d+:\d+$/, "");
  let match;
  if (code === "E606" && (match = reason.match(/^Type mismatch: found (.*), expected (.*)\.$/)))
    return {found: match[1], expected: match[2]};
  if (code === "E546" && (match = reason.match(/^Cannot generate ([^:]+): ([^;]+);/)))
    return {obligation: match[1], requirement: match[2]};
  if (code === "E343" && (match = reason.match(/^Untranslated name: (.+)$/)))
    return {untranslated: match[1]};
  if (code === "E340" && (match = reason.match(/^Untranslated dependency: ([^\s(]+)(?: \(.*\))?$/)))
    return {dependency: match[1]};
  if (code === "E871" && (match = reason.match(/^Inlining (\w+) here would capture its field (\w+):/)))
    return {helper: match[1], field: match[2]};
  if (code === "E845" && (match = reason.match(/^(\w+) is recursive, and a field's type cannot unfold it:/)))
    return {recursive: match[1], context: "field type"};
  return {reason};
}

const causeFields = {
  E343: ["untranslated"], E340: ["dependency"], E871: ["helper", "field"],
  E845: ["recursive", "context"], E606: ["found", "expected"], E546: ["obligation", "requirement"],
};
const needsCause = new Set(["E343", "E340", "E871", "E845"]);
export function validateDiagnostic({name, code, cause}) {
  assert.ok(typeof name === "string" && name.length > 0, "diagnostic needs a declaration name");
  assert.match(code ?? "", /^E\d+$/, "diagnostic needs its code");
  if (needsCause.has(code)) assert.ok(cause, `${code} needs its semantic cause`);
  if (cause !== undefined) {
    assert.ok(cause && typeof cause === "object" && !Array.isArray(cause), "invalid diagnostic cause");
    assert.deepEqual(Object.keys(cause).sort(), [...(causeFields[code] ?? [])].sort(), `invalid ${code} cause fields`);
    assert.ok(Object.values(cause).length > 0 && Object.values(cause).every(value => typeof value === "string" && value.length > 0),
      "diagnostic cause values must be nonempty strings");
  }
}

export const matchesDiagnostic = (actual, expected) => !!actual
  && actual.name === expected.name && actual.code === expected.code
  && (expected.cause === undefined || isDeepStrictEqual(diagnosticCause(actual), expected.cause));

export function matchesDiagnostics(actual, expected) {
  // Consume each occurrence: extra, missing, duplicated, and swapped diagnostics
  // cannot satisfy a contract by independently finding the same matching item.
  const remaining = [...actual];
  for (const expectation of expected) {
    const index = remaining.findIndex(item => matchesDiagnostic(item, expectation));
    if (index < 0) return false;
    remaining.splice(index, 1);
  }
  return remaining.length === 0;
}
