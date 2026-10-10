// Public diagnostics currently expose their semantic payload through text.
// Decode it once for both historical observations and desired requirements.
// Locations and attached dependency causes are deliberately separate evidence.
import assert from "node:assert/strict";
import {isDeepStrictEqual} from "node:util";

// The context phrase is retained, so a refusal in another context decodes to a
// different cause instead of an unrecognized reason.
const unfoldingContexts = {"a field's type": "field type"};
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
  if (code === "E845" && (match = reason.match(/^(\w+) is recursive, and (.+?) cannot unfold it:/)))
    return {recursive: match[1], context: unfoldingContexts[match[2]] ?? match[2]};
  return {reason};
}

// The inverse of the decoder, for counterexamples that change one cause field
// while keeping the diagnostic's code and shape.
export function encodeCause(code, cause) {
  switch (code) {
    case "E606": return `Type mismatch: found ${cause.found}, expected ${cause.expected}.`;
    case "E546": return `Cannot generate ${cause.obligation}: ${cause.requirement}; the evidence is unavailable.`;
    case "E343": return `Untranslated name: ${cause.untranslated}`;
    case "E340": return `Untranslated dependency: ${cause.dependency}`;
    case "E871": return `Inlining ${cause.helper} here would capture its field ${cause.field}: rename the binder.`;
    case "E845": {
      const phrase = Object.keys(unfoldingContexts).find(text => unfoldingContexts[text] === cause.context) ?? cause.context;
      return `${cause.recursive} is recursive, and ${phrase} cannot unfold it: call it from a value instead.`;
    }
    default: throw Error(`No cause encoding for ${code}`);
  }
}

export const causeFields = {
  E343: ["untranslated"], E340: ["dependency"], E871: ["helper", "field"],
  E845: ["recursive", "context"], E606: ["found", "expected"], E546: ["obligation", "requirement"],
};
export const needsCause = new Set(["E343", "E340", "E871", "E845"]);
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

// `permitsCode` is internal: a duplicate refusal may use any code, but it must
// still be accounted for in the complete diagnostic set.
export const matchesDiagnostic = (actual, expected) => !!actual
  && actual.name === expected.name && (expected.permitsCode || actual.code === expected.code)
  && (expected.cause === undefined || isDeepStrictEqual(diagnosticCause(actual), expected.cause));

// A complete matching pairs every expectation with its own diagnostic, so
// extra, missing, duplicated and swapped diagnostics cannot satisfy a contract.
// Augmenting paths make the verdict independent of expectation order. Returns
// the matched diagnostic index for each expectation, or null.
export function matchDiagnostics(actual, expected) {
  if (actual.length !== expected.length) return null;
  const owner = actual.map(() => -1);
  const assign = (index, visited) => actual.some((item, at) => {
    if (visited.has(at) || !matchesDiagnostic(item, expected[index])) return false;
    visited.add(at);
    if (owner[at] !== -1 && !assign(owner[at], visited)) return false;
    owner[at] = index;
    return true;
  });
  if (!expected.every((_, index) => assign(index, new Set()))) return null;
  return expected.map((_, index) => owner.indexOf(index));
}
export const matchesDiagnostics = (actual, expected) => matchDiagnostics(actual, expected) !== null;
