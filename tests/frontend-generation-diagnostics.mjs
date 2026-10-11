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

// Every field a diagnostic expectation may state. The matcher compares exactly
// these, and the audit derives its counterexamples from the same entries: an
// expectation cannot state a field that is not compared, and a compared field
// cannot lack a counterexample. `states` says whether an expectation states the
// field; `constrains` whether its counterexamples apply. A cause is constrained
// by its code or an independent obligation, never by the expectation under
// test, and every stated field must also be constrained.
export const diagnosticFields = {
  name: {
    matches: (actual, expected) => actual.name === expected.name,
    states: () => true,
    constrains: () => true,
    perturb: () => [{what: "is reported on another declaration", change: gap => { gap.name = `${gap.name}_elsewhere`; }}],
  },
  code: {
    // `permitsCode` is internal to the collision contract: a duplicate refusal
    // may use any code. It is never a fixture field.
    matches: (actual, expected) => expected.permitsCode || actual.code === expected.code,
    states: expected => !expected.permitsCode,
    constrains: ({expected}) => !expected.permitsCode,
    perturb: ({code}) => [{what: "has another code", change: gap => { gap.code = code === "E606" ? "E343" : "E606"; }}],
  },
  cause: {
    matches: (actual, expected) => expected.cause === undefined || isDeepStrictEqual(diagnosticCause(actual), expected.cause),
    states: expected => expected.cause !== undefined,
    constrains: ({actual, causeRequired}) => needsCause.has(actual.code) || causeRequired,
    perturb: actual => {
      const cause = diagnosticCause(actual), reason = text => gap => { gap.reason = text; };
      assert.deepEqual(Object.keys(cause).sort(), [...causeFields[actual.code] ?? []].sort(), `${actual.name} ${actual.code} must decode to its cause`);
      return [
        {what: "has an unrecognized cause", change: reason("An unrelated failure with the same diagnostic code")},
        ...Object.keys(cause).map(field => ({what: `names another ${field}`, change: reason(encodeCause(actual.code, {...cause, [field]: "Other"}))})),
        ..."found" in cause ? [{what: "swaps found and expected", change: reason(encodeCause(actual.code, {found: cause.expected, expected: cause.found}))}] : [],
      ];
    },
  },
};

// `locations` names the source-anchor fields a declaration diagnostic may also
// carry; range requirements, not the matcher, judge them.
export function validateDiagnostic(expectation, locations = []) {
  const {name, code, cause} = expectation;
  for (const key of Object.keys(expectation))
    assert.ok(Object.hasOwn(diagnosticFields, key) || locations.includes(key), `unknown diagnostic field ${key}`);
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
  && Object.values(diagnosticFields).every(field => field.matches(actual, expected));

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
