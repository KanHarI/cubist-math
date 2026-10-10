// Case observations are data. Assertions and exceptions are never classified
// as known defects; only an explicit observation can take the TODO path.
import assert from "node:assert/strict";
import {isDeepStrictEqual, inspect} from "node:util";
import {obligations} from "./fixtures/frontend-generation-requirements.mjs";
import {lint} from "../web/cubist/lint.mjs";

export const diagnostics = checked => checked.result.gaps.map(g => `${g.name} ${g.code}`).sort();
export const complete = checked => assert.deepEqual(diagnostics(checked), []);
export const accepted = (checked, names) => {
  for (const name of names) {
    const output = checked.get(name);
    assert.equal(output.verified, true, `${name}: ${output.reason}`);
    assert.deepEqual(output.axioms, [], `${name} must not introduce assumptions`);
  }
};
const states = (checked, names = []) => Object.fromEntries(names.map(name => {
  const output = checked.result.outputs.find(o => o.name === name);
  if (output?.verified) assert.deepEqual(output.axioms, [], `${name} must not introduce assumptions`);
  return [name, output ? output.verified ? "checked" : "refused" : "missing"];
}));
const gap = (checked, name) => checked.result.gaps.find(g => g.name === name);
const generation = checked => checked.result.gaps.flatMap(g => {
  const match = g.reason.match(/Cannot generate ([^:]+):/);
  return match ? [[g.name, match[1]]] : [];
});
// Codes identify categories, not causes. Retain the distinguishing payload of
// primary failures. Dependency identities are recorded separately below.
// This is temporary defect evidence, never the desired acceptance predicate.
const rootCauses = checked => checked.result.gaps.filter(g => g.code !== "E340").map(g => {
  const reason = g.reason.replace(/ at \d+:\d+$/, "");
  let match, detail;
  if (g.code === "E606" && (match = reason.match(/^Type mismatch: found (.*), expected (.*)\.$/)))
    detail = {found: match[1], expected: match[2]};
  else if (g.code === "E546" && (match = reason.match(/^Cannot generate ([^:]+): ([^;]+);/)))
    detail = {obligation: match[1], requirement: match[2]};
  else if (g.code === "E343" && (match = reason.match(/^Untranslated name: (.+)$/)))
    detail = {untranslated: match[1]};
  else if (g.code === "E871" && (match = reason.match(/^Inlining (\w+) here would capture its field (\w+):/)))
    detail = {helper: match[1], field: match[2]};
  else if (g.code === "E845" && (match = reason.match(/^(\w+) is recursive, and a field's type cannot unfold it:/)))
    detail = {recursive: match[1], context: "field type"};
  else detail = {reason};
  return [g.name, detail];
}).sort(([a], [b]) => a.localeCompare(b));
const dependencies = checked => {
  const targets = new Map();
  for (const g of checked.result.gaps.filter(g => g.code === "E340")) {
    const target = g.reason.match(/^Untranslated dependency: ([^\s(]+)/)?.[1] ?? g.reason;
    if (!targets.has(target)) targets.set(target, []);
    targets.get(target).push(g.name);
  }
  return [...targets].map(([target, names]) => [target, names.sort()]).sort(([a], [b]) => a.localeCompare(b));
};
const hasWord = (text, word) => (text.match(/\b\w+\b/g) ?? []).includes(word);
// Anchors are resolved before checking source. Repeated fragments require an
// explicit zero-based occurrence; consumers never silently choose a site.
export function sourceAnchor(source, fragment, label, occurrence, wholeWord = false) {
  assert.ok(typeof fragment === "string" && fragment.length > 0, `${label} must be nonempty`);
  const starts = [];
  for (let at = source.indexOf(fragment); at !== -1; at = source.indexOf(fragment, at + 1)) {
    if (!wholeWord || !/\w/.test(source[at - 1] ?? "") && !/\w/.test(source[at + fragment.length] ?? "")) starts.push(at);
  }
  assert.ok(starts.length, `${label} must exist in its source`);
  if (occurrence === undefined) assert.equal(starts.length, 1, `${label} must occur once`);
  else assert.ok(Number.isInteger(occurrence) && occurrence >= 0 && occurrence < starts.length,
    `${label} occurrence must select an existing site`);
  const start = starts[occurrence ?? 0];
  return {start, end: start + fragment.length};
}
const relativeAnchor = (source, scope, fragment, label, occurrence, wholeWord = false) => {
  const span = sourceAnchor(source.slice(scope.start, scope.end), fragment, label, occurrence, wholeWord);
  return {start: scope.start + span.start, end: scope.start + span.end};
};
export function validateFixture(fixture) {
  const {source, diagnostic, observations, rewrite} = fixture;
  const anchors = {};
  for (const key of ["id", "group", "kind", "phase", "contract", "source"])
    assert.ok(typeof fixture[key] === "string" && fixture[key].length, `missing case ${key}`);
  const names = [...fixture.clients ?? [], ...fixture.refusedClients ?? []];
  assert.equal(new Set(names).size, names.length, "client names must be distinct");
  for (const field of ["clients", "refusedClients", "absentMembers", "absentFamilies"])
    if (fixture[field]) assert.ok(Array.isArray(fixture[field]) && fixture[field].every(name => typeof name === "string" && name.length), `invalid ${field}`);
  if (diagnostic && ("scope" in diagnostic || "token" in diagnostic)) {
    anchors.scope = sourceAnchor(source, diagnostic.scope, "diagnostic scope");
    anchors.token = relativeAnchor(source, anchors.scope, diagnostic.token, "diagnostic token", diagnostic.tokenOccurrence);
  }
  if (diagnostic && "conflict" in diagnostic) {
    anchors.conflict = sourceAnchor(source, diagnostic.conflict, "diagnostic conflict");
    assert.ok(hasWord(diagnostic.conflict, diagnostic.binder), "conflicting binder must be a complete identifier");
    anchors.binder = relativeAnchor(source, anchors.conflict, diagnostic.binder, "conflicting binder", diagnostic.binderOccurrence, true);
    anchors.call = relativeAnchor(source, anchors.conflict, diagnostic.call, "conflicting helper call");
  }
  if (observations) {
    const scope = sourceAnchor(source, observations.scope, "observation scope");
    assert.ok(typeof observations.label === "string" && observations.label.length, "observation label must be nonempty");
    anchors.positions = [...observations.scope.matchAll(/\b\w+\b/g)]
      .filter(match => match[0] === observations.label).map(match => scope.start + match.index);
    assert.ok(Number.isInteger(observations.sites) && observations.sites > 0, "observation count must be positive");
    assert.equal(anchors.positions.length, observations.sites, "observation sites must match the fixture");
  }
  if (rewrite) {
    anchors.rewrite = sourceAnchor(source, rewrite.from, "lint rewrite target");
    assert.ok(typeof rewrite.to === "string" && rewrite.to.length > 0, "lint replacement must be nonempty");
    assert.notEqual(rewrite.from, rewrite.to, "lint rewrite must change the source");
    assert.ok(rewrite.advice?.length, "lint rewrite must identify the advice it implements");
  }
  return anchors;
}
export function validateObligations(fixtures) {
  const byId = new Map(fixtures.map(fixture => [fixture.id, fixture]));
  for (const obligation of obligations) for (const id of obligation.cases)
    assert.ok(byId.has(id), `${obligation.id}: missing witness ${id}`);
  const witnessed = new Set(obligations.flatMap(obligation => obligation.cases));
  for (const fixture of fixtures) assert.ok(witnessed.has(fixture.id), `${fixture.id}: no requirement mapping`);
  // These are independently stated minimum obligations, so deleting a check
  // from the fixture cannot silently redefine success in the observer audit.
  for (const [id, members] of [["G1", ["c"]], ["G1-initial", ["N.model", "N.fold_map", "N.fold"]]])
    for (const name of members) assert.ok(byId.get(id).absentMembers?.includes(name), `${id}: missing publication requirement ${name}`);
  for (const id of ["G4", "G4-flat", "G12", "G12-inherited", "G12-initial"])
    assert.ok(byId.get(id).refusedClients?.includes("wrong"), `${id}: missing wrong-equation witness`);
  assert.ok(byId.get("G12-shadowed").refusedClients?.includes("captured"), "G12-shadowed: missing captured-equation witness");
}
export function validateCoverage(manifest, fixtures) {
  validateObligations(fixtures);
  const documented = [...manifest.matchAll(/^\| `([^`]+)` \| (G\d+) \|/gm)].map(match => [match[1], match[2]]);
  assert.deepEqual(documented.sort(), fixtures.map(({id, group}) => [id, group]).sort(),
    "the coverage matrix must map every executable case to its finding once");
}
export const rangeFacts = (actual, {scope, token}) => ({
  nonempty: actual.end > actual.start,
  withinScope: actual.start >= scope.start && actual.end <= scope.end,
  coversToken: actual.start <= token.start && actual.end >= token.end,
});

// Client meaning and publication are orthogonal to the diagnostic kind.
// A semantic case can require both checked equations and refused alternatives.
const clientRequirements = (fixture, facts) => ({
  clients: (fixture.clients ?? []).every(name => facts.clients[name] === "checked"),
  refusedClients: (fixture.refusedClients ?? []).every(name => facts.clients[name] === "refused"),
});
const expectedClientDiagnostics = fixture => (fixture.refusedClients ?? [])
  .map(name => `${name} ${fixture.refusalCode ?? "E606"}`).sort();
function observePublication(checked, fixture, facts, requirements) {
  if (!fixture.absentMembers && !fixture.absentFamilies) return;
  facts.published = checked.result.outputs.filter(({name}) =>
    fixture.absentMembers?.includes(name) || fixture.absentFamilies?.some(prefix => name === prefix || name.startsWith(prefix + ".")))
    .map(o => o.name).sort();
  requirements.publication = facts.published.length === 0;
}

// `check` uses the existing program/module reader and test-owned disposal.
// The optional lint function is used by the harness's adversarial controls.
export async function observeCase(t, fixture, check, lintSource = lint) {
  const anchors = validateFixture(fixture);
  let checked = await check(t, fixture.source);
  accepted(checked, fixture.invariantClients ?? []);
  let advice, recognizedAdvice;
  if (fixture.kind === "lint") {
    // A valid original interface is a prerequisite, never the lint defect.
    complete(checked); accepted(checked, fixture.clients);
    const warnings = lintSource(fixture.source).filter(w => ["W705", "W706"].includes(w.code));
    advice = warnings.map(({code, declaration, message}) => ({code, declaration, message}));
    const start = anchors.rewrite.start;
    recognizedAdvice = isDeepStrictEqual(advice, fixture.rewrite.advice)
      && warnings.every(w => w.start >= start && w.end > w.start && w.end <= start + fixture.rewrite.from.length);
    // A warning code alone cannot authorize this particular edit. Changed
    // advice must be investigated before assigning it a replacement source.
    if (recognizedAdvice) checked = await check(t, fixture.source.replace(fixture.rewrite.from, fixture.rewrite.to));
  }
  const facts = {gaps: diagnostics(checked), clients: states(checked, [...fixture.clients ?? [], ...fixture.refusedClients ?? []]),
    rootCauses: rootCauses(checked), dependencies: dependencies(checked)};
  const requirements = clientRequirements(fixture, facts);
  observePublication(checked, fixture, facts, requirements);
  switch (fixture.kind) {
    case "completion":
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, expectedClientDiagnostics(fixture));
      break;
    case "lint":
      facts.advice = advice;
      requirements.advice = advice.length === 0 || recognizedAdvice;
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, expectedClientDiagnostics(fixture));
      break;
    case "evidence":
      facts.generation = generation(checked);
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, expectedClientDiagnostics(fixture));
      break;
    case "collision": {
      const output = checked.get(fixture.symbol), refusal = gap(checked, fixture.symbol);
      facts.originalType = output.verified ? output.type : null;
      facts.duplicateRefused = !!refusal && /already|duplicate/i.test(refusal.reason);
      requirements.originalType = facts.originalType === fixture.originalType;
      requirements.duplicateRefused = facts.duplicateRefused;
      requirements.diagnostics = checked.result.gaps.length === 1 && !!refusal;
      break;
    }
    case "unsupported-family": {
      accepted(checked, fixture.clients);
      facts.refusals = fixture.refusedClients.map(name => {
        const refusal = gap(checked, name);
        return {name, code: refusal?.code ?? null,
          words: fixture.refusalWords.map(word => hasWord(refusal?.reason ?? "", word)),
          unsupported: /depend|transport|unsupported/i.test(refusal?.reason ?? "")};
      });
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, fixture.refusedClients.map(name => `${name} E817`).sort());
      requirements.refusals = facts.refusals.every(r => r.code === "E817" && r.words.every(Boolean) && r.unsupported);
      break;
    }
    case "dependency": {
      accepted(checked, fixture.clients);
      assert.equal(gap(checked, fixture.parent)?.code, "E343");
      assert.ok(hasWord(gap(checked, fixture.parent).reason, fixture.cause), "the parent must report its original cause");
      facts.childNamesParent = hasWord(gap(checked, fixture.child)?.reason ?? "", fixture.parent);
      facts.childRepeatsCause = hasWord(gap(checked, fixture.child)?.reason ?? "", fixture.cause);
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, [`${fixture.parent} E343`, `${fixture.child} E340`].sort());
      requirements.dependency = facts.childNamesParent;
      break;
    }
    case "wildcard": {
      const actual = gap(checked, fixture.diagnostic.name);
      assert.ok(actual, "the wildcard must be refused");
      facts.generation = generation(checked);
      const mismatch = actual.reason.match(/^Type mismatch: found (.*), expected (.*)\.(?: at \d+:\d+)?$/);
      facts.endpoints = [mismatch?.[1] === fixture.diagnostic.found, mismatch?.[2] === fixture.diagnostic.expected];
      facts.range = rangeFacts(actual, anchors);
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, [`${fixture.diagnostic.name} ${fixture.diagnostic.code}`]);
      requirements.endpoints = facts.endpoints.every(Boolean);
      requirements.range = Object.values(facts.range).every(Boolean);
      break;
    }
    case "links": {
      complete(checked); accepted(checked, fixture.clients);
      const positions = anchors.positions, binder = positions[0];
      facts.links = positions.map(position => {
        const links = checked.result.links.filter(link => link.start === position && link.end === position + fixture.observations.label.length);
        // Retain every distinct label/target at every written occurrence.
        return [...new Set(links.map(link => JSON.stringify([link.name, Number.isInteger(link.definitionStart) ? link.definitionStart - binder : null])))].map(text => JSON.parse(text));
      });
      requirements.links = facts.links.every(links => links.length > 0 && links.every(([name, target]) => name === fixture.observations.label && target === 0));
      break;
    }
    case "capture-range": {
      const {diagnostic, source} = fixture, actual = gap(checked, diagnostic.name);
      assert.deepEqual(facts.gaps, [`${diagnostic.name} ${diagnostic.code}`]);
      const {conflict, binder, call} = anchors;
      facts.range = {nonempty: actual.end > actual.start,
        withinConflict: actual.start >= conflict.start && actual.end <= conflict.end,
        coversConflict: [binder, call].some(site => actual.start <= site.start && actual.end >= site.end)};
      requirements.range = Object.values(facts.range).every(Boolean);
      break;
    }
    case "capture":
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, expectedClientDiagnostics(fixture));
      break;
    case "refusal-range": {
      const actual = gap(checked, fixture.diagnostic.name);
      assert.deepEqual(facts.gaps, [`${fixture.diagnostic.name} ${fixture.diagnostic.code}`]);
      facts.range = rangeFacts(actual, anchors);
      requirements.range = Object.values(facts.range).every(Boolean);
      break;
    }
    default: throw Error(`Unknown observation kind: ${fixture.kind}`);
  }
  return {facts, requirements};
}

export function classifyCase(fixture, observation, {strict = false} = {}) {
  const {facts, requirements} = observation;
  const unmet = Object.entries(requirements).filter(([, met]) => !met).map(([name]) => name);
  if (!unmet.length) {
    if (fixture.knownDefect && !strict) throw Error(`${fixture.id} unexpectedly passed: remove its knownDefect to activate this case`);
    return "pass";
  }
  const detail = `${fixture.id}: unmet ${unmet.join(", ")}\n${inspect(facts, {depth: null})}`;
  // Active semantic regressions remain assertions for the FG6 mutation gate.
  if (strict || !fixture.knownDefect) assert.fail(detail);
  if (!isDeepStrictEqual(facts, fixture.knownDefect))
    throw Error(`Unrecognized defect observation; update evidence only after investigation.\n${detail}\nRecorded: ${inspect(fixture.knownDefect, {depth: null})}`);
  return "known-defect";
}
export function recordCase(t, fixture, observation, options) {
  if (classifyCase(fixture, observation, options) === "known-defect") {
    t.todo(`${fixture.phase}: documented ${fixture.id} defect; never counts as completion`);
    assert.fail(`${fixture.id}: ${inspect(observation.facts, {depth: null})}`);
  }
}
