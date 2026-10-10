// Active contracts: fixture validation, observations and semantic assertions.
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
  const names = [...fixture.clients ?? [], ...Object.keys(fixture.refusedClients ?? {})];
  assert.equal(new Set(names).size, names.length, "client names must be distinct");
  for (const field of ["clients", "absentOutputs", "absentOutputFamilies"])
    if (fixture[field]) assert.ok(Array.isArray(fixture[field]) && fixture[field].every(name => typeof name === "string" && name.length), `invalid ${field}`);
  if (fixture.refusedClients) {
    assert.ok(typeof fixture.refusedClients === "object" && !Array.isArray(fixture.refusedClients), "invalid refusedClients");
    for (const [name, code] of Object.entries(fixture.refusedClients))
      assert.ok(name.length > 0 && /^E\d+$/.test(code), "each refused client needs its diagnostic code");
  }
  // Old names confused reported outputs with names available to later source.
  for (const field of ["absentMembers", "absentFamilies", "refusalCode"])
    assert.ok(!(field in fixture), `obsolete expectation ${field}`);
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
  for (const name of ["N.model", "N.fold_map", "N.fold"])
    assert.ok(byId.get("G1-initial").absentOutputs?.includes(name), `G1-initial: missing output requirement ${name}`);
  for (const [id, clients] of [["G1", ["leaked_c"]], ["G1-initial", ["leaked_one", "leaked_mul"]]])
    for (const name of clients)
      assert.equal(byId.get(id).refusedClients?.[name], "E343", `${id}: missing name-availability witness ${name}`);
  assert.ok(byId.get("G1-reverse").clients.includes("constructor"), "G1-reverse: missing original constructor witness");
  for (const id of ["G4", "G4-flat", "G12", "G12-inherited", "G12-initial"])
    assert.equal(byId.get(id).refusedClients?.wrong, "E606", `${id}: missing wrong-equation witness`);
  for (const id of ["G12", "G12-inherited", "G12-initial"])
    for (const name of ["base", "computation", "computation2"])
      assert.ok(byId.get(id).clients.includes(name), `${id}: missing recursive-result witness ${name}`);
  assert.equal(byId.get("G12-shadowed").refusedClients?.captured, "E606", "G12-shadowed: missing captured-equation witness");
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
  refusedClients: Object.keys(fixture.refusedClients ?? {}).every(name => facts.clients[name] === "refused"),
});
const expectedClientDiagnostics = fixture => Object.entries(fixture.refusedClients ?? {})
  .map(([name, code]) => `${name} ${code}`);
// Outputs report declarations; constructors must instead be tested by source clients.
function observeOutputAbsence(checked, fixture, facts, requirements) {
  if (!fixture.absentOutputs && !fixture.absentOutputFamilies) return;
  facts.forbiddenOutputs = checked.result.outputs.filter(({name}) =>
    fixture.absentOutputs?.includes(name) || fixture.absentOutputFamilies?.some(prefix => name === prefix || name.startsWith(prefix + ".")))
    .map(o => o.name).sort();
  requirements.outputsAbsent = facts.forbiddenOutputs.length === 0;
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
  const facts = {gaps: diagnostics(checked), clients: states(checked, [...fixture.clients ?? [], ...Object.keys(fixture.refusedClients ?? {})])};
  const requirements = clientRequirements(fixture, facts);
  observeOutputAbsence(checked, fixture, facts, requirements);
  const expectedDiagnostics = expectedClientDiagnostics(fixture);
  switch (fixture.kind) {
    case "completion":
      break;
    case "lint":
      facts.advice = advice;
      requirements.advice = advice.length === 0 || recognizedAdvice;
      break;
    case "evidence":
      break;
    case "collision": {
      const output = checked.get(fixture.symbol), refusal = gap(checked, fixture.symbol);
      facts.originalType = output.verified ? output.type : null;
      facts.duplicateRefused = !!refusal && /already|duplicate/i.test(refusal.reason);
      requirements.originalType = facts.originalType === fixture.originalType;
      requirements.duplicateRefused = facts.duplicateRefused;
      expectedDiagnostics.push(`${fixture.symbol} ${refusal?.code}`);
      break;
    }
    case "unsupported-family": {
      accepted(checked, fixture.clients);
      facts.refusals = Object.keys(fixture.refusedClients).map(name => {
        const refusal = gap(checked, name);
        return {name, code: refusal?.code ?? null,
          words: fixture.refusalWords.map(word => hasWord(refusal?.reason ?? "", word)),
          unsupported: /depend|transport|unsupported/i.test(refusal?.reason ?? "")};
      });
      requirements.refusals = facts.refusals.every(r => r.code === "E817" && r.words.every(Boolean) && r.unsupported);
      break;
    }
    case "dependency": {
      accepted(checked, fixture.clients);
      assert.equal(gap(checked, fixture.parent)?.code, "E343");
      assert.ok(hasWord(gap(checked, fixture.parent).reason, fixture.cause), "the parent must report its original cause");
      facts.childNamesParent = hasWord(gap(checked, fixture.child)?.reason ?? "", fixture.parent);
      expectedDiagnostics.push(`${fixture.parent} E343`, `${fixture.child} E340`);
      requirements.dependency = facts.childNamesParent;
      break;
    }
    case "wildcard": {
      const actual = gap(checked, fixture.diagnostic.name);
      assert.ok(actual, "the wildcard must be refused");
      const mismatch = actual.reason.match(/^Type mismatch: found (.*), expected (.*)\.(?: at \d+:\d+)?$/);
      facts.endpoints = [mismatch?.[1] === fixture.diagnostic.found, mismatch?.[2] === fixture.diagnostic.expected];
      facts.range = rangeFacts(actual, anchors);
      expectedDiagnostics.push(`${fixture.diagnostic.name} ${fixture.diagnostic.code}`);
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
      expectedDiagnostics.push(`${diagnostic.name} ${diagnostic.code}`);
      const {conflict, binder, call} = anchors;
      facts.range = {nonempty: actual.end > actual.start,
        withinConflict: actual.start >= conflict.start && actual.end <= conflict.end,
        coversConflict: [binder, call].some(site => actual.start <= site.start && actual.end >= site.end)};
      requirements.range = Object.values(facts.range).every(Boolean);
      break;
    }
    case "capture":
      break;
    case "refusal-range": {
      const actual = gap(checked, fixture.diagnostic.name);
      expectedDiagnostics.push(`${fixture.diagnostic.name} ${fixture.diagnostic.code}`);
      facts.range = rangeFacts(actual, anchors);
      requirements.range = Object.values(facts.range).every(Boolean);
      break;
    }
    default: throw Error(`Unknown observation kind: ${fixture.kind}`);
  }
  requirements.diagnostics = isDeepStrictEqual(facts.gaps, expectedDiagnostics.sort());
  return {facts, requirements};
}

export function assertCase(fixture, {facts, requirements}) {
  const unmet = Object.entries(requirements).filter(([, met]) => !met).map(([name]) => name);
  assert.equal(unmet.length, 0, `${fixture.id}: unmet ${unmet.join(", ")}\n${inspect(facts, {depth: null})}`);
}
