// Case observations are data. Assertions and exceptions are never classified
// as known defects; only an explicit observation can take the TODO path.
import assert from "node:assert/strict";
import {isDeepStrictEqual, inspect} from "node:util";
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
const hasWord = (text, word) => (text.match(/\b\w+\b/g) ?? []).includes(word);
const observationPositions = ({source, observations}) => {
  const start = source.indexOf(observations.scope);
  return [...observations.scope.matchAll(/\b\w+\b/g)]
    .filter(match => match[0] === observations.label).map(match => start + match.index);
};
export function validateFixture(fixture) {
  const {source, diagnostic, observations, rewrite} = fixture;
  const contains = (text, fragment, label) => {
    assert.ok(typeof fragment === "string" && fragment.length > 0, `${label} must be nonempty`);
    assert.ok(text.includes(fragment), `${label} must exist in its source`);
  };
  for (const key of ["id", "group", "kind", "phase", "contract", "source"])
    assert.ok(typeof fixture[key] === "string" && fixture[key].length, `missing case ${key}`);
  const names = [...fixture.clients ?? [], ...fixture.refusedClients ?? []];
  assert.equal(new Set(names).size, names.length, "client names must be distinct");
  if (diagnostic && ("scope" in diagnostic || "token" in diagnostic)) {
    contains(source, diagnostic.scope, "diagnostic scope");
    contains(diagnostic.scope, diagnostic.token, "diagnostic token");
  }
  if (diagnostic && "conflict" in diagnostic) {
    contains(source, diagnostic.conflict, "diagnostic conflict");
    contains(diagnostic.conflict, diagnostic.binder, "conflicting binder");
    assert.ok(hasWord(diagnostic.conflict, diagnostic.binder), "conflicting binder must be a complete identifier");
    contains(diagnostic.conflict, diagnostic.call, "conflicting helper call");
  }
  if (observations) {
    contains(source, observations.scope, "observation scope");
    contains(observations.scope, observations.label, "observation label");
    assert.ok(Number.isInteger(observations.sites) && observations.sites > 0, "observation count must be positive");
    assert.equal(observationPositions(fixture).length, observations.sites, "observation sites must match the fixture");
  }
  if (rewrite) {
    contains(source, rewrite.from, "lint rewrite target");
    assert.equal(source.split(rewrite.from).length, 2, "lint rewrite target must occur once");
    assert.ok(typeof rewrite.to === "string" && rewrite.to.length > 0, "lint replacement must be nonempty");
    assert.notEqual(rewrite.from, rewrite.to, "lint rewrite must change the source");
  }
}
const rangeFacts = (actual, fixture) => {
  const {source, diagnostic} = fixture;
  const scope = source.indexOf(diagnostic.scope);
  const token = scope + diagnostic.scope.lastIndexOf(diagnostic.token);
  return {
    nonempty: actual.end > actual.start,
    withinScope: actual.start >= scope && actual.end <= scope + diagnostic.scope.length,
    coversToken: actual.start <= token && actual.end >= token + diagnostic.token.length,
  };
};

// `check` uses the existing program/module reader and test-owned disposal.
// The optional lint function is used by the harness's adversarial controls.
export async function observeCase(t, fixture, check, lintSource = lint) {
  validateFixture(fixture);
  let checked = await check(t, fixture.source);
  accepted(checked, fixture.invariantClients ?? []);
  if (fixture.kind === "lint") {
    // A valid original interface is a prerequisite, never the lint defect.
    complete(checked); accepted(checked, fixture.clients);
    const advice = lintSource(fixture.source).filter(w => ["W705", "W706"].includes(w.code));
    if (advice.length) checked = await check(t, fixture.source.replace(fixture.rewrite.from, fixture.rewrite.to));
  }
  const facts = {gaps: diagnostics(checked), clients: states(checked, [...fixture.clients ?? [], ...fixture.refusedClients ?? []])};
  const requirements = {clients: (fixture.clients ?? []).every(name => facts.clients[name] === "checked")};
  switch (fixture.kind) {
    case "completion":
    case "lint":
      requirements.diagnostics = facts.gaps.length === 0;
      break;
    case "evidence":
      facts.generation = generation(checked);
      requirements.diagnostics = facts.gaps.length === 0;
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
      facts.published = checked.result.outputs.filter(o => fixture.absentFamilies.some(prefix => o.name === prefix || o.name.startsWith(prefix + "."))).map(o => o.name).sort();
      facts.refusals = fixture.refusedClients.map(name => {
        const refusal = gap(checked, name);
        return {name, code: refusal?.code ?? null,
          words: fixture.refusalWords.map(word => hasWord(refusal?.reason ?? "", word)),
          unsupported: /depend|transport|unsupported/i.test(refusal?.reason ?? "")};
      });
      requirements.publication = facts.published.length === 0;
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
      requirements.dependency = facts.childNamesParent && !facts.childRepeatsCause;
      break;
    }
    case "wildcard": {
      const actual = gap(checked, fixture.diagnostic.name);
      assert.ok(actual, "the wildcard must be refused");
      facts.generation = generation(checked);
      facts.endpoints = [fixture.diagnostic.found, fixture.diagnostic.expected].map(text => actual.reason.includes(text));
      facts.range = rangeFacts(actual, fixture);
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, [`${fixture.diagnostic.name} ${fixture.diagnostic.code}`]);
      requirements.endpoints = facts.endpoints.every(Boolean);
      requirements.range = Object.values(facts.range).every(Boolean);
      break;
    }
    case "links": {
      complete(checked); accepted(checked, fixture.clients);
      const positions = observationPositions(fixture), binder = positions[0];
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
      const conflict = source.indexOf(diagnostic.conflict);
      const binder = conflict + [...diagnostic.conflict.matchAll(/\b\w+\b/g)].find(match => match[0] === diagnostic.binder).index;
      const call = conflict + diagnostic.conflict.indexOf(diagnostic.call);
      facts.range = {nonempty: actual.end > actual.start,
        withinConflict: actual.start >= conflict && actual.end <= conflict + diagnostic.conflict.length,
        coversConflict: [binder, call].some(site => actual.start <= site && actual.end > site)};
      requirements.range = Object.values(facts.range).every(Boolean);
      break;
    }
    case "capture":
      requirements.refusedClients = fixture.refusedClients.every(name => facts.clients[name] === "refused");
      requirements.diagnostics = isDeepStrictEqual(facts.gaps, fixture.refusedClients.map(name => `${name} E606`).sort());
      break;
    case "refusal-range": {
      const actual = gap(checked, fixture.diagnostic.name);
      assert.deepEqual(facts.gaps, [`${fixture.diagnostic.name} ${fixture.diagnostic.code}`]);
      facts.range = rangeFacts(actual, fixture);
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
