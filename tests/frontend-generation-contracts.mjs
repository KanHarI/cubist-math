// The contract layer: case observations are data. Facts project collected
// evidence, and each requirement judges them as a table of named conditions.
// Nothing here reads defect records; the expected-failure lifecycle in
// frontend-generation-lifecycle.mjs consumes these observations.
import assert from "node:assert/strict";
import {inspect, isDeepStrictEqual} from "node:util";
import {obligations, requirementConditions} from "./fixtures/frontend-generation-requirements.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {diagnosticCause, diagnosticFields, diagnosticVariations, matchDiagnostics, validateDiagnostic} from "./frontend-generation-diagnostics.mjs";

const gapNames = result => result.gaps.map(g => `${g.name} ${g.code}`).sort();
export const diagnostics = checked => gapNames(checked.result);
export const complete = checked => assert.deepEqual(diagnostics(checked), []);
// A client is accepted only when it is verified without assumptions.
export const clientState = output => !output ? "missing" : !output.verified ? "refused"
  : output.axioms?.length ? "assumes" : "checked";
export function accepted(checked, names) {
  for (const name of names) {
    const output = checked.get(name), state = clientState(output);
    assert.equal(state, "checked", state === "assumes" ? `${name} must not introduce assumptions` : `${name}: ${output.reason}`);
  }
}
const find = (result, name) => result.outputs.find(o => o.name === name);
const gap = (result, name) => result.gaps.find(g => g.name === name);
// Historical records and acceptance share a decoder, never expected values.
const rootCauses = result => result.gaps.filter(g => g.code !== "E340")
  .map(g => [g.name, diagnosticCause(g)]).sort(([a], [b]) => a.localeCompare(b));
const dependencies = result => {
  const targets = new Map();
  for (const g of result.gaps.filter(g => g.code === "E340")) {
    const cause = diagnosticCause(g), target = cause.dependency ?? cause.reason;
    if (!targets.has(target)) targets.set(target, []);
    targets.get(target).push(g.name);
  }
  return [...targets].map(([target, names]) => [target, names.sort()]).sort(([a], [b]) => a.localeCompare(b));
};
const hasWord = (text, word) => (text.match(/\b\w+\b/g) ?? []).includes(word);
// Anchors are resolved before checking source. Repeated fragments require an
// explicit zero-based occurrence; consumers never silently select a site.
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

// A witness states the minimum its case must keep; a fixture may say more.
// Unknown witness fields fail, so a stated minimum is never silently ignored.
const atLeast = (actual, minimum) => !!actual && (minimum.code === undefined || actual.code === minimum.code)
  && (minimum.cause === undefined || isDeepStrictEqual(actual.cause, minimum.cause));
const lacking = (actual = [], minimum, label) => minimum.filter(item => !actual.includes(item)).map(item => `${label} ${item}`);
const witnessChecks = {
  clients: (fixture, names) => lacking(fixture.clients, names, "client"),
  refusedClients: (fixture, expected) => Object.entries(expected)
    .filter(([name, minimum]) => !atLeast(fixture.refusedClients?.[name], minimum)).map(([name]) => `refused client ${name}`),
  absentOutputs: (fixture, names) => lacking(fixture.absentOutputs, names, "absent output"),
  absentOutputFamilies: (fixture, names) => lacking(fixture.absentOutputFamilies, names, "absent output family"),
  diagnostic: (fixture, minimum) => fixture.diagnostic?.name === minimum.name && atLeast(fixture.diagnostic, minimum)
    ? [] : [`diagnostic ${minimum.name}`],
  sites: (fixture, count) => fixture.observations?.sites >= count ? [] : [`${count} observation sites`],
};
export function validateWitness(fixture) {
  for (const {id, witnesses} of obligations) for (const [field, minimum] of Object.entries(witnesses[fixture.id] ?? {})) {
    assert.ok(Object.hasOwn(witnessChecks, field), `${id}: unknown witness field ${field}`);
    const missing = witnessChecks[field](fixture, minimum);
    assert.ok(!missing.length, `${id}: ${fixture.id} must keep ${missing.join(", ")}`);
  }
}
// The names a witness field states, and those its case states. A name that no
// witness states has no minimum, so deleting it from its case would pass.
const witnessNames = {
  clients: {label: "client", witness: names => names, fixture: fixture => fixture.clients ?? []},
  refusedClients: {label: "refused client", witness: Object.keys, fixture: fixture => Object.keys(fixture.refusedClients ?? {})},
  absentOutputs: {label: "absent output", witness: names => names, fixture: fixture => fixture.absentOutputs ?? []},
  absentOutputFamilies: {label: "absent output family", witness: names => names, fixture: fixture => fixture.absentOutputFamilies ?? []},
  diagnostic: {label: "diagnostic", witness: ({name}) => [name], fixture: fixture => fixture.diagnostic ? [fixture.diagnostic.name] : []},
};
function validateWitnessed(fixture) {
  const witnesses = obligations.map(({witnesses: {[fixture.id]: witness}}) => witness).filter(Boolean);
  for (const [field, {label, witness, fixture: stated}] of Object.entries(witnessNames)) {
    const named = new Set(witnesses.flatMap(minimums => field in minimums ? witness(minimums[field]) : []));
    for (const name of stated(fixture)) assert.ok(named.has(name), `${fixture.id}: ${label} ${name} is named by no obligation`);
  }
}
// A cause is required by its code or by an obligation, never by the
// expectation under test.
const causeRequired = (id, name) => obligations.some(({witnesses: {[id]: witness}}) => !!witness
  && !!(witness.refusedClients?.[name]?.cause || witness.diagnostic?.name === name && witness.diagnostic.cause));
const diagnosticLocations = ["scope", "token", "tokenOccurrence", "conflict", "binder", "binderOccurrence", "call"];

export function validateFixture(fixture) {
  const {source, diagnostic, observations, rewrite} = fixture;
  const anchors = {};
  for (const key of ["id", "group", "kind", "phase", "contract", "source"])
    assert.ok(typeof fixture[key] === "string" && fixture[key].length, `missing case ${key}`);
  const names = [...fixture.clients ?? [], ...Object.keys(fixture.refusedClients ?? {})];
  assert.equal(new Set(names).size, names.length, "client names must be distinct");
  for (const field of ["clients", "absentOutputs", "absentOutputFamilies"])
    if (fixture[field]) assert.ok(Array.isArray(fixture[field]) && fixture[field].every(name => typeof name === "string" && name.length), `invalid ${field}`);
  const stated = [];
  if (fixture.refusedClients) {
    assert.ok(typeof fixture.refusedClients === "object" && !Array.isArray(fixture.refusedClients), "invalid refusedClients");
    for (const [name, expectation] of Object.entries(fixture.refusedClients)) {
      assert.ok(expectation && typeof expectation === "object" && !Array.isArray(expectation), "each refused client needs a diagnostic expectation");
      stated.push({...expectation, name});
    }
  }
  if (diagnostic) stated.push(diagnostic);
  for (const expectation of stated) validateDiagnostic(expectation, expectation === diagnostic ? diagnosticLocations : []);
  // Every stated field must receive counterexamples. A matching diagnostic has
  // its expectation's name and code, so the field table decides here.
  for (const expected of expectedDiagnostics(fixture)) {
    const context = {actual: expected, expected, causeRequired: causeRequired(fixture.id, expected.name)};
    for (const [field, {states, constrains}] of Object.entries(diagnosticFields))
      assert.ok(!states(expected) || constrains(context), `${fixture.id}: ${expected.name}'s stated ${field} would receive no counterexamples`
        + (field === "cause" ? "; a cause its code does not always carry needs an obligation that requires it" : ""));
  }
  validateWitness(fixture);
  // Old names confused reported outputs with names available to later source;
  // invariant clients duplicated the client requirement. A defect record on a
  // case would let contracts depend on the lifecycle.
  for (const field of ["absentMembers", "absentFamilies", "refusalCode", "refusalWords", "invariantClients", "knownDefect"])
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
  for (const obligation of obligations) for (const id of Object.keys(obligation.witnesses))
    assert.ok(byId.has(id), `${obligation.id}: missing witness ${id}`);
  const witnessed = new Set(obligations.flatMap(obligation => Object.keys(obligation.witnesses)));
  for (const fixture of fixtures) assert.ok(witnessed.has(fixture.id), `${fixture.id}: no requirement mapping`);
  // A witness must keep the requirements that distinguish its counterexample,
  // so removing a requirement or its applicability cannot pass silently.
  for (const obligation of obligations) for (const id of Object.keys(obligation.witnesses)) {
    const names = requirementNames(byId.get(id));
    for (const name of obligation.checks) assert.ok(names.includes(name), `${obligation.id}: ${id} must check ${name}`);
  }
  // Independently stated minimums: deleting part of a fixture's expectation
  // cannot silently redefine success in the audit. Every name a registered
  // case states has one, so none can be deleted unnoticed.
  for (const fixture of fixtures) {
    validateWitness(fixture);
    validateWitnessed(fixture);
  }
  validateConditions();
}
// A condition deleted together with its counterexamples leaves no
// counterexample to fail, so the conditions are also stated independently.
export function validateConditions(stated = requirementConditions) {
  const judged = Object.fromEntries(Object.entries(requirementChecks).map(([name, {conditions}]) => [name, Object.keys(conditions).sort()]));
  assert.deepEqual(judged, Object.fromEntries(Object.entries(stated).map(([name, conditions]) => [name, [...conditions].sort()])),
    "every requirement must judge exactly its stated conditions");
}
export function validateCoverage(manifest, fixtures) {
  validateObligations(fixtures);
  const documented = [...manifest.matchAll(/^\| `([^`]+)` \| (G\d+) \|/gm)].map(match => [match[1], match[2]]);
  assert.deepEqual(documented.sort(), fixtures.map(({id, group}) => [id, group]).sort(),
    "the coverage matrix must map every executable case to its finding once");
}

// Client meaning, publication and source expectations compose across kinds:
// a semantic case can require checked equations and refused alternatives.
function expectedDiagnostics(fixture) {
  const expected = Object.entries(fixture.refusedClients ?? {}).map(([name, expectation]) => ({...expectation, name}));
  if (fixture.diagnostic) expected.push(fixture.diagnostic);
  if (fixture.kind === "dependency") expected.push(
    {name: fixture.parent, code: "E343", cause: {untranslated: fixture.cause}},
    {name: fixture.child, code: "E340", cause: {dependency: fixture.parent}});
  return expected;
}
// Both kinds of audit controls need the expectation paired with each actual
// diagnostic, independently of their order. Pair the accepted observation
// once; never use the matcher to discard a generated control.
function diagnosticContexts(fixture, result) {
  const expected = expectedDiagnostics(fixture), owners = matchDiagnostics(result.gaps, expected);
  assert.ok(owners, `${fixture.id}: diagnostic controls need an accepted diagnostic set`);
  return result.gaps.map((actual, at) => ({actual, expected: expected[owners.indexOf(at)],
    causeRequired: causeRequired(fixture.id, actual.name)}));
}
const adviceCodes = ["W705", "W706"];
// Advice is a set: issued and identified advice are compared in one order.
const byMessage = advice => [...advice].sort((a, b) => a.message.localeCompare(b.message));
// Issued advice, located relative to its rewrite target, in that order.
const adviceFacts = (warnings, target) => byMessage(warnings).map(({code, declaration, message, start, end}) =>
  ({code, declaration, message, start: start - target.start, end: end - target.start}));
// Only identified advice at the rewrite target authorizes the replacement. The
// advice requirement's conditions decide, so recognition and acceptance agree.
function recognizedAdvice(fixture, anchors, warnings) {
  if (fixture.kind !== "lint" || !warnings.length) return false;
  const context = {fixture, anchors, facts: {advice: adviceFacts(warnings, anchors.rewrite)}};
  return Object.values(requirementChecks.advice.conditions).every(({holds}) => holds(context));
}
function observed(fixture, evidence, anchors = validateFixture(fixture)) {
  const recognized = recognizedAdvice(fixture, anchors, evidence.warnings);
  const result = recognized ? evidence.rewritten : evidence.result;
  assert.ok(result, "recognized advice needs its rewritten result");
  return {anchors, recognized, result};
}

// Facts project evidence without judging it. They locate evidence by
// declaration, site or region, and never compare it with an expectation or
// drop evidence that a condition judges: such a comparison would be a
// condition without counterexamples. Facts are also the lifecycle's records.
const regionOf = anchors => anchors.scope ?? anchors.conflict;
const sitesOf = anchors => anchors.token ? [anchors.token] : [anchors.binder, anchors.call];
const spanIn = (actual, region) => Number.isInteger(actual?.start) && Number.isInteger(actual?.end)
  ? {start: actual.start - region.start, end: actual.end - region.start} : null;
const clientFacts = (fixture, result) => Object.fromEntries([...fixture.clients ?? [], ...Object.keys(fixture.refusedClients ?? {})]
  .map(name => [name, clientState(find(result, name))]));
const forbiddenOutputs = (fixture, result) => result.outputs.filter(({name}) => fixture.absentOutputs?.includes(name)
  || fixture.absentOutputFamilies?.some(prefix => name === prefix || name.startsWith(prefix + "."))).map(o => o.name).sort();
const rangeFacts = ({fixture, result, anchors}) => ({range: spanIn(gap(result, fixture.diagnostic.name), regionOf(anchors))});
const noFacts = () => ({});
const kindFacts = {
  completion: noFacts,
  capture: noFacts,
  evidence: noFacts,
  dependency: noFacts,
  lint: ({evidence, anchors}) => ({advice: adviceFacts(evidence.warnings, anchors.rewrite)}),
  collision: ({fixture, result}) => {
    const output = find(result, fixture.symbol);
    return {originalType: output?.verified ? output.type : null};
  },
  // Every distinct link overlapping each written label, with its span relative
  // to that label and its target relative to the binder.
  links: ({fixture: {observations: {label}}, result, anchors: {positions}}) => ({links: positions.map(position => {
    const end = position + label.length;
    const links = result.links.filter(link => link.start < end && link.end > position).map(link => JSON.stringify({
      name: link.name, target: Number.isInteger(link.definitionStart) ? link.definitionStart - positions[0] : null,
      start: link.start - position, end: link.end - end}));
    return [...new Set(links)].map(text => JSON.parse(text));
  })}),
  wildcard: rangeFacts,
  "capture-range": rangeFacts,
  "refusal-range": rangeFacts,
};

// A requirement is met when each of its named conditions holds. A condition
// carries the plausible wrong results that must violate it, and the audit
// applies every one to an accepted observation: each must violate its own
// condition, and each condition must be violated alone by one of them, so a
// check that combines two conditions cannot leave either unguarded. `permits`
// lists valid variations, which must meet every requirement. Both edit the
// observed compiler result (`result`) or the collected lint evidence
// (`evidence`).
const editOutputs = (result, name, edit) => result.outputs.filter(o => o.name === name).forEach(edit);
const withoutDeclaration = (result, name) => {
  result.outputs = result.outputs.filter(o => o.name !== name);
  result.gaps = result.gaps.filter(g => g.name !== name);
};
const published = name => ({name: `publishes ${name}`, result: r => { r.outputs.push({name, verified: true, axioms: []}); }});
// Advice changes start from the case's identified advice at its whole target.
const identified = ({fixture, anchors}) => fixture.rewrite.advice.map(advice => ({...advice, ...anchors.rewrite}));
const advised = (context, name, edit) => ({name, evidence: e => { e.warnings = structuredClone(identified(context)); edit(e.warnings); }});
// Each issued warning states its identified counterpart's field.
const adviceField = (field, what, other) => ({
  holds: ({fixture, facts: {advice}}) => byMessage(fixture.rewrite.advice).every((expected, at) => !advice[at] || advice[at][field] === expected[field]),
  breaks: context => [advised(context, `advice ${what}`, w => { w[0][field] = other(w[0][field]); })],
});
// Range changes place the declaration's refusal at a span within the source.
function placements({fixture, anchors}) {
  const region = regionOf(anchors), sites = sitesOf(anchors);
  assert.ok(sites.every(site => site.end > site.start), "a covered site must be nonempty");
  const inside = [region.start, region.start + 1], last = sites.reduce((a, b) => b.start > a.start ? b : a);
  assert.ok(!sites.some(site => inside[0] <= site.start && inside[1] >= site.end), "the region must not start with its site");
  assert.ok(region.start > 0 && region.end < fixture.source.length, "the region must lie strictly inside the source");
  assert.ok(last.start + 1 < region.end, "the region must continue past its last site's start");
  const at = (name, start, end) => ({name, result: r => { Object.assign(gap(r, fixture.diagnostic.name), {start, end}); }});
  return {region, sites, inside, last, at};
}
// Link changes at each written label; `here` selects the real links that span it.
const atLabels = changes => ({fixture: {observations: {label}}, anchors: {positions}}) => positions.flatMap((position, site) => {
  const here = link => link.start === position && link.end === position + label.length;
  const edit = change => r => r.links.filter(here).forEach(change);
  const beside = change => r => { r.links.push(...r.links.filter(here).map(link => change({...link}))); };
  return changes({label, position, positions, here, edit, beside}).map(([what, result]) => ({name: `site ${site} ${what}`, result}));
});
const requirementChecks = {
  clients: {
    applies: fixture => !!fixture.clients?.length,
    conditions: {
      // One counterexample for each way a client can fail to be checked.
      checked: {
        holds: ({fixture, facts}) => fixture.clients.every(name => facts.clients[name] === "checked"),
        breaks: ({fixture}) => fixture.clients.flatMap(name => [
          {name: `${name} is refused`, result: r => editOutputs(r, name, o => { o.verified = false; })},
          {name: `${name} assumes an axiom`, result: r => editOutputs(r, name, o => { o.axioms = ["unproved"]; })},
          {name: `${name} is missing`, result: r => withoutDeclaration(r, name)},
        ]),
      },
    },
  },
  refusedClients: {
    applies: fixture => Object.keys(fixture.refusedClients ?? {}).length > 0,
    conditions: {
      refused: {
        holds: ({fixture, facts}) => Object.keys(fixture.refusedClients).every(name => facts.clients[name] === "refused"),
        breaks: ({fixture}) => Object.keys(fixture.refusedClients).flatMap(name => [
          {name: `${name} checks`, result: r => {
            editOutputs(r, name, o => Object.assign(o, {verified: true, axioms: []}));
            r.gaps = r.gaps.filter(g => g.name !== name);
          }},
          {name: `${name} is missing`, result: r => withoutDeclaration(r, name)},
        ]),
      },
    },
  },
  // Outputs report declarations; constructors must instead be tested by clients.
  outputsAbsent: {
    applies: fixture => !!(fixture.absentOutputs?.length || fixture.absentOutputFamilies?.length),
    conditions: {
      absent: {
        holds: ({facts}) => facts.forbiddenOutputs.length === 0,
        breaks: ({fixture}) => [
          ...(fixture.absentOutputs ?? []).map(published),
          ...(fixture.absentOutputFamilies ?? []).flatMap(prefix => [published(prefix), published(`${prefix}.id`)]),
        ],
      },
    },
  },
  originalType: {
    applies: fixture => fixture.kind === "collision",
    conditions: {
      verified: {
        holds: ({facts}) => facts.originalType !== null,
        breaks: ({fixture: {symbol}}) => [{name: `${symbol} is refused`, result: r => editOutputs(r, symbol, o => { o.verified = false; })}],
      },
      type: {
        holds: ({fixture, facts}) => facts.originalType === null || facts.originalType === fixture.originalType,
        breaks: ({fixture: {symbol}}) => [{name: `${symbol} has another type`, result: r => editOutputs(r, symbol, o => { o.type = "Bool"; })}],
      },
    },
  },
  // Advice may be withheld. Issued advice must be exactly the case's identified
  // advice within its rewrite target, so each condition holds vacuously
  // without advice.
  advice: {
    applies: fixture => fixture.kind === "lint",
    conditions: {
      count: {
        holds: ({fixture, facts: {advice}}) => !advice.length || advice.length === fixture.rewrite.advice.length,
        breaks: context => [
          advised(context, "advice includes another warning", w => {
            w.push({...w[0], code: "W705", message: "z is unused in the body: write M -> … instead of forall z : M. …."});
          }),
          ...context.fixture.rewrite.advice.length > 1 ? [advised(context, "advice is partial", w => { w.pop(); })] : [],
        ],
      },
      codes: adviceField("code", "has another code", code => code === "W705" ? "W706" : "W705"),
      declarations: adviceField("declaration", "names another declaration", () => "unrelated"),
      messages: adviceField("message", "has another message", () => "x is unused in the body: rename it _x."),
      startsInTarget: {
        holds: ({facts: {advice}}) => advice.every(w => w.start >= 0),
        breaks: context => [advised(context, "advice lies outside its rewrite", w => Object.assign(w[0], {start: 0, end: 1}))],
      },
      endsInTarget: {
        holds: ({anchors: {rewrite}, facts: {advice}}) => advice.every(w => w.end <= rewrite.end - rewrite.start),
        breaks: context => [advised(context, "advice extends past its rewrite", w => { w[0].end = context.anchors.rewrite.end + 1; })],
      },
      nonempty: {
        holds: ({facts: {advice}}) => advice.every(w => w.end > w.start),
        breaks: context => [advised(context, "advice has an empty span", w => { w[0].end = w[0].start; })],
      },
    },
    permits: context => [["the identified advice", warnings => warnings], ["the identified advice in reverse order", warnings => warnings.reverse()]]
      .map(([name, order]) => ({name: `${name}, with a rewrite that preserves the result`, evidence: e => {
        e.warnings = order(structuredClone(identified(context)));
        e.rewritten = structuredClone(e.result);
      }})),
  },
  // A refusal is located within its region and covers one of its sites. A
  // span that covers a nonempty site is nonempty, so emptiness needs no
  // condition. The bounds hold vacuously for an unlocated refusal, which only
  // `located` rejects.
  range: {
    applies: fixture => ["wildcard", "capture-range", "refusal-range"].includes(fixture.kind),
    conditions: {
      located: {
        holds: ({facts}) => facts.range !== null,
        breaks: ({fixture: {diagnostic: {name}}}) => [
          {name: "an unlocated refusal", result: r => { delete gap(r, name).start; delete gap(r, name).end; }},
          {name: "a refusal located only by its start", result: r => { delete gap(r, name).end; }},
        ],
      },
      startsInRegion: {
        holds: ({facts: {range}}) => !range || range.start >= 0,
        breaks: context => {
          const {region, at} = placements(context);
          return [at("a span covering the site that starts before the region", region.start - 1, region.end)];
        },
      },
      endsInRegion: {
        holds: ({facts: {range}, anchors}) => !range || range.end <= regionOf(anchors).end - regionOf(anchors).start,
        breaks: context => {
          const {region, at} = placements(context);
          return [at("a span covering the site that ends after the region", region.start, region.end + 1)];
        },
      },
      coversSite: {
        holds: ({facts: {range}, anchors}) => !range || sitesOf(anchors).some(site =>
          range.start <= site.start - regionOf(anchors).start && range.end >= site.end - regionOf(anchors).start),
        breaks: context => {
          const {region, sites, inside, last, at} = placements(context);
          return [
            at("an empty span at the site", sites[0].start, sites[0].start),
            at("a span inside the region that misses the site", ...inside),
            at("a span starting inside the site", last.start + 1, region.end),
          ];
        },
      },
    },
    permits: context => {
      const {region, sites, at} = placements(context);
      return [...sites.map(site => at("a span over exactly the site", site.start, site.end)), at("a span over the whole region", region.start, region.end)];
    },
  },
  // Every link at every written label shows that label, targets the binder and
  // spans exactly the label, and every label has a link. The conditions over
  // a label's links hold vacuously without links, which only `present` rejects.
  links: {
    applies: fixture => fixture.kind === "links",
    conditions: {
      present: {
        holds: ({facts}) => facts.links.every(links => links.length > 0),
        breaks: atLabels(({here}) => [["has no link", r => { r.links = r.links.filter(link => !here(link)); }]]),
      },
      label: {
        holds: ({fixture, facts}) => facts.links.every(links => links.every(link => link.name === fixture.observations.label)),
        breaks: atLabels(({label, edit, beside}) => [
          ["shows a freshened label", edit(link => { link.name = `${label}1`; })],
          // The correct link remains, so every link at a label must be correct.
          ["keeps its link beside a stale freshened one", beside(link => ({...link, name: `${label}1`}))],
        ]),
      },
      target: {
        holds: ({facts}) => facts.links.every(links => links.every(link => link.target === 0)),
        breaks: atLabels(({positions, edit, beside}) => [
          ["targets another definition", edit(link => { link.definitionStart = positions[0] + 1; })],
          ["has no target", edit(link => { delete link.definitionStart; })],
          ["keeps its link beside one to another definition", beside(link => ({...link, definitionStart: positions[0] + 1}))],
        ]),
      },
      start: {
        holds: ({facts}) => facts.links.every(links => links.every(link => link.start === 0)),
        breaks: atLabels(({edit, beside}) => [
          ["starts before its label", edit(link => { link.start -= 1; })],
          ["keeps its link beside one that starts before its label", beside(link => ({...link, start: link.start - 1}))],
        ]),
      },
      end: {
        holds: ({facts}) => facts.links.every(links => links.every(link => link.end === 0)),
        breaks: atLabels(({edit, beside}) => [
          ["covers more than its label", edit(link => { link.end += 1; })],
          ["keeps its link beside one that covers more than its label", beside(link => ({...link, end: link.end + 1}))],
        ]),
      },
    },
    // Repeated identical links are equivalent; links that only touch a label
    // belong to their own text.
    permits: atLabels(({label, position, beside}) => [
      ["repeats its link", beside(link => link)],
      ["has adjacent links", r => { r.links.push({name: "before", start: position - 1, end: position},
        {name: "after", start: position + label.length, end: position + label.length + 1}); }],
    ]),
  },
  // Every accepted diagnostic receives one counterexample per field the matcher
  // compares and its expectation constrains, from the matcher's own field table.
  // A cause is constrained by its code or an independent obligation, so an
  // expectation that loses its cause still meets the counterexample that
  // changes that cause. Fixture validation requires every stated field to be
  // constrained.
  diagnostics: {
    applies: () => true,
    permits: ({fixture, result}) => diagnosticContexts(fixture, result).flatMap(({actual, expected}, at) =>
      diagnosticVariations(actual, expected).map(variation => ({
        name: `${actual.name} permits ${variation.code}: ${variation.reason}`,
        result: r => { r.gaps[at] = structuredClone(variation); },
      }))),
    conditions: {
      matched: {
        holds: ({fixture, result}) => matchDiagnostics(result.gaps, expectedDiagnostics(fixture)) !== null,
        breaks: ({fixture, result}) => {
          return [
            {name: "an unrelated diagnostic", result: r => { r.gaps.push({name: "unrelated", code: "E606", reason: "Type mismatch: found Bool, expected Unit."}); }},
            ...diagnosticContexts(fixture, result).flatMap((context, at) => {
              const {actual} = context;
              const label = `${actual.name} ${actual.code}`;
              return [
                {name: `${label} is missing`, result: r => { r.gaps.splice(at, 1); }},
                {name: `${label} is duplicated`, result: r => { r.gaps.push({...r.gaps[at]}); }},
                ...Object.values(diagnosticFields).filter(field => field.constrains(context))
                  .flatMap(field => field.perturb(actual).map(({what, change}) => ({name: `${label} ${what}`, result: r => change(r.gaps[at])}))),
              ];
            }),
          ];
        },
      },
    },
  },
};
const requirementsFor = fixture => Object.entries(requirementChecks).filter(([, check]) => check.applies(fixture));
export const requirementNames = fixture => requirementsFor(fixture).map(([name]) => name);
export const unmet = observation => Object.entries(observation.requirements).filter(([, met]) => !met).map(([name]) => name);
// An active case asserts every requirement; a semantic mismatch is an
// ordinary failure, as the FG6 mutation gate requires. The lifecycle asserts
// this for unrecorded cases, and once RC0 retires it the runner calls it.
export function assertCase(fixture, observation) {
  const missing = unmet(observation);
  assert.equal(missing.length, 0, `${fixture.id}: unmet ${missing.join(", ")}\n${inspect(observation.facts, {depth: null})}`);
}
// The judging code, for the audit's mutation sweep: the projections that
// conditions read and the conditions themselves. Facts that only the
// lifecycle reads are left out; its records, not the audit, depend on them.
export const judgments = () => [...new Set([hasWord, clientState, expectedDiagnostics, adviceFacts, recognizedAdvice,
  regionOf, sitesOf, spanIn, clientFacts, forbiddenOutputs, ...Object.values(kindFacts),
  ...Object.values(requirementChecks).flatMap(({conditions}) => Object.values(conditions).map(({holds}) => holds))])];

// Compiler and lint results are collected once, as the plain data that
// judgments read: a program computes some result fields from its kernel when
// they are first read, so a result outlives its program only as a copy. Every
// judgment below is a pure function of this evidence, so audits can substitute
// plausible wrong results.
const copied = (keys, object) => Object.fromEntries(keys.filter(key => object[key] !== undefined)
  .map(key => [key, structuredClone(object[key])]));
const resultData = ({outputs, gaps, links}) => ({
  outputs: outputs.map(output => copied(["name", "verified", "axioms", "type", "reason"], output)),
  gaps: gaps.map(diagnostic => copied(["name", "code", "reason", "start", "end"], diagnostic)),
  links: links.map(link => copied(["name", "start", "end", "definitionStart"], link)),
});
export const evidenceData = ({result, rewritten, ...evidence}) =>
  ({...evidence, result: resultData(result), ...rewritten && {rewritten: resultData(rewritten)}});
export async function collectEvidence(t, fixture, check, lintSource = lint) {
  const anchors = validateFixture(fixture), evidence = {result: (await check(t, fixture.source)).result};
  if (fixture.kind === "lint") {
    // A valid original interface is a prerequisite, never the lint defect.
    const prerequisite = "the original interface must check before its rewrite";
    assert.deepEqual(gapNames(evidence.result), [], prerequisite);
    for (const name of fixture.clients)
      assert.equal(clientState(find(evidence.result, name)), "checked", `${prerequisite}: ${name}`);
    evidence.warnings = lintSource(fixture.source).filter(w => adviceCodes.includes(w.code))
      .map(({code, declaration, message, start, end}) => ({code, declaration, message, start, end}));
    // A warning code alone cannot authorize this particular edit. Changed
    // advice must be investigated before assigning it a replacement source.
    if (recognizedAdvice(fixture, anchors, evidence.warnings))
      evidence.rewritten = (await check(t, fixture.source.replace(fixture.rewrite.from, fixture.rewrite.to))).result;
  }
  return evidenceData(evidence);
}
export function observeEvidence(fixture, evidence) {
  const {anchors, recognized, result} = observed(fixture, evidence);
  const facts = {gaps: gapNames(result), clients: clientFacts(fixture, result), rootCauses: rootCauses(result), dependencies: dependencies(result)};
  if (fixture.absentOutputs || fixture.absentOutputFamilies) facts.forbiddenOutputs = forbiddenOutputs(fixture, result);
  const context = {fixture, evidence, anchors, recognized, result, facts};
  Object.assign(facts, kindFacts[fixture.kind]?.(context) ?? assert.fail(`Unknown observation kind: ${fixture.kind}`));
  const conditions = Object.fromEntries(requirementsFor(fixture).map(([name, check]) => [name,
    Object.fromEntries(Object.entries(check.conditions).map(([condition, {holds}]) => [condition, !!holds(context)]))]));
  const requirements = Object.fromEntries(Object.entries(conditions).map(([name, held]) => [name, Object.values(held).every(Boolean)]));
  return {facts, conditions, requirements};
}
// `check` uses the existing program/module reader and test-owned disposal.
// The optional lint function is used by the harness's adversarial controls.
export async function observeCase(t, fixture, check, lintSource = lint) {
  const evidence = await collectEvidence(t, fixture, check, lintSource);
  return {...observeEvidence(fixture, evidence), evidence};
}
// Each condition's plausible wrong results, and each requirement's permitted
// variations, of an accepted observation; `apply` edits a copy of its evidence.
function changes(fixture, evidence, list) {
  const context = {fixture, evidence, ...observed(fixture, evidence)};
  return requirementsFor(fixture).flatMap(([requirement, check]) => list(check, context).map(change => ({requirement,
    condition: change.condition, name: change.name,
    apply: target => change.result ? change.result(observed(fixture, target).result) : change.evidence(target)})));
}
export const counterexamples = (fixture, evidence) => changes(fixture, evidence, ({conditions}, context) =>
  Object.entries(conditions).flatMap(([condition, {breaks}]) => breaks(context).map(change => ({...change, condition}))));
export const permitted = (fixture, evidence) => changes(fixture, evidence, ({permits}, context) => permits?.(context) ?? []);
