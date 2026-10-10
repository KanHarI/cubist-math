// Case observations are data. Assertions and exceptions are never classified
// as known defects; only an explicit observation can take the TODO path.
import assert from "node:assert/strict";
import {isDeepStrictEqual, inspect} from "node:util";
import {obligations} from "./fixtures/frontend-generation-requirements.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {causeFields, diagnosticCause, encodeCause, matchDiagnostics, needsCause, validateDiagnostic} from "./frontend-generation-diagnostics.mjs";

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
const generation = result => result.gaps.flatMap(g => {
  const match = g.reason.match(/Cannot generate ([^:]+):/);
  return match ? [[g.name, match[1]]] : [];
});
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
    for (const [name, expectation] of Object.entries(fixture.refusedClients)) {
      assert.ok(expectation && typeof expectation === "object" && !Array.isArray(expectation), "each refused client needs a diagnostic expectation");
      validateDiagnostic({...expectation, name});
    }
  }
  if (diagnostic) validateDiagnostic(diagnostic);
  // Old names confused reported outputs with names available to later source;
  // invariant clients duplicated the client requirement.
  for (const field of ["absentMembers", "absentFamilies", "refusalCode", "invariantClients"])
    assert.ok(!(field in fixture), `obsolete expectation ${field}`);
  if (fixture.kind === "unsupported-family")
    assert.ok(Array.isArray(fixture.refusalWords) && fixture.refusalWords.length
      && fixture.refusalWords.every(word => /^\w+$/.test(word)), "an unsupported family needs its refusal words");
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
  // A witness must keep the requirements that distinguish its counterexample,
  // so removing a requirement or its applicability cannot pass silently.
  for (const obligation of obligations) for (const id of obligation.cases) {
    const names = requirementNames(byId.get(id));
    for (const name of obligation.checks) assert.ok(names.includes(name), `${obligation.id}: ${id} must check ${name}`);
  }
  // These are independently stated minimum obligations, so deleting a check
  // from the fixture cannot silently redefine success in the observer audit.
  for (const name of ["N.model", "N.fold_map", "N.fold"])
    assert.ok(byId.get("G1-initial").absentOutputs?.includes(name), `G1-initial: missing output requirement ${name}`);
  for (const [id, clients] of [["G1", {leaked_c: "c"}], ["G1-initial", {leaked_one: "N.one", leaked_mul: "N.mul"}]])
    for (const [name, untranslated] of Object.entries(clients))
      assert.deepEqual(byId.get(id).refusedClients?.[name], {code: "E343", cause: {untranslated}}, `${id}: missing name-availability witness ${name}`);
  assert.ok(byId.get("G1-reverse").clients.includes("constructor"), "G1-reverse: missing original constructor witness");
  for (const name of ["preserves", "level", "preserves_u1", "level_u1"])
    assert.ok(byId.get("G2").clients.includes(name), `G2: missing public-type witness ${name}`);
  assert.deepEqual(byId.get("G2").refusedClients?.lowered, {code: "E606", cause: {found: "U1", expected: "U0"}}, "G2: missing universe-lowering witness");
  for (const id of ["G4", "G4-flat", "G12", "G12-inherited", "G12-initial"])
    assert.equal(byId.get(id).refusedClients?.wrong?.code, "E606", `${id}: missing wrong-equation witness`);
  for (const id of ["G12", "G12-inherited", "G12-initial"])
    for (const name of ["base", "computation", "computation2"])
      assert.ok(byId.get(id).clients.includes(name), `${id}: missing recursive-result witness ${name}`);
  assert.equal(byId.get("G12-shadowed").refusedClients?.captured?.code, "E606", "G12-shadowed: missing captured-equation witness");
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
  // The duplicate contract deliberately permits different refusal codes.
  if (fixture.kind === "collision") expected.push({name: fixture.symbol, permitsCode: true});
  if (fixture.kind === "dependency") expected.push(
    {name: fixture.parent, code: "E343", cause: {untranslated: fixture.cause}},
    {name: fixture.child, code: "E340", cause: {dependency: fixture.parent}});
  return expected;
}
const adviceCodes = ["W705", "W706"];
const adviceOf = warnings => warnings.map(({code, declaration, message}) => ({code, declaration, message}));
// Only identified advice at the rewrite target authorizes the replacement.
function recognizedAdvice(fixture, anchors, warnings) {
  if (fixture.kind !== "lint") return false;
  const {start, end} = anchors.rewrite;
  return isDeepStrictEqual(adviceOf(warnings), fixture.rewrite.advice)
    && warnings.every(w => w.start >= start && w.end > w.start && w.end <= end);
}
function observed(fixture, evidence, anchors = validateFixture(fixture)) {
  const recognized = recognizedAdvice(fixture, anchors, evidence.warnings);
  const result = recognized ? evidence.rewritten : evidence.result;
  assert.ok(result, "recognized advice needs its rewritten result");
  return {anchors, recognized, result};
}
const rangeFacts = (actual = {}, {scope, token}) => ({
  nonempty: actual.end > actual.start,
  withinScope: actual.start >= scope.start && actual.end <= scope.end,
  coversToken: actual.start <= token.start && actual.end >= token.end,
});
// Kind-specific facts. Facts are the recorded defect observation; requirements
// below judge them, and neither depends on historical records.
const kindFacts = {
  completion: () => ({}),
  capture: () => ({}),
  lint: ({evidence}) => ({advice: adviceOf(evidence.warnings)}),
  evidence: ({result}) => ({generation: generation(result)}),
  collision: ({fixture, result}) => {
    const output = find(result, fixture.symbol), refusal = gap(result, fixture.symbol);
    return {originalType: output?.verified ? output.type : null,
      duplicateRefused: !!refusal && /already|duplicate/i.test(refusal.reason)};
  },
  "unsupported-family": ({fixture, result}) => ({refusals: Object.keys(fixture.refusedClients).map(name => {
    const reason = gap(result, name)?.reason ?? "";
    return {name, code: gap(result, name)?.code ?? null, words: fixture.refusalWords.map(word => hasWord(reason, word)),
      unsupported: /depend|transport|unsupported/i.test(reason)};
  })}),
  dependency: ({fixture, result}) => {
    const reason = gap(result, fixture.child)?.reason ?? "";
    return {childNamesParent: hasWord(reason, fixture.parent), childRepeatsCause: hasWord(reason, fixture.cause)};
  },
  wildcard: ({fixture: {diagnostic}, result, anchors}) => {
    const actual = gap(result, diagnostic.name), mismatch = actual ? diagnosticCause(actual) : {};
    return {generation: generation(result), range: rangeFacts(actual, anchors),
      endpoints: [mismatch.found === diagnostic.cause.found, mismatch.expected === diagnostic.cause.expected]};
  },
  links: ({fixture: {observations: {label}}, result, anchors: {positions}}) => ({links: positions.map(position => {
    const links = result.links.filter(link => link.start === position && link.end === position + label.length);
    // Retain every distinct label/target at every written occurrence.
    return [...new Set(links.map(link => JSON.stringify([link.name,
      Number.isInteger(link.definitionStart) ? link.definitionStart - positions[0] : null])))].map(text => JSON.parse(text));
  })}),
  "capture-range": ({fixture, result, anchors: {conflict, binder, call}}) => {
    const actual = gap(result, fixture.diagnostic.name) ?? {};
    return {range: {nonempty: actual.end > actual.start,
      withinConflict: actual.start >= conflict.start && actual.end <= conflict.end,
      coversConflict: [binder, call].some(site => actual.start <= site.start && actual.end >= site.end)}};
  },
  "refusal-range": ({fixture, result, anchors}) => ({range: rangeFacts(gap(result, fixture.diagnostic.name), anchors)}),
};

// Each requirement states the accepted behavior and the plausible wrong
// results that must violate it. The audit applies every counterexample to an
// accepted observation, so deleting or weakening a check fails after the
// defect records are gone. A counterexample edits the observed compiler result
// (`result`) or the collected lint evidence (`evidence`).
const editOutputs = (result, name, edit) => result.outputs.filter(o => o.name === name).forEach(edit);
const withoutDeclaration = (result, name) => {
  result.outputs = result.outputs.filter(o => o.name !== name);
  result.gaps = result.gaps.filter(g => g.name !== name);
};
const published = name => ({name: `publishes ${name}`, result: r => { r.outputs.push({name, verified: true, axioms: []}); }});
// The real refusal for an arrow-typed operation shares E817 with G3's cause.
const arrowRefusal = "T's models have no homomorphisms: its op's result mentions a carrier on both sides of an arrow, and such homomorphisms need not compose.";
const requirementChecks = {
  clients: {
    applies: fixture => !!fixture.clients?.length,
    met: ({fixture, facts}) => fixture.clients.every(name => facts.clients[name] === "checked"),
    breaks: ({fixture}) => fixture.clients.flatMap(name => [
      {name: `${name} is refused`, result: r => editOutputs(r, name, o => { o.verified = false; })},
      {name: `${name} assumes an axiom`, result: r => editOutputs(r, name, o => { o.axioms = ["unproved"]; })},
      {name: `${name} is missing`, result: r => withoutDeclaration(r, name)},
    ]),
  },
  refusedClients: {
    applies: fixture => Object.keys(fixture.refusedClients ?? {}).length > 0,
    met: ({fixture, facts}) => Object.keys(fixture.refusedClients).every(name => facts.clients[name] === "refused"),
    breaks: ({fixture}) => Object.keys(fixture.refusedClients).flatMap(name => [
      {name: `${name} checks`, result: r => {
        editOutputs(r, name, o => Object.assign(o, {verified: true, axioms: []}));
        r.gaps = r.gaps.filter(g => g.name !== name);
      }},
      {name: `${name} is missing`, result: r => withoutDeclaration(r, name)},
    ]),
  },
  // Outputs report declarations; constructors must instead be tested by clients.
  outputsAbsent: {
    applies: fixture => !!(fixture.absentOutputs?.length || fixture.absentOutputFamilies?.length),
    met: ({facts}) => facts.forbiddenOutputs.length === 0,
    breaks: ({fixture}) => [
      ...(fixture.absentOutputs ?? []).map(published),
      ...(fixture.absentOutputFamilies ?? []).flatMap(prefix => [published(prefix), published(`${prefix}.id`)]),
    ],
  },
  originalType: {
    applies: fixture => fixture.kind === "collision",
    met: ({fixture, facts}) => facts.originalType === fixture.originalType,
    breaks: ({fixture: {symbol}}) => [
      {name: `${symbol} has another type`, result: r => editOutputs(r, symbol, o => { o.type = "Bool"; })},
      {name: `${symbol} is refused`, result: r => editOutputs(r, symbol, o => { o.verified = false; })},
    ],
  },
  duplicateRefused: {
    applies: fixture => fixture.kind === "collision",
    met: ({facts}) => facts.duplicateRefused,
    breaks: ({fixture: {symbol}}) => [
      {name: "the duplicate is refused for another reason", result: r => { gap(r, symbol).reason = "Type mismatch: found Bool, expected Unit."; }},
      {name: "the duplicate is accepted", result: r => { r.gaps = r.gaps.filter(g => g.name !== symbol); }},
    ],
  },
  advice: {
    applies: fixture => fixture.kind === "lint",
    met: ({evidence, recognized}) => evidence.warnings.length === 0 || recognized,
    breaks: ({fixture, anchors}) => {
      const recognized = fixture.rewrite.advice.map(advice => ({...advice, ...anchors.rewrite}));
      const advised = (name, edit) => ({name, evidence: e => { e.warnings = structuredClone(recognized); edit(e.warnings); }});
      return [
        advised("advice has another message", w => { w[0].message = "x is unused in the body: rename it _x."; }),
        advised("advice names another declaration", w => { w[0].declaration = "unrelated"; }),
        advised("advice lies outside its rewrite", w => Object.assign(w[0], {start: 0, end: 1})),
        advised("advice has an empty span", w => { w[0].end = w[0].start; }),
        advised("advice includes another warning", w => { w.push({...w[0], code: "W705", message: "z is unused in the body: write M -> … instead of forall z : M. …."}); }),
        ...recognized.length > 1 ? [advised("advice is partial", w => { w.pop(); })] : [],
      ];
    },
  },
  refusals: {
    applies: fixture => fixture.kind === "unsupported-family",
    met: ({facts}) => facts.refusals.every(r => r.code === "E817" && r.words.every(Boolean) && r.unsupported),
    breaks: ({fixture: {refusedClients, refusalWords: words}}) => Object.keys(refusedClients).flatMap(name => {
      const focused = `Cannot derive ${words[0]}: ${words.slice(1).join(" depends on ")}`;
      const reason = (what, text) => ({name: `${name} ${what}`, result: r => { gap(r, name).reason = text; }});
      return [
        reason("omits the dependency", words.join(", ")),
        ...words.map(word => reason(`omits ${word}`, focused.replace(new RegExp(`\\b${word}\\b`), "other"))),
        reason("describes an arrow-typed operation", arrowRefusal),
        {name: `${name} has another code`, result: r => { gap(r, name).code = "E606"; }},
      ];
    }),
  },
  range: {
    applies: fixture => ["wildcard", "capture-range", "refusal-range"].includes(fixture.kind),
    met: ({facts}) => Object.values(facts.range).every(Boolean),
    breaks: ({fixture, anchors}) => {
      const region = anchors.scope ?? anchors.conflict, sites = anchors.token ? [anchors.token] : [anchors.binder, anchors.call];
      const inside = [region.start, region.start + 1];
      assert.ok(!sites.some(site => inside[0] <= site.start && inside[1] >= site.end), "the region must not start with its site");
      assert.ok(region.start > 0 || region.end < fixture.source.length, "the region must be narrower than the source");
      const located = (name, start, end) => ({name, result: r => { Object.assign(gap(r, fixture.diagnostic.name), {start, end}); }});
      return [
        located("an empty span at the site", sites[0].start, sites[0].start),
        located("a span inside the region that misses the site", ...inside),
        located("a span covering the site beyond the region", 0, fixture.source.length),
        {name: "an unlocated refusal", result: r => { const g = gap(r, fixture.diagnostic.name); delete g.start; delete g.end; }},
      ];
    },
  },
  links: {
    applies: fixture => fixture.kind === "links",
    met: ({fixture, facts}) => facts.links.every(links => links.length > 0
      && links.every(([name, target]) => name === fixture.observations.label && target === 0)),
    breaks: ({fixture: {observations: {label}}, anchors: {positions}}) => positions.flatMap((position, site) => {
      const here = link => link.start === position && link.end === position + label.length;
      const edit = (what, change) => ({name: `site ${site} ${what}`, result: r => r.links.filter(here).forEach(change)});
      return [
        edit("shows a freshened label", link => { link.name = `${label}1`; }),
        edit("targets another definition", link => { link.definitionStart = positions[0] + 1; }),
        edit("has no target", link => { delete link.definitionStart; }),
        {name: `site ${site} has no link`, result: r => { r.links = r.links.filter(link => !here(link)); }},
      ];
    }),
  },
  // Counterexamples come from the accepted diagnostics and the fixture's data,
  // never from the expectations under test: an expectation that loses its cause
  // must still meet the counterexample that changes that cause.
  diagnostics: {
    applies: () => true,
    met: ({fixture, result}) => matchDiagnostics(result.gaps, expectedDiagnostics(fixture)) !== null,
    breaks: ({fixture, result}) => {
      const declared = name => fixture.refusedClients?.[name] ?? (fixture.diagnostic?.name === name ? fixture.diagnostic : undefined);
      return [
        {name: "an unrelated diagnostic", result: r => { r.gaps.push({name: "unrelated", code: "E606", reason: "Type mismatch: found Bool, expected Unit."}); }},
        ...result.gaps.flatMap(({name, code, ...gap}, at) => {
          const label = `${name} ${code}`, cause = diagnosticCause({code, ...gap});
          const edit = (what, change) => ({name: `${label} ${what}`, result: r => change(r.gaps[at])});
          const pinned = needsCause.has(code) || declared(name)?.cause;
          if (pinned) assert.deepEqual(Object.keys(cause).sort(), [...causeFields[code]].sort(), `${label} must decode to its cause`);
          return [
            {name: `${label} is missing`, result: r => { r.gaps.splice(at, 1); }},
            {name: `${label} is duplicated`, result: r => { r.gaps.push({...r.gaps[at]}); }},
            // A duplicate refusal may use any code.
            ...fixture.kind === "collision" && name === fixture.symbol ? []
              : [edit("has another code", g => { g.code = code === "E606" ? "E343" : "E606"; })],
            ...pinned ? [
              edit("has an unrecognized cause", g => { g.reason = "An unrelated failure with the same diagnostic code"; }),
              ...Object.keys(cause).map(field => edit(`names another ${field}`, g => { g.reason = encodeCause(code, {...cause, [field]: "Other"}); })),
              ..."found" in cause ? [edit("swaps found and expected", g => { g.reason = encodeCause(code, {found: cause.expected, expected: cause.found}); })] : [],
            ] : [],
          ];
        }),
      ];
    },
  },
};
const requirementsFor = fixture => Object.entries(requirementChecks).filter(([, check]) => check.applies(fixture));
export const requirementNames = fixture => requirementsFor(fixture).map(([name]) => name);

// Compiler and lint results are collected once. Every judgment below is a pure
// function of this evidence, so audits can substitute plausible wrong results.
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
  return evidence;
}
export function observeEvidence(fixture, evidence) {
  const {anchors, recognized, result} = observed(fixture, evidence);
  const names = [...fixture.clients ?? [], ...Object.keys(fixture.refusedClients ?? {})];
  const facts = {gaps: gapNames(result), clients: Object.fromEntries(names.map(name => [name, clientState(find(result, name))])),
    rootCauses: rootCauses(result), dependencies: dependencies(result)};
  if (fixture.absentOutputs || fixture.absentOutputFamilies)
    facts.forbiddenOutputs = result.outputs.filter(({name}) => fixture.absentOutputs?.includes(name)
      || fixture.absentOutputFamilies?.some(prefix => name === prefix || name.startsWith(prefix + "."))).map(o => o.name).sort();
  const context = {fixture, evidence, anchors, recognized, result, facts};
  Object.assign(facts, kindFacts[fixture.kind]?.(context) ?? assert.fail(`Unknown observation kind: ${fixture.kind}`));
  return {facts, requirements: Object.fromEntries(requirementsFor(fixture).map(([name, check]) => [name, check.met(context)]))};
}
// `check` uses the existing program/module reader and test-owned disposal.
// The optional lint function is used by the harness's adversarial controls.
export async function observeCase(t, fixture, check, lintSource = lint) {
  const evidence = await collectEvidence(t, fixture, check, lintSource);
  return {...observeEvidence(fixture, evidence), evidence};
}
// Plausible wrong results for each requirement of an accepted observation.
export function counterexamples(fixture, evidence) {
  const context = {fixture, evidence, ...observed(fixture, evidence)};
  return requirementsFor(fixture).map(([name, check]) => [name, check.breaks(context).map(counterexample => ({
    name: counterexample.name,
    apply: target => counterexample.result ? counterexample.result(observed(fixture, target).result) : counterexample.evidence(target),
  }))]);
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
