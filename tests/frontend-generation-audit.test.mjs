import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import {inspect} from "node:util";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {cases} from "./fixtures/frontend-generation.mjs";
import {supportedSources} from "./fixtures/frontend-generation-supported.mjs";
import {collectEvidence, counterexamples, diagnostics, observeCase, observeEvidence, sourceAnchor, unmet,
  validateCoverage, validateFixture, validateObligations} from "./frontend-generation-contracts.mjs";
import {causeFields, diagnosticCause, diagnosticFields, encodeCause, matchesDiagnostic, matchesDiagnostics,
  validateDiagnostic} from "./frontend-generation-diagnostics.mjs";

// The contract audit judges observations by their requirements alone. It never
// reads defect records or classifies cases, so activating a case, or retiring
// every record, leaves each test here unchanged.
const module = await createCubical();
const check = (t, source) => checkProgram(t, source, {module});
const fixture = id => structuredClone(cases.find(c => c.id === id));
// Evidence edits replace part of a compiler result; judgments read only evidence.
const observe = (c, evidence, edit) => {
  const changed = structuredClone(evidence);
  edit(changed.result);
  return observeEvidence(c, changed);
};
const meets = observation => assert.deepEqual(unmet(observation), [], inspect(observation.facts, {depth: null}));
const violates = (observation, ...names) => {
  const missing = unmet(observation);
  assert.ok(missing.length, `must violate a requirement: ${inspect(observation.facts, {depth: null})}`);
  for (const name of names) assert.ok(missing.includes(name), `must violate ${name}; unmet: ${missing.join(", ")}`);
};

// Each case's accepted observation: a supported source checked by the compiler,
// or an observer result layered over real checked outputs. Observer edits test
// the acceptance boundary; they do not establish that the compiler is fixed.
const duplicates = {
  G1: "inductive N : U0 { c; }\n",
  "G1-initial": "initial N : Monoid(U0);\n",
  "G1-reverse": "def N : Unit := tt;\n",
  "G1-same-kind": "def N : U0 := Unit;\n",
};
async function preservedBinding(t, c) {
  const {result} = await check(t, c.source.replace(duplicates[c.id], ""));
  // Without the duplicate only the refused clients fail. The duplicate's
  // refusal is synthetic; bindings and client verdicts are real.
  assert.deepEqual(result.gaps.map(g => `${g.name} ${g.code}`).sort(),
    Object.entries(c.refusedClients ?? {}).map(([name, {code}]) => `${name} ${code}`).sort());
  result.gaps.push({name: "N", code: "E604", reason: "Duplicate declaration: N"});
  return {result};
}
// Spans state the specification independently of the fixture's anchors.
const reference = (source, scope, text) => {
  const start = source.indexOf(scope) + scope.lastIndexOf(text);
  return {start, end: start + text.length};
};
const acceptedEvidence = {
  ...Object.fromEntries(Object.entries(supportedSources).map(([id, transform]) =>
    [id, (t, c) => { transform(c); return collectEvidence(t, c, check); }])),
  ...Object.fromEntries(Object.keys(duplicates).map(id => [id, preservedBinding])),
  G3: async (t, c) => {
    const {result} = await check(t, c.source);
    result.outputs = result.outputs.filter(o => !/^T\.(Hom|Iso)(\.|$)/.test(o.name));
    // The fixing compiler's wording; other focused wordings are tested below.
    result.gaps = [{name: "unsupported", code: "E817",
      reason: "T's models have no homomorphisms: its op's argument p depends on law l, whose transport and composition are not generated."}];
    return {result};
  },
  G5: (t, c) => collectEvidence(t, c, check, () => []),
  "G5-single": (t, c) => collectEvidence(t, c, check, () => []),
  G6: async (t, c) => {
    const {result} = await check(t, c.source);
    Object.assign(result.gaps.find(g => g.name === "C"), {code: "E340", reason: "Untranslated dependency: P at 3:8"});
    return {result};
  },
  G8: async (t, c) => {
    const {result} = await check(t, c.source);
    Object.assign(result.gaps[0], {code: "E606", reason: "Type mismatch: found t1 = t1, expected t0 = t1.",
      ...reference(c.source, c.diagnostic.scope, "t1")});
    return {result};
  },
  G10: async (t, c) => {
    const {result} = await check(t, c.source), start = c.source.indexOf("succ(c) =>") + "succ(".length;
    Object.assign(result.gaps[0], {start, end: start + 1});
    return {result};
  },
  "G12-range": async (t, c) => {
    const {result} = await check(t, c.source);
    Object.assign(result.gaps[0], reference(c.source, c.diagnostic.scope, "iter"));
    return {result};
  },
};
test("FG0 audit: every case has an accepted observation", () => {
  assert.deepEqual(Object.keys(acceptedEvidence).sort(), cases.map(c => c.id).sort());
});
// Every requirement carries its own plausible wrong results. Each must violate
// that requirement, so a deleted or weakened check fails here.
for (const original of cases) test(`FG0 audit: ${original.id} accepts its supported observation and rejects each requirement's counterexamples`, async t => {
  const c = structuredClone(original), evidence = await acceptedEvidence[c.id](t, c);
  meets(observeEvidence(c, evidence));
  for (const [requirement, breaks] of counterexamples(c, evidence)) {
    assert.ok(breaks.length, `${c.id}: ${requirement} needs a counterexample`);
    for (const {name, apply} of breaks) {
      const broken = structuredClone(evidence);
      apply(broken);
      assert.equal(observeEvidence(c, broken).requirements[requirement], false, `${c.id}: ${name} must violate ${requirement}`);
    }
  }
});

// Permitted alternatives and reported counterexamples beyond the generic ones.
test("FG0 audit: G3 accepts other focused refusal wordings", async t => {
  const c = fixture("G3"), evidence = await acceptedEvidence.G3(t, c);
  for (const reason of ["op parameter p has unsupported transport through law l", "Cannot derive op: p depends on l"])
    meets(observe(c, evidence, result => { result.gaps[0].reason = reason; }));
});
test("FG0 audit: G6 permits an attached cause but requires the actual parent", async t => {
  const c = fixture("G6"), evidence = await acceptedEvidence.G6(t, c);
  const child = reason => result => { result.gaps.find(g => g.name === "C").reason = reason; };
  meets(observe(c, evidence, child("Untranslated dependency: P (P failed: Untranslated name: Undefined at 2:8) at 3:8")));
  for (const reason of ["Untranslated dependency: Q (Q failed: P at 2:8) at 3:8", "Untranslated name: P at 3:8"])
    violates(observe(c, evidence, child(reason)), "diagnostics");
  violates(observe(c, evidence, result => { result.gaps.find(g => g.name === "P").reason = "Untranslated name: Other (mentions Undefined)"; }), "diagnostics");
});
for (const id of ["G8", "G12-range"]) test(`FG0 audit: ${id} accepts the reference and wider spans within its scope`, async t => {
  const c = fixture(id), evidence = await acceptedEvidence[id](t, c), {scope} = c.diagnostic;
  const text = id === "G8" ? "t1" : "iter", token = reference(c.source, scope, text), start = c.source.indexOf(scope);
  const valid = [[token.start, token.end], [start, start + scope.length]];
  if (id === "G12-range") valid.push([token.start, token.start + "iter(n)".length]);
  for (const [start, end] of valid) meets(observe(c, evidence, result => Object.assign(result.gaps[0], {start, end})));
});
test("FG0 audit: G10 accepts the binder, the helper call or the whole conflicting clause", async t => {
  const c = fixture("G10"), evidence = await acceptedEvidence.G10(t, c), {conflict} = c.diagnostic;
  const at = c.source.indexOf(conflict), binder = at + "succ(".length, call = at + conflict.indexOf("k(c)");
  for (const [start, end] of [[binder, binder + 1], [call, call + "k(c)".length], [at, at + conflict.length]])
    meets(observe(c, evidence, result => Object.assign(result.gaps[0], {start, end})));
});
test("FG0 audit: supplied client names, labels and scope drive navigation checks", async t => {
  const c = fixture("G9"), scope = "law l(z : M) : k(z) = op(z, z);";
  c.source = c.source.replace(c.observations.scope, scope).replace("def meaning(", "def renamed(");
  c.observations = {...c.observations, scope, label: "z"};
  c.clients = ["renamed"];
  meets(await observeCase(t, c, check));
});

// These programs establish the observable API independently of absentOutputs.
// A constructor is usable through a client but never a top-level output.
for (const [id, declaration, clients, outputs] of [
  ["G1", "inductive N : U0 { c; }", {leaked_c: "c"}, []],
  ["G1-initial", "import hlevels; import algebra; initial N : Monoid(U0);",
    {leaked_one: "N.one", leaked_mul: "N.mul"}, ["N.model", "N.fold_map", "N.fold"]],
]) test(`FG0 audit: ${id} detects available constructors through real clients`, async t => {
  const positive = await check(t, declaration + Object.entries(clients).map(([client, name]) => `\ndef ${client} := ${name};`).join(""));
  assert.deepEqual(positive.result.gaps, []);
  for (const [client, name] of Object.entries(clients)) {
    assert.equal(positive.get(client).verified, true);
    assert.deepEqual(positive.get(client).axioms, []);
    assert.ok(!positive.result.outputs.some(output => output.name === name), `${name} is not an output`);
  }
  const c = fixture(id), evidence = await preservedBinding(t, c);
  meets(observeEvidence(c, evidence));
  // Replay each real client verdict into the observer control. This represents
  // a leaked binding without inventing an output for the constructor itself.
  for (const client of Object.keys(clients)) {
    const observation = observe(c, evidence, result => {
      result.outputs = result.outputs.map(output => output.name === client ? positive.get(client) : output);
      result.gaps = result.gaps.filter(gap => gap.name !== client);
    });
    assert.equal(observation.facts.clients[client], "checked");
    assert.equal(observation.requirements.outputsAbsent ?? true, true, "name availability has its own observer");
    violates(observation, "refusedClients");
  }
  for (const name of outputs) {
    const observation = observe(c, evidence, result => { result.outputs.push(positive.get(name)); });
    assert.equal(observation.requirements.refusedClients, true, "output absence has its own observer");
    violates(observation, "outputsAbsent");
  }
});
test("FG0 audit: collision, name and equation refusals compose with per-client codes", async t => {
  const c = fixture("G1");
  c.source += "\ndef wrong : Unit := Unit;";
  c.refusedClients.wrong = {code: "E606"};
  const evidence = await preservedBinding(t, c);
  meets(observeEvidence(c, evidence));
  for (const [requirement, edit] of [
    ["diagnostics", result => { for (const gap of result.gaps) if (gap.name !== "N") gap.code = gap.code === "E343" ? "E606" : "E343"; }],
    ["diagnostics", result => { result.gaps.push({name: "unrelated", code: "E343", reason: "Untranslated name: absent"}); }],
    ["diagnostics", result => { result.gaps.push({...result.gaps.find(g => g.name === "leaked_c")}); }],
    ["diagnostics", result => { result.gaps = result.gaps.filter(g => g.name !== "leaked_c"); }],
    ["refusedClients", result => { result.outputs = result.outputs.filter(output => output.name !== "leaked_c"); }],
  ]) violates(observe(c, evidence, edit), requirement);
});

// Advice comes from each case's identified edit, never from the current
// linter, so these hold whether or not the linter still issues it.
for (const id of ["G5", "G5-single"]) test(`FG0 audit: ${id} judges identified advice by its rewrite and applies no other advice`, async t => {
  const c = fixture(id), identified = c.rewrite.advice.map(advice => ({...advice, ...validateFixture(c).rewrite}));
  const edited = c.source.replace(c.rewrite.from, c.rewrite.to), rewritten = await check(t, edited);
  const results = new Map([[c.source, await check(t, c.source)], [edited, rewritten]]);
  const collect = async warnings => {
    let checks = 0;
    const evidence = await collectEvidence(t, c, async (t, source) => { checks++; return results.get(source); }, () => structuredClone(warnings));
    return {checks, evidence, observation: observeEvidence(c, evidence)};
  };
  const quiet = await collect([]);
  assert.equal(quiet.checks, 1);
  meets(quiet.observation);
  // Identified advice authorizes exactly its rewrite, judged by the same
  // clients. The arrow form changes the generated interface (G5's premise),
  // so advice that remains, as when only grouped advice is suppressed, fails.
  const advised = await collect(identified);
  assert.equal(advised.checks, 2);
  assert.equal(advised.observation.requirements.advice, true);
  assert.deepEqual(advised.observation.facts.gaps, diagnostics(rewritten));
  violates(advised.observation, "clients");
  // Every advice counterexample, issued by the linter, must leave the source
  // unrewritten; the requirement's own list drives this check.
  const [, breaks] = counterexamples(c, quiet.evidence).find(([requirement]) => requirement === "advice");
  for (const {name, apply} of breaks) {
    const changed = {};
    apply(changed);
    const {checks, observation} = await collect(changed.warnings);
    assert.equal(checks, 1, `${name}: unrecognized advice must not apply the assumed rewrite`);
    violates(observation, "advice");
  }
});

// Weakened expectations fail validation before any program is checked: causes
// fixed by their code or an obligation, witnesses and diagnostic fields.
for (const [id, mutation, mutate] of [
  ["G10", "without its cause", c => { delete c.diagnostic.cause; }],
  ["G10", "without its captured field", c => { delete c.diagnostic.cause.field; }],
  ["G10", "naming another helper", c => { c.diagnostic.cause.helper = "kk"; }],
  ["G12-range", "without its cause", c => { delete c.diagnostic.cause; }],
  ["G12-range", "with a misspelled cause field", c => { c.diagnostic.cause = {recursive: "iter", contex: "field type"}; }],
  ["G8", "without its endpoints", c => { delete c.diagnostic.cause; }],
  ["G2", "without its lowering endpoints", c => { delete c.refusedClients.lowered.cause; }],
  ["G1", "without its constructor's cause", c => { delete c.refusedClients.leaked_c.cause; }],
  ["G1-initial", "with a bare refusal code", c => { c.refusedClients.leaked_one = "E343"; }],
  ["G3", "without its refusal words", c => { delete c.refusalWords; }],
  ["G3", "without the dependent law", c => { c.refusalWords = ["op", "p"]; }],
  ["G4", "with a cause no obligation requires", c => { c.refusedClients.wrong.cause = {found: "A", expected: "B"}; }],
  ["G11", "with an uncompared diagnostic field", c => { c.refusedClients.captured.reason = "Type mismatch"; }],
]) test(`FG0 audit: ${id} ${mutation} is rejected before checking`, async t => {
  const c = fixture(id); mutate(c);
  let checks = 0;
  await assert.rejects(observeCase(t, c, async () => { checks++; }), {code: "ERR_ASSERTION"});
  assert.equal(checks, 0);
});

test("FG0 audit: diagnostic matching is complete and independent of expectation order", () => {
  const actual = [{name: "x", code: "E606", reason: "Type mismatch: found A, expected B."},
    {name: "x", code: "E606", reason: "Type mismatch: found C, expected D."}];
  const any = {name: "x", code: "E606"}, exact = {name: "x", code: "E606", cause: {found: "A", expected: "B"}};
  assert.ok(matchesDiagnostics(actual, [any, exact]));
  assert.ok(matchesDiagnostics(actual, [exact, any]));
  assert.ok(!matchesDiagnostics(actual, [exact, exact]));
  assert.ok(!matchesDiagnostics(actual, [any]));
  assert.ok(!matchesDiagnostics(actual.slice(0, 1), [any, exact]));
  assert.ok(!matchesDiagnostics(actual.map(gap => ({...gap, name: "y"})), [any, exact]));
});
// The matcher and the audit's diagnostic counterexamples share one field
// table, and an expectation may state only fields from it.
test("FG0 audit: every field an expectation can state is compared and has counterexamples", () => {
  const actual = {name: "x", code: "E606", reason: "Type mismatch: found A, expected B."};
  const expected = {name: "x", code: "E606", cause: {found: "A", expected: "B"}};
  validateDiagnostic(expected);
  assert.ok(matchesDiagnostic(actual, expected));
  for (const [field, {perturb}] of Object.entries(diagnosticFields)) {
    const changes = perturb(actual);
    assert.ok(changes.length, `${field} needs a counterexample`);
    for (const {what, change} of changes) {
      const gap = structuredClone(actual);
      change(gap);
      assert.ok(!matchesDiagnostic(gap, expected), `a diagnostic that ${what} must not match`);
    }
  }
  assert.throws(() => validateDiagnostic({...expected, reason: "anything"}), /unknown diagnostic field reason/);
});
test("FG0 audit: encoded causes decode to the same cause", () => {
  for (const [code, fields] of Object.entries(causeFields)) {
    const cause = Object.fromEntries(fields.map(field => [field, field === "context" ? "field type" : `some_${field}`]));
    assert.deepEqual(diagnosticCause({code, reason: encodeCause(code, cause)}), cause, code);
    assert.deepEqual(diagnosticCause({code, reason: `${encodeCause(code, cause)} at 3:8`}), cause, `${code} with a location`);
  }
  const other = {recursive: "iter", context: "a law's body"};
  assert.deepEqual(diagnosticCause({code: "E845", reason: encodeCause("E845", other)}), other);
});

// These are semantic mutants of supported source controls. They keep the
// program well formed, but make a plausible wrong equation true. This is a
// different boundary from changing a diagnostic on an already-failing case.
for (const id of ["G4", "G4-flat", "G12-shadowed"])
  test(`FG0 audit: ${id} rejects a well-typed wrong computation`, async t => {
    const c = fixture(id); supportedSources[id](c);
    meets(await observeCase(t, c, check));
    if (id.startsWith("G4")) c.source = c.source.replace(/match n \{[^}]+\}/, "zero");
    else c.source = c.source.replace("op(local(n))", "op(c)");
    const observation = await observeCase(t, c, check);
    assert.equal(observation.facts.clients[id === "G12-shadowed" ? "captured" : "wrong"], "checked");
    assert.deepEqual(observation.facts.gaps, id === "G4" ? ["computation E606", "off_computation E606"] : [`${id === "G12-shadowed" ? "intended" : "computation"} E606`]);
    violates(observation, "clients", "refusedClients");
  });

// Each wrong source states the behavior to distinguish and the clients whose
// verdicts separate it. A branch executing is insufficient: its result must
// depend on the recursive result. Expectations do not come from fixture data.
for (const id of ["G12", "G12-inherited", "G12-initial"])
  for (const {name, body, gaps, clients, requirements} of [
    {name: "constant result", body: "c", gaps: ["computation E606", "computation2 E606"],
      clients: {base: "checked", computation: "refused", computation2: "refused", wrong: "checked"}, requirements: ["clients", "refusedClients"]},
    {name: "ignored recursive result", body: "match n { zero => c; succ(k) => op(c); }",
      gaps: ["computation2 E606", "wrong E606"],
      clients: {base: "checked", computation: "checked", computation2: "refused", wrong: "refused"}, requirements: ["clients"]},
  ]) test(`FG0 audit: ${id} rejects ${name}`, async t => {
    const c = fixture(id), recursive = "match n { zero => c; succ(k) => op(iter(k)); }";
    sourceAnchor(c.source, recursive, "recursive body");
    c.source = c.source.replace(recursive, body);
    const observation = await observeCase(t, c, check);
    assert.deepEqual(observation.facts.gaps, gaps);
    for (const [client, state] of Object.entries(clients)) assert.equal(observation.facts.clients[client], state, client);
    violates(observation, ...requirements);
  });

for (const [id, field, label] of [
  ["G8", "diagnostic.scope", "diagnostic scope"],
  ["G10", "diagnostic.conflict", "diagnostic conflict"],
  ["G9", "observations.scope", "observation scope"],
  ["G5", "rewrite.from", "lint rewrite target"],
]) test(`FG0 audit: ${field} rejects ambiguous anchors before checking`, async t => {
  const c = fixture(id), [parent, key] = field.split(".");
  c.source += `\n// duplicate: ${c[parent][key]}`;
  let checks = 0;
  await assert.rejects(observeCase(t, c, async () => { checks++; }), new RegExp(`${label} must occur once`));
  assert.equal(checks, 0);
});

test("FG0 audit: repeated inner tokens require an explicit occurrence", () => {
  assert.throws(() => sourceAnchor("x x", "x", "token"), /must occur once/);
  assert.deepEqual(sourceAnchor("x x", "x", "token", 1), {start: 2, end: 3});
  assert.throws(() => sourceAnchor("x x", "x", "token", 2), /existing site/);
  const c = fixture("G8"); c.diagnostic.token = "t0";
  assert.throws(() => validateFixture(c), /diagnostic token must occur once/);
});

test("FG0 audit: the manifest preserves group ownership", async () => {
  const manifest = await readFile(new URL("./fixtures/frontend-generation.md", import.meta.url), "utf8");
  validateCoverage(manifest, cases);
  assert.throws(() => validateCoverage(manifest.replace("| `G12-range` | G12 |", "| `G12-range` | G11 |"), cases), /coverage matrix/);
});
test("FG0 audit: requirements survive deletion of a case, its manifest row or its requirement", async () => {
  const manifest = await readFile(new URL("./fixtures/frontend-generation.md", import.meta.url), "utf8");
  const removed = cases.filter(c => c.id !== "G12-shadowed");
  const matchingManifest = manifest.replace(/^\| `G12-shadowed`[^\n]*\n/m, "");
  assert.throws(() => validateCoverage(matchingManifest, removed), /lexical-shadowing: missing witness G12-shadowed/);
  const weakens = (id, edit, error) => {
    const weakened = structuredClone(cases);
    edit(weakened.find(c => c.id === id));
    assert.throws(() => validateObligations(weakened), error);
  };
  // A witness whose requirement no longer applies fails the mapping check.
  weakens("G1-initial", c => { delete c.absentOutputs; }, /atomic-publication: G1-initial must check outputsAbsent/);
  weakens("G1", c => { delete c.refusedClients; }, /name-availability: G1 must check refusedClients/);
  weakens("G12", c => { delete c.refusedClients; }, /recursive-step: G12 must check refusedClients/);
  for (const [id, error] of [["G9", /G9 must check links/], ["G8", /G8 must check range/], ["G3", /G3 must check refusals/], ["G5", /G5 must check advice/]])
    weakens(id, c => { c.kind = "completion"; }, error);
  // Independently stated witnesses survive a weakened but applicable requirement.
  weakens("G1-initial", c => { c.absentOutputs = ["N.model", "N.fold_map"]; }, /atomic-publication: G1-initial must keep absent output N.fold/);
  weakens("G1-initial", c => { delete c.refusedClients.leaked_mul; }, /name-availability: G1-initial must keep refused client leaked_mul/);
  weakens("G2", c => { c.refusedClients.lowered = {code: "E606"}; }, /universe-contribution: G2 must keep refused client lowered/);
  weakens("G2", c => { c.clients = c.clients.filter(name => name !== "preserves"); }, /universe-contribution: G2 must keep client preserves/);
  weakens("G3", c => { c.refusalWords = ["op", "p"]; }, /unsupported-transport: G3 must keep refusal word l/);
  weakens("G4", c => { c.clients = c.clients.filter(name => name !== "off_computation"); }, /match-computation: G4 must keep client off_computation/);
  weakens("G5-single", c => { c.clients = c.clients.filter(name => name !== "N.fold"); }, /lint-interface: G5-single must keep client N.fold/);
  weakens("G8", c => { delete c.diagnostic.cause; }, /wildcard-diagnostic: G8 must keep diagnostic h/);
  weakens("G9", c => { c.observations.sites = 3; }, /written-navigation: G9 must keep 4 observation sites/);
  weakens("G12", c => { c.refusedClients.wrong.code = "E604"; }, /recursive-step: G12 must keep refused client wrong/);
  for (const id of ["G12", "G12-inherited", "G12-initial"])
    weakens(id, c => { c.clients = c.clients.filter(name => name !== "computation2"); }, new RegExp(`recursive-step: ${id} must keep client computation2`));
});
