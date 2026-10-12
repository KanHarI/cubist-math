import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {mkdtemp, readFile, rm, writeFile} from "node:fs/promises";
import {tmpdir} from "node:os";
import {join} from "node:path";
import {pathToFileURL} from "node:url";
import {inspect} from "node:util";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {cases} from "./fixtures/frontend-generation.mjs";
import {requirementConditions} from "./fixtures/frontend-generation-requirements.mjs";
import {supportedSources} from "./fixtures/frontend-generation-supported.mjs";
import * as contracts from "./frontend-generation-contracts.mjs";
import {collectEvidence, counterexamples, evidenceData, judgments, observeCase, observeEvidence, sourceAnchor, unmet,
  validateConditions, validateCoverage, validateFixture, validateObligations} from "./frontend-generation-contracts.mjs";
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
    // The fixing compiler's wording for Hom and Iso clients; the diagnostic
    // decoder also recognizes the permitted focused wordings.
    result.gaps = ["unsupported", "unsupported_iso"].map(name => ({name, code: "E817",
      reason: "T's models have no homomorphisms: its op's argument p depends on law l, whose transport and composition are not generated."}));
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
// Collected once per case, as data: the judgments below are pure functions of
// this evidence, so each program is disposed of once its evidence is copied.
const acceptedCases = new Map();
const acceptedCase = id => {
  if (!acceptedCases.has(id)) acceptedCases.set(id, (async () => {
    const c = fixture(id), programs = [];
    try {
      return {c, evidence: evidenceData(await acceptedEvidence[id]({after: dispose => programs.push(dispose)}, c))};
    } finally {
      for (const dispose of programs) dispose();
    }
  })());
  return acceptedCases.get(id);
};

// The audit of an accepted observation by a contract module: the observation
// and each permitted variation meet every requirement, and each counterexample
// violates its own condition. Returns the failures and the conditions that
// some counterexample violates alone; with `stop`, the first failure throws.
function audit(contract, c, evidence, stop = false) {
  const failures = [], alone = new Set();
  const fail = message => { if (stop) throw Error(message); failures.push(`${c.id}: ${message}`); };
  const judge = apply => {
    const changed = structuredClone(evidence);
    apply?.(changed);
    return contract.observeEvidence(c, changed);
  };
  const missing = contract.unmet(judge());
  if (missing.length) fail(`the accepted observation must meet every requirement; unmet: ${missing.join(", ")}`);
  for (const {name, apply} of contract.permitted(c, evidence)) {
    const missing = contract.unmet(judge(apply));
    if (missing.length) fail(`${name} must meet every requirement; unmet: ${missing.join(", ")}`);
  }
  for (const {requirement, condition, name, apply} of contract.counterexamples(c, evidence)) {
    const held = judge(apply).conditions[requirement];
    if (held[condition]) fail(`${name} must violate ${requirement}.${condition}`);
    else if (Object.values(held).filter(holds => !holds).length === 1) alone.add(`${requirement}.${condition}`);
  }
  return {failures, alone};
}
// Every condition carries its own plausible wrong results and every
// requirement its permitted variations, so a deleted or weakened check fails
// here, as does one that rejects a valid result.
for (const {id} of cases) test(`FG0 audit: ${id} accepts its observation and permitted variations and rejects each condition's counterexamples`, async () => {
  const {c, evidence} = await acceptedCase(id);
  assert.ok(contracts.counterexamples(c, evidence).length, `${id} needs counterexamples`);
  assert.deepEqual(audit(contracts, c, evidence).failures, []);
});
test("FG0 audit: duplicate diagnostic variations preserve optional code constraints", async () => {
  for (const id of Object.keys(duplicates)) for (const code of [undefined, "E604", "E872", "E999"]) {
    const {c, evidence} = structuredClone(await acceptedCase(id));
    // Pair by the complete matching, not by the fixture's diagnostic order.
    evidence.result.gaps.reverse();
    if (code !== undefined) {
      c.diagnostic.code = code;
      evidence.result.gaps.find(gap => gap.name === "N").code = code;
    }
    validateFixture(c);
    meets(observeEvidence(c, evidence));
    const variations = contracts.permitted(c, evidence).filter(({requirement}) => requirement === "diagnostics")
      .map(({apply}) => {
        const changed = structuredClone(evidence);
        apply(changed);
        return changed.result.gaps.find(gap => gap.name === "N");
      });
    assert.deepEqual([...new Set(variations.map(gap => gap.code))].sort(), code === undefined ? ["E604", "E872"] : [code]);
    // Both wordings remain exercised even when the code is fixed. Filtering
    // away a rejected variation would hide a matcher bug from the audit.
    for (const reason of ["Instruction kernel: Definition symbol is already registered.",
      "Duplicate declaration N: a declaration in this module already owns that name."])
      assert.ok(variations.some(gap => gap.reason === reason), `${id}: missing permitted wording ${reason}`);
    assert.deepEqual(audit(contracts, c, evidence).failures, []);
    if (code !== undefined) violates(observe(c, evidence, result => {
      result.gaps.find(gap => gap.name === "N").code = code === "E604" ? "E872" : "E604";
    }), "diagnostics");
  }
});
// A counterexample that violates two conditions leaves either unguarded, so
// each condition needs one that violates it alone, in some case.
test("FG0 audit: some counterexample violates each condition alone", async () => {
  const alone = new Set();
  for (const {id} of cases) {
    const {c, evidence} = await acceptedCase(id);
    for (const key of audit(contracts, c, evidence).alone) alone.add(key);
  }
  const stated = Object.entries(requirementConditions).flatMap(([requirement, conditions]) => conditions.map(condition => `${requirement}.${condition}`));
  assert.deepEqual(stated.filter(key => !alone.has(key)), []);
});

// Every comparison in the judging code must matter. A mutant changes one
// operator in a fact projection that conditions read, in a condition, or in
// the diagnostic field matchers. Judged over every case's accepted
// observation, permitted variations and counterexamples, some verdict must
// change; a surviving mutant is a check that no counterexample or permitted
// variation exercises. The cause decoder and the complete matching's search
// have their own tests below.
const mutations = [[/===/g, "!=="], [/!==/g, "==="], [/&&/g, "||"], [/\|\|/g, "&&"], [/>=/g, ">"], [/<=/g, "<"],
  [/(?<![=>])>(?![=>])/g, ">="], [/<(?![=<])/g, "<="], [/\.every\(/g, ".some("], [/\.some\(/g, ".every("], [/!(?![=!])/g, ""]];
function mutants(source, functions) {
  return functions.flatMap(code => {
    const text = code.toString(), at = source.indexOf(text);
    assert.ok(at !== -1 && source.indexOf(text, at + 1) === -1, `judging code must occur once: ${text.slice(0, 80)}`);
    return mutations.flatMap(([pattern, replacement]) => [...text.matchAll(pattern)].map(({index, 0: operator}) => {
      const start = at + index, line = source.slice(0, start).split("\n").length;
      return {site: `${line}: ${operator} → ${replacement || "(removed)"} in ${source.split("\n")[line - 1].trim()}`,
        source: source.slice(0, start) + replacement + source.slice(start + operator.length)};
    }));
  });
}
const survives = (contract, accepted) => {
  try {
    for (const {c, evidence} of accepted) audit(contract, c, evidence, true);
    return true;
  } catch {
    return false;
  }
};
test("FG0 audit: every comparison in the judging code is exercised", async t => {
  const accepted = [];
  for (const {id} of cases) accepted.push(await acceptedCase(id));
  const contractsURL = new URL("./frontend-generation-contracts.mjs", import.meta.url);
  const diagnosticsURL = new URL("./frontend-generation-diagnostics.mjs", import.meta.url);
  const contractsSource = await readFile(contractsURL, "utf8"), diagnosticsSource = await readFile(diagnosticsURL, "utf8");
  // Mutants live outside the tree, so their relative imports become absolute.
  const absolute = source => source.replace(/(from ")(\.\.?\/[^"]+)"/g, (_, from, path) => `${from}${new URL(path, contractsURL).href}"`);
  const directory = await mkdtemp(join(tmpdir(), "fg0-mutants-"));
  t.after(() => rm(directory, {recursive: true, force: true}));
  let index = 0;
  const load = async (source, diagnostics) => {
    const path = join(directory, `mutant-${index++}.mjs`);
    source = absolute(source);
    if (diagnostics) {
      await writeFile(`${path}.diagnostics.mjs`, diagnostics);
      assert.ok(source.includes(diagnosticsURL.href), "the contracts must import the diagnostics module");
      source = source.replace(diagnosticsURL.href, pathToFileURL(`${path}.diagnostics.mjs`).href);
    }
    await writeFile(path, source);
    return import(pathToFileURL(path).href);
  };
  const survivors = [];
  for (const {site, source} of mutants(contractsSource, judgments()))
    if (survives(await load(source), accepted)) survivors.push(`contracts ${site}`);
  const matching = [matchesDiagnostic, ...Object.values(diagnosticFields).map(({matches}) => matches)];
  for (const {site, source} of mutants(diagnosticsSource, matching))
    if (survives(await load(contractsSource, source), accepted)) survivors.push(`diagnostics ${site}`);
  assert.deepEqual(survivors, []);
});

// Reported counterexamples and permitted alternatives beyond the tables.
// These examples preserve the old matchers' vocabulary while changing its
// meaning. State them independently of the decoder and generated mutations.
for (const id of Object.keys(duplicates)) test(`FG0 audit: ${id} rejects unrelated uses of duplicate-refusal vocabulary`, async () => {
  const {c, evidence} = await acceptedCase(id);
  for (const reason of [
    "Internal elaboration error: c is already bound.",
    "The last tube does not overlap that tube, or already agrees with it.",
    "Duplicate declaration: Other",
    "Duplicate declaration Other: a declaration in this module already owns that name.",
    "N is not a duplicate declaration.",
  ]) violates(observe(c, evidence, result => { result.gaps.find(g => g.name === "N").reason = reason; }), "diagnostics");
});
test("FG0 audit: both G3 clients require the operation, argument and law in their stated roles", async () => {
  const {c, evidence} = await acceptedCase("G3");
  for (const name of ["unsupported", "unsupported_iso"]) for (const reason of [
    "T's models have no homomorphisms: its op's argument l depends on law p, whose transport and composition are not generated.",
    "Cannot derive p: op depends on l",
    "Cannot derive l: p depends on op",
    "Cannot derive op: l depends on p",
    "op parameter p is independent of law l",
    "op parameter p does not depend on law l",
    "op's argument p depends on carrier l",
    "T's models have no homomorphisms: its op's result mentions a carrier on both sides of an arrow, and such homomorphisms need not compose.",
  ]) violates(observe(c, evidence, result => { result.gaps.find(g => g.name === name).reason = reason; }), "diagnostics");
});
test("FG0 audit: G6 permits an attached cause but requires the actual parent", async t => {
  const c = fixture("G6"), evidence = await acceptedEvidence.G6(t, c);
  const child = reason => result => { result.gaps.find(g => g.name === "C").reason = reason; };
  meets(observe(c, evidence, child("Untranslated dependency: P (P failed: Untranslated name: Undefined at 2:8) at 3:8")));
  for (const reason of ["Untranslated dependency: Q (Q failed: P at 2:8) at 3:8", "Untranslated name: P at 3:8"])
    violates(observe(c, evidence, child(reason)), "diagnostics");
  violates(observe(c, evidence, result => { result.gaps.find(g => g.name === "P").reason = "Untranslated name: Other (mentions Undefined)"; }), "diagnostics");
});
// Range tables permit the site and the whole region; a call is in between.
test("FG0 audit: G12-range accepts a span over the whole call", async t => {
  const c = fixture("G12-range"), evidence = await acceptedEvidence["G12-range"](t, c);
  const call = reference(c.source, c.diagnostic.scope, "iter(n)");
  meets(observe(c, evidence, result => Object.assign(result.gaps[0], call)));
});
// A case outside the registry: the requirement map names G9's own client, so
// a renamed client belongs to another case ID.
test("FG0 audit: supplied client names, labels and scope drive navigation checks", async t => {
  const c = {...fixture("G9"), id: "G9-renamed"}, scope = "law l(z : M) : k(z) = op(z, z);";
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
// linter, and the rewrite's results are observer results over the real
// original. These hold whatever the linter or the compiler does with the
// arrow form, including a later simplification that preserves its clients.
for (const id of ["G5", "G5-single"]) test(`FG0 audit: ${id} judges identified advice by its rewrite and applies no other advice`, async t => {
  const c = fixture(id), identified = c.rewrite.advice.map(advice => ({...advice, ...validateFixture(c).rewrite}));
  const edited = c.source.replace(c.rewrite.from, c.rewrite.to), {result: original} = await check(t, c.source);
  const lost = structuredClone(original), [client] = c.clients;
  lost.outputs.find(o => o.name === client).verified = false;
  lost.gaps.push({name: client, code: "E817", reason: "T's models have no homomorphisms."});
  const collect = async (warnings, rewritten) => {
    let checks = 0;
    const results = new Map([[c.source, original], [edited, rewritten]]);
    const evidence = await collectEvidence(t, c, async (t, source) => { checks++; return {result: results.get(source)}; }, () => structuredClone(warnings));
    return {checks, evidence, observation: observeEvidence(c, evidence)};
  };
  const quiet = await collect([]);
  assert.equal(quiet.checks, 1);
  meets(quiet.observation);
  // Identified advice authorizes exactly its rewrite, and the rewritten
  // program's clients decide: a rewrite that preserves them meets the
  // contract, and one that loses a client does not.
  const preserving = await collect(identified, structuredClone(original));
  assert.equal(preserving.checks, 2);
  meets(preserving.observation);
  const losing = await collect(identified, lost);
  assert.equal(losing.checks, 2);
  assert.equal(losing.observation.requirements.advice, true);
  assert.deepEqual(losing.observation.facts.gaps, [`${client} E817`]);
  violates(losing.observation, "clients");
  // Every advice counterexample, issued by the linter, must leave the source
  // unrewritten; the requirement's own list drives this check.
  for (const {name, apply} of counterexamples(c, quiet.evidence).filter(({requirement}) => requirement === "advice")) {
    const changed = {};
    apply(changed);
    const {checks, observation} = await collect(changed.warnings, lost);
    assert.equal(checks, 1, `${name}: unrecognized advice must not apply the assumed rewrite`);
    violates(observation, "advice");
  }
});

// Advice is a set on both sides: a case may state its identified advice in any
// order, as the linter may issue it in any order.
test("FG0 audit: G5 may state its identified advice in any order", async () => {
  const {c, evidence} = structuredClone(await acceptedCase("G5"));
  c.rewrite.advice.reverse();
  assert.deepEqual(audit(contracts, c, evidence).failures, []);
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
  ["G1", "without its duplicate cause", c => { delete c.diagnostic.cause; }],
  ["G1-reverse", "with another duplicate subject", c => { c.diagnostic.cause.duplicate = "Other"; }],
  ["G1-initial", "with a bare refusal code", c => { c.refusedClients.leaked_one = "E343"; }],
  ["G3", "without its Hom refusal cause", c => { delete c.refusedClients.unsupported.cause; }],
  ["G3", "without its Iso refusal cause", c => { delete c.refusedClients.unsupported_iso.cause; }],
  ["G3", "without the dependent law", c => { delete c.refusedClients.unsupported.cause.law; }],
  ["G3", "with swapped argument and law", c => { c.refusedClients.unsupported.cause = {operation: "op", argument: "l", law: "p"}; }],
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
test("FG0 audit: diagnostic causes recognize roles and subjects independently of fixtures", () => {
  const duplicate = {name: "Fresh", cause: {duplicate: "Fresh"}};
  validateDiagnostic(duplicate);
  for (const [code, reason] of [
    ["E604", "Duplicate declaration: Fresh"],
    ["E872", "Duplicate declaration Fresh: a declaration in this module already owns that name."],
    ["E604", "Instruction kernel: Definition symbol is already registered."],
    ["E999", "Duplicate declaration: Fresh at 2:3"],
  ]) {
    const actual = {name: "Fresh", code, reason};
    assert.deepEqual(diagnosticCause(actual), {duplicate: "Fresh"});
    assert.ok(matchesDiagnostic(actual, duplicate));
  }
  const cause = {operation: "combine", argument: "value", law: "identity"};
  for (const reason of [
    "Algebra's models have no homomorphisms: its combine's argument value depends on law identity, whose transport and composition are not generated.",
    "Cannot derive combine: value depends on identity",
    "combine parameter value has unsupported transport through law identity",
    "combine's argument value depends on law identity at 2:3",
  ]) assert.deepEqual(diagnosticCause({code: "E817", reason}), cause);
  for (const [code, reason] of [
    ["E604", "Internal elaboration error: Fresh is already bound."],
    ["E817", "combine parameter value is independent of law identity"],
    ["E817", "combine's argument value depends on carrier identity"],
    ["E817", "Cannot derive combine: value depends on identity, but transport is supported"],
  ]) assert.deepEqual(diagnosticCause({name: "Fresh", code, reason}), {reason});
  assert.throws(() => validateDiagnostic({name: "x", cause}), /only a duplicate declaration may omit its code/);
  assert.throws(() => validateDiagnostic({name: "x", cause: {duplicate: "Fresh", extra: "ignored"}}), /cause fields/);
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
  // Outside the registry, no witness fixes this case's anchors or requires
  // its cause.
  const c = {...fixture("G8"), id: "G8-repeated"};
  delete c.diagnostic.cause; c.diagnostic.token = "t0";
  assert.throws(() => validateFixture(c), /diagnostic token must occur once/);
  c.diagnostic.tokenOccurrence = 1;
  validateFixture(c);
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
  // A condition deleted from a requirement's table, with its counterexamples.
  const {links, ...others} = requirementConditions;
  assert.throws(() => validateConditions({...others, links: links.filter(condition => condition !== "start")}), /stated conditions/);
  // A witness whose requirement no longer applies fails the mapping check.
  weakens("G1-initial", c => { delete c.absentOutputs; }, /atomic-publication: G1-initial must check outputsAbsent/);
  weakens("G1", c => { delete c.refusedClients; }, /name-availability: G1 must check refusedClients/);
  weakens("G12", c => { delete c.refusedClients; }, /recursive-step: G12 must check refusedClients/);
  for (const [id, error] of [["G9", /G9 must check links/], ["G8", /G8 must check range/], ["G5", /G5 must check advice/]])
    weakens(id, c => { c.kind = "completion"; }, error);
  // Independently stated witnesses survive a weakened but applicable requirement.
  weakens("G1-initial", c => { c.absentOutputs = ["N.model", "N.fold_map"]; }, /atomic-publication: G1-initial must keep absent output N.fold/);
  weakens("G1-initial", c => { delete c.refusedClients.leaked_mul; }, /name-availability: G1-initial must keep refused client leaked_mul/);
  weakens("G2", c => { c.refusedClients.lowered = {code: "E606"}; }, /universe-contribution: G2 must keep refused client lowered/);
  weakens("G2", c => { c.clients = c.clients.filter(name => name !== "preserves"); }, /universe-contribution: G2 must keep client preserves/);
  weakens("G1", c => { delete c.diagnostic; }, /ownership: G1 must keep diagnostic N/);
  weakens("G1", c => { c.clients = c.clients.filter(name => name !== "original"); }, /ownership: G1 must keep client original/);
  weakens("G1-reverse", c => { c.clients = c.clients.filter(name => name !== "original"); }, /ownership: G1-reverse must keep client original/);
  weakens("G3", c => { c.clients = c.clients.filter(name => name !== "usable"); }, /unsupported-transport: G3 must keep client usable/);
  weakens("G6", c => { c.clients = []; }, /failed-dependency: G6 must keep client independent/);
  weakens("G3", c => { delete c.refusedClients.unsupported.cause; }, /unsupported-transport: G3 must keep refused client unsupported/);
  weakens("G3", c => { delete c.refusedClients.unsupported_iso.cause; }, /unsupported-transport: G3 must keep refused client unsupported_iso/);
  weakens("G4", c => { c.clients = c.clients.filter(name => name !== "off_computation"); }, /match-computation: G4 must keep client off_computation/);
  weakens("G5-single", c => { c.clients = c.clients.filter(name => name !== "N.fold"); }, /lint-interface: G5-single must keep client N.fold/);
  weakens("G8", c => { delete c.diagnostic.cause; }, /wildcard-diagnostic: G8 must keep diagnostic h/);
  weakens("G9", c => { c.observations.sites = 3; }, /written-navigation: G9 must keep observation sites/);
  weakens("G12", c => { c.refusedClients.wrong.code = "E604"; }, /recursive-step: G12 must keep refused client wrong/);
  for (const id of ["G12", "G12-inherited", "G12-initial"])
    weakens(id, c => { c.clients = c.clients.filter(name => name !== "computation2"); }, new RegExp(`recursive-step: ${id} must keep client computation2`));
  // Anchors, rewrites and other single-valued expectations are kept exactly.
  // Range and advice counterexamples are placed from them, so narrowing a
  // site, widening a region or replacing the rewrite would otherwise move the
  // counterexamples with it; several such edits also left the records unchanged.
  for (const [id, edit, error] of [
    ["G8", c => { c.diagnostic.token = "1"; }, /wildcard-diagnostic: G8 must keep diagnostic h's token/],
    ["G8", c => { c.diagnostic.scope = "def h(x : T) : T := match x { t0 => t0; _ => t1; };"; }, /G8 must keep diagnostic h's scope/],
    ["G10", c => { c.diagnostic.call = "k"; }, /capture-origin: G10 must keep diagnostic T's call/],
    ["G10", c => { Object.assign(c.diagnostic, {conflict: "(match n return M { zero => c; succ(c) => k(c); })", binderOccurrence: 1}); },
      /G10 must keep diagnostic T's conflict, diagnostic T's binderOccurrence/],
    ["G12-range", c => { c.diagnostic.token = "i"; }, /type-unfolding-origin: G12-range must keep diagnostic T's token/],
    ["G12-range", c => { Object.assign(c.diagnostic, {scope: "def iter(n : Nat) : M := match n { zero => c; succ(k) => op(iter(k)); };\n  law nope(n : Nat) : iter(n) = c;", tokenOccurrence: 2}); },
      /G12-range must keep diagnostic T's scope, diagnostic T's tokenOccurrence/],
    ["G9", c => { c.observations.scope = "law l(c : M) : k(c) = op(c, c);\n}"; }, /written-navigation: G9 must keep observation scope/],
    ["G5", c => { c.rewrite.to = "forall x, y : M. M "; }, /lint-interface: G5 must keep rewrite replacement/],
    ["G5-single", c => { c.rewrite.from = "op : forall x : M. M"; c.rewrite.to = "op : M -> M"; }, /G5-single must keep rewrite target, rewrite replacement/],
    ["G5", c => { c.rewrite.advice.pop(); }, /G5 must keep rewrite advice/],
    ["G1", c => { c.symbol = "independent"; }, /ownership: G1 must keep collision symbol/],
    ["G1-reverse", c => { c.originalType = "Unit"; }, /ownership: G1-reverse must keep original type/],
    ["G6", c => { c.parent = "C"; c.child = "P"; }, /failed-dependency: G6 must keep failed parent/],
    ["G6", c => { c.cause = "Other"; }, /G6 must keep parent cause/],
    // An anchor its witness does not state is kept by no witness.
    ["G1", c => { c.diagnostic.scope = "def N : Unit := tt;"; }, /ownership: G1 must keep diagnostic N's scope/],
  ]) weakens(id, edit, error);
  // An expectation that no witness keeps could be deleted or changed
  // unnoticed; every expectation a registered case states must have one, and
  // a misspelled expectation field is not silently ignored.
  for (const [id, edit, error] of [
    ["G2", c => { c.clients.push("unnamed"); }, /G2: no obligation's witness keeps its client unnamed/],
    ["G4", c => { c.refusedClients.unnamed = {code: "E606"}; }, /G4: no obligation's witness keeps its refused client unnamed/],
    ["G1", c => { c.absentOutputs = ["N.unnamed"]; }, /G1: no obligation's witness keeps its absent output N.unnamed/],
    ["G3", c => { c.absentOutputFamilies.push("T.Unnamed"); }, /G3: no obligation's witness keeps its absent output family T.Unnamed/],
    ["G4", c => { c.diagnostic = {name: "T.value", code: "E546"}; }, /G4: no obligation's witness keeps its diagnostic T.value/],
    ["G11", c => { c.observations = {scope: "def kk(c : M) : M := k(c);", label: "c", sites: 2}; }, /G11: no obligation's witness keeps its observations/],
    ["G4-flat", c => { c.rewrite = {from: "op(op(c))", to: "op(c)", advice: []}; }, /G4-flat: no obligation's witness keeps its rewrite/],
    ["G12", c => { c.symbol = "T"; c.originalType = "Unit"; }, /G12: no obligation's witness keeps its collision symbol/],
    ["G2", c => { c.client = ["T.Hom"]; }, /G2: client is not an expectation a witness can keep/],
  ]) weakens(id, edit, error);
});
