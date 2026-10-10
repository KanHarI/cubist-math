import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {checkProgram} from "./check-program.mjs";
import {cases} from "./fixtures/frontend-generation.mjs";
import {observeCase, classifyCase, validateCoverage, validateFixture, sourceAnchor, validateObligations} from "./frontend-generation-contracts.mjs";

const module = await createCubical();
const check = (t, source) => checkProgram(t, source, {module});
const fixture = id => structuredClone(cases.find(c => c.id === id));
const changed = (checked, modify) => {
  const result = structuredClone(checked.result);
  modify(result);
  return {...checked, result, get: name => {
    const output = result.outputs.find(o => o.name === name);
    assert.ok(output, `missing declaration ${name}`);
    return output;
  }};
};
const passes = (c, observation) => {
  assert.equal(classifyCase(c, observation, {strict: true}), "pass");
  assert.throws(() => classifyCase(c, observation), /unexpectedly passed/);
  assert.equal(classifyCase({...c, knownDefect: undefined}, observation), "pass");
};
const refuses = (c, observation) => assert.throws(
  () => classifyCase({...c, knownDefect: undefined}, observation), {code: "ERR_ASSERTION"});

// Every case must distinguish its recorded debt from a different primary cause
// with the SAME diagnostic code (or a different target for the link-only case).
// Synthetic result edits test the observer boundary, not compiler correctness.
for (const original of cases) test(`FG0 audit: ${original.id} recognizes debt and rejects a different cause`, async t => {
  const c = structuredClone(original), cache = new Map();
  const cachedCheck = async (t, source) => {
    if (!cache.has(source)) cache.set(source, await check(t, source));
    return cache.get(source);
  };
  assert.equal(classifyCase(c, await observeCase(t, c, cachedCheck)), "known-defect");
  const otherCause = async (t, source) => changed(await cachedCheck(t, source), result => {
    const primary = result.gaps.find(g => g.code !== "E340");
    if (primary) primary.reason = primary.code === "E606"
      ? "Type mismatch: found Bool, expected Unit."
      : "An unrelated failure with the same diagnostic code";
    else result.links = result.links.map(link => ({...link, definitionStart: c.source.length}));
  });
  await assert.rejects(async () => classifyCase(c, await observeCase(t, c, otherCause)),
    error => error.code === "ERR_ASSERTION" || /Unrecognized defect observation/.test(error.message));
  if ([...cache.values()].some(checked => checked.result.gaps.some(g => g.code === "E340"))) {
    const otherDependency = async (t, source) => changed(await cachedCheck(t, source), result => {
      const dependency = result.gaps.find(g => g.code === "E340");
      if (dependency) dependency.reason = "Untranslated dependency: Other";
    });
    await assert.rejects(async () => classifyCase(c, await observeCase(t, c, otherDependency)), /Unrecognized defect observation/);
  }
});

// Supported source variants check real clients. They establish that the
// acceptance predicate is reachable, without claiming to fix the original bug.
const supported = {
  G2: c => { c.source = c.source.replace("op(A : U0, x : A) : M", "op(x : M) : M"); },
  G4: natMotive,
  "G4-flat": natMotive,
  G9: c => {
    const scope = "law l(z : M) : k(z) = op(z, z);";
    c.source = c.source.replace(c.observations.scope, scope);
    c.observations = {...c.observations, scope, label: "z"};
  },
  G11: renameParameter,
  "G11-grouped-dependent": renameParameter,
  "G11-inherited": renameParameter,
  "G11-initial": renameParameter,
  G12: nonrecursive,
  "G12-inherited": nonrecursive,
  "G12-initial": nonrecursive,
  "G12-shadowed": c => { c.source = c.source.replace("twice(iter : Nat -> M, n : Nat) : M := op(iter(n))", "twice(local : Nat -> M, n : Nat) : M := op(local(n))"); },
};
function natMotive(c) {
  c.source = c.source.replace("import hlevels;", "import hlevels; import nat;")
    .replace(/def value[^;]+(?:;[^}]+)*?};/, declaration => declaration
      .replace(": M :=", ": Nat :=").replace(/\bop\(/g, "succ(").replace(/\bc\b/g, "zero"))
    .replaceAll("S.op(S.op(S.c))", "succ(succ(zero))").replaceAll("S.op(S.c)", "succ(zero)").replaceAll("= S.c {", "= zero {");
}
function renameParameter(c) {
  c.source = c.source.replace(/def kk\([^;]+;/, declaration => declaration.replace(/\bc\b/g, "z"));
}
function nonrecursive(c) {
  c.source = c.source.replace("match n { zero => c; succ(k) => op(iter(k)); }", "match n { zero => c; succ(k) => op(c); }");
}
for (const [id, transform] of Object.entries(supported)) test(`FG0 audit: ${id} accepts a supported source control`, async t => {
  const c = fixture(id); transform(c);
  passes(c, await observeCase(t, c, check));
});

const duplicates = {
  G1: "inductive N : U0 { c; }\n",
  "G1-initial": "initial N : Monoid(U0);\n",
  "G1-reverse": "def N : Unit := tt;\n",
  "G1-same-kind": "def N : U0 := Unit;\n",
};
for (const [id, duplicate] of Object.entries(duplicates)) test(`FG0 audit: ${id} accepts preserved bindings and rejects a lost client`, async t => {
  const c = fixture(id);
  const original = await check(t, c.source.replace(duplicate, ""));
  assert.deepEqual(original.result.gaps, []);
  // Real original declarations and clients, with the intended duplicate
  // refusal injected at the observer boundary. No generated term is fabricated.
  const corrected = changed(original, result => result.gaps.push({name: "N", code: "E604", reason: "Duplicate declaration: N"}));
  passes(c, await observeCase(t, c, async () => corrected));
  const lost = changed(corrected, result => { result.outputs = result.outputs.filter(o => o.name !== c.clients[0]); });
  refuses(c, await observeCase(t, c, async () => lost));
  const forbidden = {G1: ["c"], "G1-initial": ["N.model", "N.fold_map", "N.fold"]}[id] ?? [];
  for (const name of forbidden) {
    const leaked = changed(corrected, result => result.outputs.push({...original.get("independent"), name}));
    refuses(c, await observeCase(t, c, async () => leaked));
  }
});

test("FG0 audit: G3 accepts focused refusals and rejects a leaked family", async t => {
  const c = fixture("G3"), original = await check(t, c.source);
  for (const reason of ["op parameter p has unsupported transport through law l", "Cannot derive op: p depends on l"]) {
    const corrected = changed(original, result => {
      result.outputs = result.outputs.filter(o => !/^T\.(Hom|Iso)(\.|$)/.test(o.name));
      result.gaps = [{name: "unsupported", code: "E817", reason}];
    });
    passes(c, await observeCase(t, c, async () => corrected));
    const leaked = changed(corrected, result => result.outputs.push(original.get("T.Hom")));
    refuses(c, await observeCase(t, c, async () => leaked));
  }
});

for (const id of ["G5", "G5-single"]) test(`FG0 audit: ${id} binds its rewrite to actual advice`, async t => {
  const c = fixture(id), original = await check(t, c.source);
  passes(c, await observeCase(t, c, async () => original, () => []));
  for (const mutate of [
    warning => ({...warning, message: "x is unused in the body: rename it _x."}),
    warning => ({...warning, declaration: "unrelated"}),
    warning => ({...warning, start: 0, end: 1}),
  ]) {
    let checks = 0;
    const observation = await observeCase(t, c, async () => { checks++; return original; }, source => lint(source).map(mutate));
    assert.equal(checks, 1, "unrecognized advice must not apply the assumed rewrite");
    assert.throws(() => classifyCase(c, observation), /Unrecognized defect observation/);
    refuses(c, observation);
  }
  if (id === "G5") {
    const partial = await observeCase(t, c, async () => original, source => lint(source).slice(0, 1));
    assert.throws(() => classifyCase(c, partial), /Unrecognized defect observation/);
  }
});

test("FG0 audit: G6 permits an attached cause but requires the actual parent", async t => {
  const c = fixture("G6"), original = await check(t, c.source);
  for (const reason of ["Untranslated dependency: P at 3:8",
    "Untranslated dependency: P (P failed: Untranslated name: Undefined at 2:8) at 3:8"]) {
    const corrected = changed(original, result => Object.assign(result.gaps.find(g => g.name === "C"), {code: "E340", reason}));
    passes(c, await observeCase(t, c, async () => corrected));
  }
  const wrong = changed(original, result => Object.assign(result.gaps.find(g => g.name === "C"), {code: "E340", reason: "Untranslated dependency: Parent"}));
  refuses(c, await observeCase(t, c, async () => wrong));
});

for (const id of ["G8", "G12-range"]) test(`FG0 audit: ${id} accepts token and wider spans and rejects a nearby token`, async t => {
  const c = fixture(id), original = await check(t, c.source), {diagnostic: d} = c;
  // These examples state the specification independently of the fixture's
  // token/endpoint expectations, so a wrong fixture cannot redefine success.
  const reference = id === "G8" ? "t1" : "iter";
  const scope = c.source.indexOf(d.scope), token = scope + d.scope.lastIndexOf(reference);
  const valid = [[token, token + reference.length], [scope, scope + d.scope.length]];
  if (id === "G12-range") valid.push([token, token + "iter(n)".length]);
  const at = (start, end, swapped = false) => changed(original, result => Object.assign(result.gaps[0], {
    code: d.code, start, end,
    ...(id === "G8" ? {reason: swapped
      ? "Type mismatch: found t0 = t1, expected t1 = t1."
      : "Type mismatch: found t1 = t1, expected t0 = t1."} : {}),
  }));
  for (const [start, end] of valid) passes(c, await observeCase(t, c, async () => at(start, end)));
  for (const [start, end] of [[token, token], [scope, scope + 1], [0, c.source.length]])
    refuses(c, await observeCase(t, c, async () => at(start, end)));
  if (id === "G8") refuses(c, await observeCase(t, c, async () => at(token, token + reference.length, true)));
});

test("FG0 audit: G10 accepts either conflict origin and rejects an unrelated origin", async t => {
  const c = fixture("G10"), original = await check(t, c.source), {diagnostic: d} = c;
  const conflict = c.source.indexOf(d.conflict), binder = conflict + "succ(".length;
  const call = conflict + d.conflict.indexOf(d.call);
  const at = (start, end) => changed(original, result => Object.assign(result.gaps[0], {start, end}));
  for (const [start, end] of [[binder, binder + 1], [call, call + d.call.length], [conflict, conflict + d.conflict.length]])
    passes(c, await observeCase(t, c, async () => at(start, end)));
  refuses(c, await observeCase(t, c, async () => at(conflict, conflict + 1)));
});

test("FG0 audit: every case has an acceptance control and the manifest preserves group ownership", async () => {
  const ids = [...Object.keys(supported), ...Object.keys(duplicates), "G3", "G5", "G5-single", "G6", "G8", "G10", "G12-range"];
  assert.deepEqual(ids.sort(), cases.map(c => c.id).sort());
  const manifest = await readFile(new URL("./fixtures/frontend-generation.md", import.meta.url), "utf8");
  validateCoverage(manifest, cases);
  assert.throws(() => validateCoverage(manifest.replace("| `G12-range` | G12 |", "| `G12-range` | G11 |"), cases), /coverage matrix/);
});

// These are semantic mutants of supported source controls. They keep the
// program well formed, but make a plausible wrong equation true. This is a
// different boundary from changing a diagnostic on an already-failing case.
for (const id of ["G4", "G4-flat", "G12", "G12-inherited", "G12-initial", "G12-shadowed"])
  test(`FG0 audit: ${id} rejects a well-typed wrong computation`, async t => {
    const c = fixture(id); supported[id](c);
    passes(c, await observeCase(t, c, check));
    if (id.startsWith("G4")) c.source = c.source.replace(/match n \{[^}]+\}/, "zero");
    else if (id === "G12-shadowed") c.source = c.source.replace("op(local(n))", "op(c)");
    else c.source = c.source.replace("match n { zero => c; succ(k) => op(c); }", "c");
    const observation = await observeCase(t, c, check);
    assert.equal(observation.facts.clients[id === "G12-shadowed" ? "captured" : "wrong"], "checked");
    assert.deepEqual(observation.facts.gaps, id === "G4" ? ["computation E606", "off_computation E606"] : [`${id === "G12-shadowed" ? "intended" : "computation"} E606`]);
    refuses(c, observation);
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

test("FG0 audit: requirements survive deletion of both a case and its manifest row", async () => {
  const manifest = await readFile(new URL("./fixtures/frontend-generation.md", import.meta.url), "utf8");
  const removed = cases.filter(c => c.id !== "G12-shadowed");
  const matchingManifest = manifest.replace(/^\| `G12-shadowed`[^\n]*\n/m, "");
  assert.throws(() => validateCoverage(matchingManifest, removed), /lexical-shadowing: missing witness G12-shadowed/);
  for (const [id, field, error] of [["G1", "absentMembers", /publication requirement/], ["G12", "refusedClients", /wrong-equation witness/]]) {
    const weakened = structuredClone(cases); delete weakened.find(c => c.id === id)[field];
    assert.throws(() => validateObligations(weakened), error);
  }
});
