import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {checkProgram} from "./check-program.mjs";
import {cases} from "./fixtures/frontend-generation.mjs";
import {observeCase, classifyCase, validateCoverage} from "./frontend-generation-contracts.mjs";

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
  G4: unitMotive,
  "G4-flat": unitMotive,
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
};
function unitMotive(c) {
  c.source = c.source.replace("def value(n : Bits) : M", "def value(n : Bits) : Unit")
    .replaceAll("=> c;", "=> tt;").replace("= S.c { rfl; }", "= tt { rfl; }");
}
function renameParameter(c) {
  c.source = c.source.replace(/def kk\([^;]+;/, declaration => declaration.replace(/\bc\b/g, "z"));
}
function nonrecursive(c) {
  c.source = c.source.replace("match n { zero => c; succ(k) => op(iter(k)); }", "c");
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
