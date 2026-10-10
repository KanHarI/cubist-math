import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {lint} from "../web/cubist/lint.mjs";
import {checkProgram} from "./check-program.mjs";
import {cases} from "./fixtures/frontend-generation.mjs";
import {observeCase, classifyCase, recordCase} from "./frontend-generation-contracts.mjs";

const module = await createCubical();
const check = (t, source) => checkProgram(t, source, {module});
const fixture = id => structuredClone(cases.find(c => c.id === id));
const assess = async (t, c, checker = check, lintSource = lint) => classifyCase(c, await observeCase(t, c, checker, lintSource));

// These exercise the compiler and classifier together: neither a fixture bug
// nor a different compiler symptom is allowed to pass as the recorded debt.
for (const [id, mutate, error] of [
  ["G2", c => { c.source = c.source.replace("import hlevels;", ""); }, /Unrecognized defect observation/],
  ["G1", c => { c.clients[0] = "orignal"; }, /Unrecognized defect observation/],
  ["G5", c => { c.source += "\ndef unrelated : Unit := Unit;"; }, /unrelated E606/],
  ["G8", c => { c.diagnostic.scope += " "; }, /diagnostic scope/],
  ["G9", c => { c.observations.sites++; }, /observation sites/],
  ["G10", c => { c.diagnostic.conflict += " missing"; }, /diagnostic conflict/],
]) test(`FG0 harness: ${id} fixture mistakes fail normally`, async t => {
  const c = fixture(id); mutate(c);
  await assert.rejects(assess(t, c), error);
});

test("FG0 harness: changed symptoms and additional failures cannot become TODOs", async t => {
  const c = fixture("G2");
  const original = await check(t, c.source);
  for (const change of [
    checked => { checked.result.gaps[0].code = "E814"; },
    checked => { checked.result.gaps.push({name: "unrelated", code: "E606", reason: "unrelated failure"}); },
  ]) {
    const modified = {...original, result: structuredClone(original.result)};
    change(modified);
    await assert.rejects(assess(t, c, async () => modified), /Unrecognized defect observation/);
  }
});

test("FG0 harness: missing or changed navigation is not the recorded freshening defect", async t => {
  const c = fixture("G9"), original = await check(t, c.source);
  const binder = c.source.indexOf(c.observations.scope) + c.observations.scope.indexOf("c");
  for (const change of [
    checked => { checked.result.links = checked.result.links.filter(link => link.start !== binder); },
    checked => { for (const link of checked.result.links) if (link.start === binder) link.definitionStart = binder + 1; },
  ]) {
    const modified = {...original, result: structuredClone(original.result)};
    change(modified);
    await assert.rejects(assess(t, c, async () => modified), /Unrecognized defect observation/);
  }
});

test("FG0 harness: only a recognized defect can set TODO; strict and active failures stay assertions", async t => {
  const c = fixture("G4-flat"), observation = await observeCase(t, c, check);
  let todos = 0;
  const context = {todo: () => todos++};
  assert.throws(() => recordCase(context, c, observation), {code: "ERR_ASSERTION"});
  assert.equal(todos, 1);
  assert.throws(() => recordCase(context, c, observation, {strict: true}), {code: "ERR_ASSERTION"});
  assert.throws(() => recordCase(context, {...c, knownDefect: undefined}, observation), {code: "ERR_ASSERTION"});
  assert.equal(todos, 1);
  observation.facts.gaps.push("unrelated E606");
  assert.throws(() => recordCase(context, c, observation), /Unrecognized defect observation/);
  assert.equal(todos, 1);
});

test("FG0 harness: a corrected flat case activates independently of the nested case", async t => {
  const flat = fixture("G4-flat");
  // A supported motive proves this case can pass; it does not claim to fix G4.
  flat.source = flat.source.replace("import hlevels;", "import hlevels; import nat;")
    .replace("def value(n : Bits) : M", "def value(n : Bits) : Nat")
    .replace("nil => c; cons(b, rest) => op(op(c));", "nil => zero; cons(b, rest) => succ(succ(zero));")
    .replace("= S.op(S.op(S.c)) { rfl; }", "= succ(succ(zero)) { rfl; }")
    .replace("= S.c { rfl; }", "= zero { rfl; }");
  const observation = await observeCase(t, flat, check);
  assert.equal(classifyCase(flat, observation, {strict: true}), "pass");
  assert.throws(() => classifyCase(flat, observation), /G4-flat unexpectedly passed/);
  delete flat.knownDefect;
  assert.equal(classifyCase(flat, observation), "pass");
  assert.equal(await assess(t, fixture("G4")), "known-defect");
});

test("FG0 harness: supplied client names, labels and scope drive navigation checks", async t => {
  const c = fixture("G9");
  const scope = "law l(z : M) : k(z) = op(z, z);";
  c.source = c.source.replace(c.observations.scope, scope).replace("def meaning(", "def renamed(");
  c.observations = {...c.observations, scope, label: "z"};
  c.clients = ["renamed"];
  delete c.knownDefect;
  assert.equal(await assess(t, c), "pass");
});

test("FG0 harness: grouped-only lint suppression leaves the single-binder defect visible", async t => {
  const suppressGrouped = source => lint(source).filter(w => !(w.code === "W706" && w.declaration === "T"));
  const grouped = fixture("G5"), single = fixture("G5-single");
  const corrected = await observeCase(t, grouped, check, suppressGrouped);
  assert.equal(classifyCase(grouped, corrected, {strict: true}), "pass");
  assert.throws(() => classifyCase(grouped, corrected), /G5 unexpectedly passed/);
  delete grouped.knownDefect;
  assert.equal(classifyCase(grouped, corrected), "pass");
  assert.equal(await assess(t, single, check, suppressGrouped), "known-defect");
});

for (const id of ["G12", "G12-inherited", "G12-initial"]) test(`FG0 harness: ${id} twice clients pass with a nonrecursive iter`, async t => {
  const c = fixture(id);
  c.source = c.source.replace("match n { zero => c; succ(k) => op(iter(k)); }", "match n { zero => c; succ(k) => match k { zero => op(c); succ(j) => op(op(c)); }; }");
  const observation = await observeCase(t, c, check);
  assert.equal(classifyCase(c, observation, {strict: true}), "pass");
  assert.throws(() => classifyCase(c, observation), /unexpectedly passed/);
  delete c.knownDefect;
  assert.equal(classifyCase(c, observation), "pass");
});
