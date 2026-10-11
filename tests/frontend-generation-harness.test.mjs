import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {cases} from "./fixtures/frontend-generation.mjs";
import {knownDefects} from "./fixtures/frontend-generation-defects.mjs";
import {accepted, collectEvidence, observeCase, observeEvidence, unmet} from "./frontend-generation-contracts.mjs";
import {classifyCase, recordCase} from "./frontend-generation-lifecycle.mjs";

const module = await createCubical();
const check = (t, source) => checkProgram(t, source, {module});
const fixture = id => structuredClone(cases.find(c => c.id === id));
// Evidence edits replace part of a compiler result; judgments read only evidence.
const observe = (c, evidence, edit) => {
  const changed = structuredClone(evidence);
  edit(changed.result);
  return observeEvidence(c, changed);
};

// Fixture mistakes and unmet prerequisites are ordinary failures, never debt.
// Metadata and prerequisites are assertions before observation.
for (const [id, mutate, error] of [
  ["G5", c => { c.source += "\ndef unrelated : Unit := Unit;"; }, /original interface must check before its rewrite/],
  ["G8", c => { c.diagnostic.scope += " "; }, /diagnostic scope/],
  ["G9", c => { c.observations.sites++; }, /observation sites/],
  ["G10", c => { c.diagnostic.conflict += " missing"; }, /diagnostic conflict/],
]) test(`FG0 harness: ${id} fixture mistakes fail before observation`, async t => {
  const c = fixture(id); mutate(c);
  await assert.rejects(observeCase(t, c, check), error);
});

// A source or client mistake, a changed symptom or changed navigation must
// leave the contract unmet and differ from the case's own observation, so it
// can match neither the contract nor a record of that observation. The record
// is synthetic: these hold whether or not the case is still recorded.
const notDebt = (c, base, changed) => {
  assert.ok(unmet(changed).length, "a mistake must leave the contract unmet");
  assert.throws(() => classifyCase(changed, {id: c.id, record: base.facts}), /Unrecognized defect observation/);
};
for (const [id, mutate] of [
  ["G2", c => { c.source = c.source.replace("import hlevels;", ""); }],
  ["G1", c => { c.clients[0] = "orignal"; }],
]) test(`FG0 harness: ${id} source and client mistakes cannot become TODOs`, async t => {
  const c = fixture(id), base = await observeCase(t, c, check);
  mutate(c);
  notDebt(c, base, await observeCase(t, c, check));
});
test("FG0 harness: changed symptoms and additional failures cannot become TODOs", async t => {
  const c = fixture("G2"), evidence = await collectEvidence(t, c, check), base = observeEvidence(c, evidence);
  for (const edit of [
    result => { result.gaps[0].code = "E814"; },
    result => { result.gaps.push({name: "unrelated", code: "E606", reason: "unrelated failure"}); },
  ]) notDebt(c, base, observe(c, evidence, edit));
});
test("FG0 harness: missing or changed navigation cannot become a TODO", async t => {
  const c = fixture("G9"), evidence = await collectEvidence(t, c, check), base = observeEvidence(c, evidence);
  const binder = c.source.indexOf(c.observations.scope) + c.observations.scope.indexOf("c");
  for (const edit of [
    result => { result.links = result.links.filter(link => link.start !== binder); },
    result => { for (const link of result.links) if (link.start === binder) link.definitionStart = binder + 1; },
  ]) notDebt(c, base, observe(c, evidence, edit));
});

test("FG0 harness: accepted controls reject refusals and assumptions", () => {
  const checked = outputs => ({get: name => outputs[name]});
  accepted(checked({d: {verified: true, axioms: []}}), ["d"]);
  assert.throws(() => accepted(checked({d: {verified: true, axioms: ["unproved"]}}), ["d"]), /d must not introduce assumptions/);
  assert.throws(() => accepted(checked({d: {verified: false, reason: "refused here"}}), ["d"]), /d: refused here/);
});

// The expected-failure lifecycle, retired with the records at RC0. The
// classifier is a pure function of an observation and a record, so it is
// tested with synthetic observations that no case's activation can disturb.
const failing = {facts: {gaps: ["x E606"]}, requirements: {clients: false, diagnostics: true}};
const passing = {facts: {gaps: []}, requirements: {clients: true, diagnostics: true}};
test("FG0 lifecycle: only an exact record sets TODO; strict, unrecorded and changed failures stay assertions", () => {
  const record = structuredClone(failing.facts), changed = structuredClone(failing), c = {id: "X", phase: "FG0"};
  changed.facts.gaps.push("unrelated E606");
  assert.equal(classifyCase(failing, {id: "X", record}), "known-defect");
  assert.throws(() => classifyCase(changed, {id: "X", record}), /Unrecognized defect observation/);
  for (const options of [{id: "X", record, strict: true}, {id: "X"}])
    assert.throws(() => classifyCase(failing, options), {code: "ERR_ASSERTION"});
  let todos = 0;
  const context = {todo: () => todos++};
  assert.throws(() => recordCase(context, c, failing, {record}), {code: "ERR_ASSERTION"});
  assert.equal(todos, 1);
  for (const options of [{record, strict: true}, {}])
    assert.throws(() => recordCase(context, c, failing, options), {code: "ERR_ASSERTION"});
  assert.throws(() => recordCase(context, c, changed, {record}), /Unrecognized defect observation/);
  assert.equal(todos, 1);
});
test("FG0 lifecycle: a met contract with an outstanding record is an unexpected pass", () => {
  const record = structuredClone(failing.facts);
  assert.throws(() => classifyCase(passing, {id: "X", record}), /X unexpectedly passed/);
  assert.equal(classifyCase(passing, {id: "X", record, strict: true}), "pass");
  assert.equal(classifyCase(passing, {id: "X"}), "pass");
  let todos = 0;
  recordCase({todo: () => todos++}, {id: "X", phase: "FG0"}, passing, {});
  assert.equal(todos, 0);
});
test("FG0 lifecycle: every record belongs to a case", () => {
  for (const id of Object.keys(knownDefects)) assert.ok(cases.some(c => c.id === id), `${id}: record without a case`);
});

// Per record: the current observation is recognized, and changing any one
// primary cause or dependency target (navigation for the link-only case) is a
// different observation, even with the same diagnostic codes. Removing a
// record removes its test.
for (const [id, record] of Object.entries(knownDefects)) test(`FG0 lifecycle: ${id} recognizes its debt and no different cause`, async t => {
  const c = fixture(id), evidence = await collectEvidence(t, c, check);
  const classify = changed => classifyCase(observeEvidence(c, changed), {id, record});
  assert.equal(classify(evidence), "known-defect");
  const observed = changed => changed.rewritten ?? changed.result;
  const edits = observed(evidence).gaps.map(({code}, index) => result => {
    result.gaps[index].reason = code === "E340" ? "Untranslated dependency: Other"
      : code === "E606" ? "Type mismatch: found Bool, expected Unit." : "An unrelated failure with the same diagnostic code";
  });
  if (!edits.length) edits.push(result => { result.links = result.links.map(link => ({...link, definitionStart: c.source.length})); });
  for (const edit of edits) {
    const changed = structuredClone(evidence);
    edit(observed(changed));
    assert.throws(() => classify(changed), /Unrecognized defect observation/);
  }
});
