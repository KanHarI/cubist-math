import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {cases} from "./fixtures/frontend-generation.mjs";
import {accepted, collectEvidence, observeCase, observeEvidence, unmet} from "./frontend-generation-contracts.mjs";

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
// can match neither the contract nor that observation.
const notDebt = (base, changed) => {
  assert.ok(unmet(changed).length, "a mistake must leave the contract unmet");
  assert.notDeepStrictEqual(changed.facts, base.facts, "a mistake must change the observation");
};
for (const [id, mutate] of [
  ["G2", c => { c.source = c.source.replace("import hlevels;", ""); }],
  ["G1", c => { c.clients[0] = "orignal"; }],
]) test(`FG0 harness: ${id} source and client mistakes cannot become TODOs`, async t => {
  const c = fixture(id), base = await observeCase(t, c, check);
  mutate(c);
  notDebt(base, await observeCase(t, c, check));
});
test("FG0 harness: changed symptoms and additional failures cannot become TODOs", async t => {
  const c = fixture("G2"), evidence = await collectEvidence(t, c, check), base = observeEvidence(c, evidence);
  for (const edit of [
    result => { result.gaps[0].code = "E814"; },
    result => { result.gaps.push({name: "unrelated", code: "E606", reason: "unrelated failure"}); },
  ]) notDebt(base, observe(c, evidence, edit));
});
test("FG0 harness: missing or changed navigation cannot become a TODO", async t => {
  const c = fixture("G9"), evidence = await collectEvidence(t, c, check), base = observeEvidence(c, evidence);
  const binder = c.source.indexOf(c.observations.scope) + c.observations.scope.indexOf("c");
  for (const edit of [
    result => { result.links = result.links.filter(link => link.start !== binder); },
    result => { for (const link of result.links) if (link.start === binder) link.definitionStart = binder + 1; },
  ]) notDebt(base, observe(c, evidence, edit));
});

test("FG0 harness: accepted controls reject refusals and assumptions", () => {
  const checked = outputs => ({get: name => outputs[name]});
  accepted(checked({d: {verified: true, axioms: []}}), ["d"]);
  assert.throws(() => accepted(checked({d: {verified: true, axioms: ["unproved"]}}), ["d"]), /d must not introduce assumptions/);
  assert.throws(() => accepted(checked({d: {verified: false, reason: "refused here"}}), ["d"]), /d: refused here/);
});
