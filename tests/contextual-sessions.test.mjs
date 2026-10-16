import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import { checkProgram } from "./check-program.mjs";
import { contextualScenarios, probeSource } from "./fixtures/contextual-sessions.mjs";

const module = await create();
for (const c of contextualScenarios) {
  test(`CB0 contextual source control: ${c.id}`, async t => {
    assert.equal(c.source.split(c.marker).length, 2, "the selected source occurrence is unique");
    const { result, get } = await checkProgram(t, c.source, { module });
    assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), c.gaps);
    for (const name of c.clients) {
      assert.ok(get(name).verified, name);
      assert.deepEqual(get(name).axioms, [], name);
    }
  });
  for (const probe of c.probes ?? []) test(`CB0 contextual query control: ${c.id}, ${probe.id}`, async t => {
    const { result, get } = await checkProgram(t, probeSource(c, probe), { module });
    assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), probe.gaps);
    if (!probe.gaps.length) for (const name of c.clients) {
      assert.ok(get(name).verified, name);
      assert.deepEqual(get(name).axioms, [], name);
    }
  });
}
// These remain independent source controls. Session execution, instance
// selection and lifetime are covered by contextual-replay, contextual-commands,
// scope-points and cubical-worker; the CB6 roadmap maps each former TODO.

test("contextual probe edits reject missing, duplicated and unchanged anchors", () => {
  const probe = {id:"edited", edit:{anchor:"needle", replacement:"query"}};
  for (const source of ["no occurrence", "needle needle"])
    assert.throws(() => probeSource({id:"control",source},probe), /exactly once/);
  assert.throws(() => probeSource({id:"control",source:"needle"},
    {id:"unchanged",edit:{anchor:"needle",replacement:"needle"}}), /must change the source/);
  assert.equal(probeSource({id:"control",source:"before needle after"},probe), "before query after");
});
