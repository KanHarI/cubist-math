import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import create from "../web/dist/cubical.mjs";
import { checkProgram } from "./check-program.mjs";
import { contextualScenarios, sessionLifecycle } from "./fixtures/contextual-sessions.mjs";

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
  // Intentionally no fake session or module-import substitute. Replace each
  // TODO with the real scope-point API and execute its script in CB1/CB6.
  test.todo(`${c.phase} contextual session: ${c.id}`);
}
for (const contract of sessionLifecycle) test.todo(`CB6 contextual lifetime: ${contract}`);
