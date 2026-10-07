// Each Cubist test module's inlined errors, warnings and outputs are the
// checker's: every diagnostic and print is a comment directly above the
// declaration or directive it belongs to, and nothing else
// (tools/inline-errors.mjs --write writes them). The modules are checked in
// SHARDS test files, each its share (every SHARDS-th module), so that the
// test runner checks them in parallel: in one file, the check is the
// slowest test of npm test by far.
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { cubistTestModules } from "../web/cubist/modules.mjs";
import { checkedModule, reported, stated } from "../tools/inline-errors.mjs";

export const SHARDS = 4;

export function inlinedShard(shard) {
  const names = cubistTestModules.filter((_, k) => k % SHARDS === shard);
  test(`Cubist test modules ${shard + 1} of ${SHARDS}: inlined errors, warnings and outputs are the checker's`, async () => {
    const module = await createCubical();
    for (const name of names) {
      const { source, result } = await checkedModule(name, module);
      assert.ok(result.outputs.length || result.evaluations.length || result.prints.length, `${name} declares nothing`);
      const items = reported(source, result, name);
      assert.deepEqual(stated(source), items,
        `${name}: its checked comments differ from the check; run node tools/inline-errors.mjs --write ${name}`);
      // Each diagnostic has a code (web/diagnostics.mjs): one without is a
      // message the registry missed.
      for (const { label, text } of items)
        if (label !== "Output") assert.match(text, /^[EKW]\d{3}: /, `${name}: no code for "${text}"`);
    }
  });
}
