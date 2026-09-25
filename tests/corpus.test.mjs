import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { benchmark } from "../web/benchmark-runner.mjs";

test("the complete canonical .cubist corpus checks with the sole native kernel", { timeout: 180000 }, async t => {
  // A generous regression deadline avoids confusing machine load with failure.
  // Use benchmark.html for the independent <100ms optimization target.
  const report = await benchmark({ limitMs: 10000,
    readSource: name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8") });
  const failures = report.declarations.filter(d => !["checked", "template"].includes(d.category));
  assert.deepEqual(failures, []);
  assert.ok(report.declarations.length >= 2500, "The corpus must not silently lose modules.");
  t.diagnostic(JSON.stringify(report.counts));
});
