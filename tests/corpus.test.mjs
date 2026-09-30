import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { benchmark } from "../web/benchmark-runner.mjs";
import { budget } from "./timing.mjs";

// G3 of the H1 specification: the archive, with its legacy assumptions,
// still checks in full after H1.
test("the complete canonical .cubist corpus checks with the sole native kernel", { timeout: budget(900000) }, async t => {
  // A correctness test: the limits only stop a hang, far above any
  // declaration's time and the whole run's, even under machine load. Speed is
  // measured by benchmark.html, with its <100ms target, and by the coverage
  // tool's kernel work.
  const report = await benchmark({ limitMs: budget(60000),
    readSource: name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8") });
  const failures = report.declarations.filter(d => d.category !== "checked");
  assert.deepEqual(failures, []);
  // G3 asks for the archive unchanged: every module imports, and every one
  // of its 3,804 declarations checks.
  assert.deepEqual(report.importErrors, []);
  assert.equal(report.declarations.length, 3807, "The corpus must not silently lose modules.");
  t.diagnostic(JSON.stringify(report.counts));
});
