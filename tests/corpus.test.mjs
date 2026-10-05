import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { benchmark } from "../web/benchmark-runner.mjs";
import { budget } from "./timing.mjs";
import { archiveReader } from "../tools/module-sources.mjs";

// G3 of the H1 specification: the archive, with its legacy assumptions,
// still checks in full after H1.
test("the complete canonical .cubist corpus checks with the sole native kernel", { timeout: budget(900000) }, async t => {
  // A correctness test: the limits only stop a hang, far above any
  // declaration's time and the whole run's, even under machine load. Speed is
  // measured by benchmark.html, with its <100ms target, and by the coverage
  // tool's kernel work.
  const report = await benchmark({ limitMs: budget(60000),
    readSource: archiveReader("benchmark") });
  const failures = report.declarations.filter(d => d.category !== "checked");
  assert.deepEqual(failures, []);
  // G3 asks for the archive unchanged: every module imports, and every one
  // of its declarations checks. Declaring BinaryNat, BinaryPositive, RadixNat
  // and RadixPositive by their constructors removed 21 W-encoding helpers.
  // The declared pushout module added Pushout and pushout_induction. The
  // entry points basics and euclid, which no module imports, are checked
  // too since the archive has one list of modules (web/cubist/modules.mjs).
  // The count includes the library modules the archive imports: replacing
  // the archive's sets by the library's hlevels removed 6 declarations and
  // added hlevels' 40, and nat's multiplication laws added 8 and removed
  // primes' 5 copies.
  assert.deepEqual(report.importErrors, []);
  assert.equal(report.declarations.length, 3832, "The corpus must not silently lose modules.");
  t.diagnostic(JSON.stringify(report.counts));
});
