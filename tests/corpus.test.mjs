import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { benchmark } from "../web/benchmark-runner.mjs";
import { budget } from "./timing.mjs";
import { archiveReader } from "../tools/module-sources.mjs";

// G3 of the H1 specification: the archive still checks in full after H1,
// on the library's truncation and axioms since K2.5's in-place migration.
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
  // entry point basics, which no module imports, is checked too since the
  // archive has one list of modules (web/cubist/modules.mjs).
  // The count includes the library modules the archive imports: replacing
  // the archive's sets by the library's hlevels removed 6 declarations and
  // added hlevels' 40; unat's multiplication laws added 8 and removed
  // primes' 5 copies; and unat's predecessor, injectivity, cancellation and
  // two rearrangements added 5 and removed hlevels' predecessor and primes'
  // 3 copies; and unat's zero test, multiplicative cancellation and
  // trichotomy added 5 and removed hlevels' zero test; the binary
  // notation's parser added binary_naturals' 4 and the library's lexemes (9)
  // and lists (7), which it imports; hlevels' prop_over_unique (B8 of
  // the rational normalization debugging plan) added 1; lexemes'
  // power_of_ten, which only the removed unary rationals used (NUM2), 1 less;
  // and unat's order lemmas and equality decision (NT1 of the archive
  // retirement) added 8 and removed hlevels' decision and primes' 9 copies;
  // hlevels' subtype_injective added 1; and the library's Euclid (NT2)
  // removed the entry point euclid's 2 and primes' 10 of divisibility and
  // primality; the archive's truncation over the library's Trunc, importing
  // classical_axioms (K2.5's in-place migration), added h1_truncation's 6
  // and classical_axioms' 7; and least elements (NT3) added unat's 2 order
  // laws, the library's unat_least_elements (13) and polynomial_degree's
  // classical_least.
  assert.deepEqual(report.importErrors, []);
  assert.equal(report.declarations.length, 3873, "The corpus must not silently lose modules.");
  t.diagnostic(JSON.stringify(report.counts));
});
