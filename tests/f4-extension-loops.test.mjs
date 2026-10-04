import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";

const module = await createCubical();
// The programs are cubist-tests/f4_extension_loops*.cubist
// (tests/cubist-tests.test.mjs states their verdicts): there, each lemma
// that the extension's identity type equals C2 is computable.

test("the two-loop equality cannot certify a one-element loop type", async t => {
  // Its refusal is the module's own: the archive it imports checks.
  const { result } = await checkTestModule(t, "f4_extension_loops_false", { module, options: { collectReferences: false } });
  assert.ok(result.gaps.every(gap => gap.module === "f4_extension_loops_false"), JSON.stringify(result.gaps));
});
