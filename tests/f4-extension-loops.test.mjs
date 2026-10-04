import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";

const module = await createCubical();
// The programs are cubist-tests/f4_extension_loops*.cubist
// (tests/cubist-tests.test.mjs states their verdicts).

test("the extension's identity type equals C2, with the specified transport and group law", async t => {
  const { program: p, result } = await checkTestModule(t, "f4_extension_loops", { module });
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of [
    "f4_automorphisms_equal_loops", "f4_extension_loops_equal_cyclic_two",
    "f4_extension_loop_equality_action", "f4_loop_zero", "f4_loop_one",
    "f4_loop_bit_roundtrip", "f4_extension_loop_roundtrip",
    "f4_loop_bit_concatenate", "f4_extension_loop_group_is_cyclic_two",
    "f4_extension_fundamental_group_is_cyclic_two",
  ]) {
    const symbol = p.symbols[`f4_galois_group__${name}`];
    assert.equal(symbol?.verified, true, name);
    assert.deepEqual(symbol.axioms, [], `${name} must remain axiom-free in the cubical kernel`);
  }
});

test("the two-loop equality cannot certify a one-element loop type", async t => {
  // Its refusal is the module's own: the archive it imports checks.
  const { result } = await checkTestModule(t, "f4_extension_loops_false", { module, options: { collectReferences: false } });
  assert.ok(result.gaps.every(gap => gap.module === "f4_extension_loops_false"), JSON.stringify(result.gaps));
});
