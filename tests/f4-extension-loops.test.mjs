import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

const module = await createCubical();
const readSource = name => readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");

test("the extension's identity type equals C2, with the specified transport and group law", async t => {
  const p = new CubicalProgram(module, readSource);
  t.after(() => p.dispose());
  const result = await p.check("import f4_galois_group; theorem checked : Unit { exact tt; }", "loop_highlight");
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
  const p = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => p.dispose());
  const result = await p.check(`import f4_galois_group;
    theorem loops_are_contractible : F4ExtensionLoops =[U1] Unit {
      exact f4_extension_loops_equal_cyclic_two;
    }`, "false_loop_highlight");
  assert.equal(result.complete, false);
  assert.equal(p.symbols.false_loop_highlight__loops_are_contractible.verified, false);
  assert.ok(result.gaps.every(gap => gap.module === "false_loop_highlight"), JSON.stringify(result.gaps));
});
