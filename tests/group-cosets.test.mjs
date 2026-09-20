import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { replaceSyntax } from "./source-edit.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/group_cosets.proof");
const c = compile(module, loaded.source, loaded.sources);
after(() => c.kernel.dispose());
const quotientPaths = ["lib_Trunc", "lib_trunc_intro", "lib_trunc_is_trunc", "lib_funext", "lib_univalence"].sort();
function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("coset equivalence and normality's exact role are constructive and axiom-free", () => {
  for (const name of ["same_coset_equivalence", "same_coset_multiply_left", "same_coset_multiply_right",
    "normal_coset_multiply", "normal_coset_inverse", "right_coset_compatibility_implies_normal",
    "kernel_coset_of_equal_images", "kernel_coset_equal_images"]) check(name, []);
});

test("quotient equality is connected to coset membership with explicit dependencies", () => {
  check("same_coset_path", quotientPaths);
  check("normal_coset_product_path", quotientPaths);
  check("coset_path_membership", ["lib_Trunc", "lib_trunc_intro"]);
  assert.ok(!c.kernel.bindings.has("LEM"));
  assert.ok(!c.kernel.bindings.has("AOC"));
});

test("coset compatibility and kernel-fiber results retain verified folded types", () => {
  for (const name of ["normal_coset_product_path", "kernel_coset_equal_images", "right_coset_compatibility_implies_normal"]) {
    const folded = checkedFoldedView(c, name);
    assert.deepEqual(folded.failures, {}, name);
    assert.ok(folded.verified.type, name);
  }
});

test("right multiplication cannot use unchanged subgroup evidence in place of normality", () => {
  const changed = replaceSyntax(loaded.source, "normal(group_inverse(G, a), n, same)", "same");
  assert.throws(() => compile(module, changed, loaded.sources), /Expected|differ/);
});

test("a quotient class is not a chosen representative", () => {
  assert.throws(() => compile(module, loaded.source + `
    def false_coset_representative(G : Group, S : Subgroup(G), q : LeftCosets(G, S)) : group_carrier(G) {
      exact q;
    }
  `, loaded.sources), /Expected|differ/);
});

test("predicate quotients cannot silently be lowered to U0", () => {
  assert.throws(() => compile(module, loaded.source + `
    def false_small_cosets(G : Group, S : Subgroup(G)) : U0 { exact LeftCosets(G, S); }
  `, loaded.sources), /Expected|differ|universe/i);
});
