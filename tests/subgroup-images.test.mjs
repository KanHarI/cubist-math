import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";
import { loadProof } from "../tools/test-selection.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/subgroup_images.proof");
const c = compile(module, loaded.source, loaded.sources);
after(() => c.kernel.dispose());
const truncation = ["lib_Trunc", "lib_trunc_elim", "lib_trunc_intro", "lib_trunc_is_trunc"].sort();
function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("image witnesses use group algebra without any axioms", () => {
  check("subgroup_image_product_witness", []);
  check("subgroup_image_inverse_witness", []);
});

test("subgroup images, adjunction and surjectivity use only propositional truncation", () => {
  for (const name of ["subgroup_image", "subgroup_image_multiply", "subgroup_image_inverse",
    "subgroup_image_least", "subgroup_image_preimage_adjunction", "subgroup_image_monotone",
    "group_image_factor", "group_image_factor_surjective"]) check(name, truncation);
  check("group_image_factor_triangle", [...truncation, "lib_funext"].sort());
  assert.ok(!c.kernel.bindings.has("LEM"));
  assert.ok(!c.kernel.bindings.has("AOC"));
});

test("identity and trivial homomorphisms have the expected image as equal subgroups", () => {
  for (const name of ["subgroup_image_identity", "group_image_trivial"])
    check(name, [...truncation, "lib_funext", "lib_univalence"].sort());
});

test("the image and its surjective factorization have certified folded types", () => {
  for (const name of ["subgroup_image_preimage_adjunction", "group_image_factor_surjective", "group_image_trivial"]) {
    const folded = checkedFoldedView(c, name);
    assert.deepEqual(folded.failures, {}, name);
    assert.ok(folded.verified.type, name);
  }
});

test("image membership does not choose a representative", () => {
  assert.throws(() => compile(module, loaded.source + `
    def false_representative(G : Group, H : Group, h : GroupHom(G, H), S : Subgroup(G),
      y : group_carrier(H), member : SubgroupImage(G, H, h, S, y)) : SubgroupImageWitness(G, H, h, S, y) {
      exact member;
    }
  `, loaded.sources), /Expected|differ/);
});

test("image introduction requires an element of the source subgroup", () => {
  assert.throws(() => compile(module, loaded.source + `
    def false_image_member(G : Group, H : Group, h : GroupHom(G, H), S : Subgroup(G),
      x : group_carrier(G)) : SubgroupImage(G, H, h, S, group_hom_map(G, H, h, x)) {
      exact subgroup_image_intro(G, H, h, S, x, tt);
    }
  `, loaded.sources), /Expected|differ/);
});
