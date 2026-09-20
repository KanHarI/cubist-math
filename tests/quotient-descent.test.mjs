import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { replaceSyntax } from "./source-edit.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/kernel_quotient_image.proof");
const source = loaded.source + `
  theorem kernel_image_equiv_forward_computes(G : Group, H : Group, h : GroupHom(G, H)) :
    field_first((KernelQuotient(G, H, h) -> GroupImageCarrier(G, H, h)),
      (fun (f : KernelQuotient(G, H, h) -> GroupImageCarrier(G, H, h)) =>
        IsEquiv(U1, KernelQuotient(G, H, h), GroupImageCarrier(G, H, h), f)),
      kernel_quotient_image_equiv(G, H, h)) = kernel_quotient_to_image(G, H, h) {
    exact refl(kernel_quotient_to_image(G, H, h));
  }
`;
const c = compile(module, source, loaded.sources);
after(() => c.kernel.dispose());
const truncation = ["lib_Trunc", "lib_trunc_intro", "lib_trunc_elim", "lib_trunc_is_trunc"].sort();
const descent = [...truncation, "lib_funext"].sort();
const univalent = [...descent, "lib_univalence"].sort();
function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("quotient descent, computation and uniqueness require no choice or univalence", () => {
  for (const name of ["quotient_rec", "group_quotient_map"])
    check(name, ["lib_Trunc", "lib_funext", "lib_trunc_elim"]);
  for (const name of ["quotient_rec_beta", "group_quotient_map_beta", "group_quotient_map_multiply"])
    check(name, ["lib_Trunc", "lib_funext", "lib_trunc_elim", "lib_trunc_intro"]);
  for (const name of ["quotient_rec_unique", "quotient_maps_ext", "group_quotient_map_unique"])
    check(name, descent);
  check("killing_subgroup_respects_cosets", []);
  assert.ok(!c.kernel.bindings.has("LEM"));
  assert.ok(!c.kernel.bindings.has("AOC"));
});

test("kernel quotient and image have checked inverse maps with exact dependencies", () => {
  check("kernel_quotient_to_image", descent);
  check("image_to_kernel_quotient", [...truncation, "lib_univalence"].sort());
  for (const name of ["kernel_quotient_image_left", "kernel_quotient_image_right",
    "kernel_quotient_image_equiv", "kernel_quotient_image_equality", "kernel_quotient_is_set"]) check(name, univalent);
  check("kernel_image_equiv_forward_computes", descent);
});

test("quotient universal property and carrier equivalence retain certified folded types", () => {
  for (const name of ["quotient_rec_unique", "group_quotient_map_unique", "kernel_quotient_image_equiv", "kernel_quotient_image_equality"]) {
    const folded = checkedFoldedView(c, name);
    assert.deepEqual(folded.failures, {}, name);
    assert.ok(folded.verified.type, name);
  }
});

test("a nonconstant map cannot descend through the indiscrete relation", () => {
  assert.throws(() => compile(module, loaded.source + `
    theorem false_respects : RespectsRelation(Nat, (fun (x : Nat) => fun (y : Nat) => Unit),
      Nat, (fun (x : Nat) => x)) {
      intro x; intro y; intro related; exact refl(x);
    }
  `, loaded.sources), /Expected|differ/);
});

test("descent cannot omit the target's set hypothesis", () => {
  assert.throws(() => compile(module, loaded.source + `
    def false_descent(A : U1, R : A -> A -> U0, laws : EquivalenceRelation(A, R),
      B : U1, f : A -> B, respects : RespectsRelation(A, R, B, f)) =
      quotient_rec(A, R, laws, B, tt, f, respects);
  `, loaded.sources), /Expected|differ/);
});

test("the image inverse retains its complete fiber predicate", () => {
  const changed = replaceSyntax(loaded.source,
    "subgroup_value(H, group_image(G, H, h), y) = group_hom_map(G, H, h, x)", "Unit");
  assert.throws(() => compile(module, changed, loaded.sources), /Expected|differ/);
});

test("an image element does not supply a chosen source preimage", () => {
  assert.throws(() => compile(module, loaded.source + `
    def false_preimage(G : Group, H : Group, h : GroupHom(G, H), y : GroupImageCarrier(G, H, h)) :
      SubgroupImageWitness(G, H, h, subgroup_top(G), subgroup_value(H, group_image(G, H, h), y)) {
      exact subgroup_evidence(H, group_image(G, H, h), y);
    }
  `, loaded.sources), /Expected|differ/);
});
