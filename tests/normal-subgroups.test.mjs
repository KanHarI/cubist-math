import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { replaceSyntax } from "./source-edit.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/f4_normal_subgroups.proof");
const source = loaded.source + `
  theorem conjugation_hom_computes(G : Group, g : group_carrier(G), x : group_carrier(G)) :
    group_hom_map(G, G, group_iso_hom(G, G, group_conjugation_iso(G, g)), x) = group_conjugate(G, g, x) {
    exact refl(group_conjugate(G, g, x));
  }
`;
const c = compile(module, source, loaded.sources);
after(() => c.kernel.dispose());
const univalent = ["lib_funext", "lib_univalence"];
function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("group operations, conjugation, homomorphisms and kernels require no axioms", () => {
  for (const name of ["group_inverse", "group_inverse_involutive", "group_cancel_left", "group_cancel_right",
    "group_conjugation_iso", "conjugation_hom_computes", "group_hom_unit", "group_hom_inverse", "group_hom_conjugate",
    "group_hom_compose", "subgroup_top", "subgroup_bottom", "subgroup_preimage", "subgroup_preimage_normal",
    "group_kernel_normal", "group_kernel_trivial_member", "normal_members_conjugate", "normal_subgroup_transport"])
    check(name, []);
  assert.ok(!c.kernel.bindings.has("LEM"));
  assert.ok(!c.kernel.bindings.has("AOC"));
});

test("subgroup laws, contravariance and univalent equalities have their exact dependencies", () => {
  for (const name of ["group_hom_ext", "group_hom_left_identity", "group_hom_right_identity", "group_hom_associative",
    "subgroup_preimage_identity", "subgroup_preimage_composite", "subgroup_intersection", "normal_subgroup_prop", "group_kernel_identity"])
    check(name, ["lib_funext"]);
  for (const name of ["subgroup_inclusion_antisymmetric", "normal_subgroup_conjugation_invariant",
    "normal_subgroup_along_iso", "group_conjugation_path_roundtrip", "group_kernel_trivial"])
    check(name, univalent);
});

test("F4 subgroup normality is obtained by transporting the cyclic-two group property", () => {
  check("cyclic_two_abelian", []);
  for (const name of ["f4_galois_abelian", "f4_galois_subgroups_normal", "f4_identity_kernel"])
    check(name, univalent);
  assert.ok(c.kernel.steps.some(step => step.args.includes("f4_galois_group_equality")));
});

test("normality and inner-automorphism statements retain verified folded kernel types", () => {
  for (const name of ["group_kernel_normal", "normal_subgroup_along_iso", "group_conjugation_path_roundtrip", "f4_galois_subgroups_normal"]) {
    const folded = checkedFoldedView(c, name);
    assert.deepEqual(folded.failures, {}, name);
    assert.ok(folded.verified.type, name);
  }
});

test("an arbitrary subgroup cannot be asserted normal without conjugation closure", () => {
  assert.throws(() => compile(module, loaded.source + `
    theorem false_normal(G : Group, S : Subgroup(G)) : IsNormal(G, S) {
      intro g; intro x; intro member;
      exact member;
    }
  `, loaded.sources), /Expected|differ/);
});

test("a constant nonidentity map is not a group homomorphism", () => {
  assert.throws(() => compile(module, loaded.source + `
    def false_hom : GroupHom(CyclicTwo, CyclicTwo) {
      exact ((fun (x : F2Carrier) => f2_1),
        (fun (x : F2Carrier) => fun (y : F2Carrier) => refl(f2_1)));
    }
  `, loaded.sources), /Expected|differ/);
});

test("the kernel of the identity is not the whole nontrivial cyclic group", () => {
  assert.throws(() => compile(module, loaded.source + `
    theorem false_identity_kernel : subgroup_members(CyclicTwo,
      group_kernel(CyclicTwo, CyclicTwo, group_hom_identity(CyclicTwo)), f2_1) {
      exact refl(f2_1);
    }
  `, loaded.sources), /Expected|differ/);
});

test("conjugation requires the inverse factor", () => {
  const changed = replaceSyntax(loaded.sources.group_operations,
    "group_multiply(G, group_multiply(G, g, x), group_inverse(G, g))", "group_multiply(G, g, x)");
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, group_operations: changed }), /Expected|differ/);
});
