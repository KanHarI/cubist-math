import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { replaceSyntax } from "./source-edit.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/f4_embedding_images.proof");
const c = compile(module, loaded.source, loaded.sources);
after(() => c.kernel.dispose());
const univalent = ["lib_funext", "lib_univalence"];
const generated = ["lib_Trunc", "lib_funext", "lib_trunc_elim", "lib_trunc_intro", "lib_trunc_is_trunc", "lib_univalence"];
function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("realized subfields, embeddings, images and inverse images are constructive without axioms", () => {
  for (const name of ["subtype_is_set", "subfield_carrier_field_laws", "subfield_as_field", "subfield_inclusion",
    "field_embedding_compose", "intermediate_base_embedding", "field_nonzero_of_inverse",
    "subfield_image_laws", "subfield_preimage_laws", "subfield_image_preimage_adjunction", "field_embedding_image_iso"])
    check(name, []);
  for (const name of ["field_embedding_ext", "field_embedding_left_identity", "field_embedding_right_identity",
    "field_embedding_associative", "intermediate_tower", "field_embedding_factor_unique"])
    check(name, ["lib_funext"]);
  assert.ok(!c.kernel.bindings.has("LEM"));
  assert.ok(!c.kernel.bindings.has("AOC"));
});

test("ambient embeddings preserve composita and field equality identifies only the image", () => {
  for (const name of ["field_embedding_image_equality", "subfield_preimage_identity", "subfield_preimage_composite", "subfield_preimage_image"])
    check(name, univalent);
  for (const name of ["compositum_image", "f2_embedding_image_is_base", "f4_base_field_is_f2", "f2_compositum_in_f4"])
    check(name, generated);
  check("f4_base_tower", univalent);
});

test("a tower cannot omit compatibility with the specified direct embedding", () => {
  assert.throws(() => compile(module, loaded.source + `
    theorem wrong_tower(K : AlgebraicField, L : AlgebraicField, e : FieldEmbedding(K, L), d : FieldEmbedding(K, L)) :
      FieldTower(K, K, L, field_embedding_identity(K), e, d) {
      exact field_embedding_left_identity(K, L, e);
    }
  `, loaded.sources), /Expected|differ/);
});

test("an embedding into F4 does not give equality with all of F4", () => {
  assert.throws(() => compile(module, loaded.source + `
    theorem false_field_equality : F2 =[AlgebraicField] F4 {
      exact field_embedding_image_equality(F2, F4, f2_f4_embedding);
    }
  `, loaded.sources), /Expected|differ/);
});

test("the image isomorphism must return its actual preimage, not a constant", () => {
  const original = loaded.sources.field_embedding_image;
  const changed = replaceSyntax(original, "sigma_first(af_carrier(K), fiber, subfield_evidence(L, S, y))", "af_zero(af_carrier(K), af_operations(K))");
  assert.notEqual(changed, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, field_embedding_image: changed }), /Expected|differ/);
});
