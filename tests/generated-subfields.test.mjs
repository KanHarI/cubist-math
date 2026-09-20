import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { replaceSyntax } from "./source-edit.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/f4_generated_subfields.proof");
const c = compile(module, loaded.source, loaded.sources);
after(() => c.kernel.dispose());
const truncation = ["lib_Trunc", "lib_trunc_elim", "lib_trunc_intro", "lib_trunc_is_trunc"].sort();
const extensional = [...truncation, "lib_funext", "lib_univalence"].sort();
function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("finite field-generation derivations stay small and require no axioms", () => {
  for (const name of ["field_closure_step_into_subfield", "field_closure_stage_least", "field_closure_pad_right",
    "field_derivation_add", "field_derivation_mul", "field_derivation_inverse", "f4_add_derivation_rank"])
    check(name, []);
  const small = compile(module, loaded.source + `
    def derivations_are_small(F : AlgebraicField, P : af_carrier(F) -> U0, x : af_carrier(F)) : U0 {
      exact FieldDerivation(F, P, x);
    }
    def generated_membership_is_small(F : AlgebraicField, P : af_carrier(F) -> U0, x : af_carrier(F)) : U0 {
      exact GeneratedField(F, P, x);
    }
  `, loaded.sources);
  small.kernel.dispose();
});

test("generated subfields have checked closure and leastness with only the existing truncation axioms", () => {
  check("generated_field_laws", truncation);
  check("generated_subfield", truncation);
  for (const name of ["generated_field_least", "generated_subfield_least", "compositum_least"])
    check(name, ["lib_Trunc", "lib_trunc_elim"]);
  for (const name of ["compositum_commutative", "compositum_associative", "compositum_idempotent", "generated_subfield_of_subfield"])
    check(name, extensional);
  assert.ok(!c.kernel.bindings.has("LEM"));
  assert.ok(!c.kernel.bindings.has("AOC"));
});

test("composita respect field isomorphisms by path induction and F4 generation has both positive and negative examples", () => {
  check("compositum_transport", truncation);
  for (const name of ["compositum_along_iso", "f4_alpha_generates_field", "f4_prime_subfield_is_base", "f4_alpha_not_in_prime"])
    check(name, extensional);
});

test("the kernel rejects alpha as a member of the prime subfield", () => {
  assert.throws(() => compile(module, loaded.source + `
    theorem false_prime_member : GeneratedField(F4, (fun (x : F4Carrier) => Void), f4_2) {
      exact generated_field_zero(F4, (fun (x : F4Carrier) => Void));
    }
  `, loaded.sources), /Expected|differ/);
});

test("padding must account for both derivation ranks", () => {
  const original = loaded.sources.generated_subfields;
  const changed = replaceSyntax(original, "succ(n + m)", "succ(n)");
  assert.notEqual(changed, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, generated_subfields: changed }), /Expected|differ/);
});

test("leastness cannot replace a generated inverse by its original element", () => {
  const original = loaded.sources.subfield_generation_steps;
  const changed = replaceSyntax(original,
    "subfield_inverse(F, Q, laws, y, x, included(y, py), inverseLaw)", "included(y, py)");
  assert.notEqual(changed, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, subfield_generation_steps: changed }), /Expected|differ/);
});
