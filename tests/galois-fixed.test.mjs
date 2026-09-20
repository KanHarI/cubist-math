import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";
import { replaceSyntax } from "./source-edit.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/f4_galois_connection.proof");
const c = compile(module, loaded.source, loaded.sources);
after(() => c.kernel.dispose());
const constructive = ["lib_funext", "lib_univalence"];

function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("the fixed-point connection is logical and subobject laws use only their stated constructive axioms", () => {
  for (const name of ["galois_connection", "galois_fixed_antitone", "galois_fixing_antitone",
    "galois_fixed_fixing_contains", "galois_fixing_fixed_contains",
    "galois_fixed_closure_idempotent", "galois_fixing_closure_idempotent",
    "galois_fixed_inverse", "subfield_zero", "subgroup_inverse"])
    check(name, []);
  for (const name of ["galois_fixed_field", "subfield_laws_prop", "subgroup_laws_prop", "intermediate_ext"])
    check(name, ["lib_funext"]);
  for (const name of ["galois_fixing_subgroup", "subfield_ext", "galois_fixed_is_loop_invariant", "galois_loop_invariant_is_fixed"])
    check(name, constructive);
  assert.ok(!c.kernel.bindings.has("AOC"));
  assert.ok(!c.kernel.bindings.has("LEM"));
  for (const name of ["subfields", "subgroups", "intermediate_fields", "galois_fixed_points", "galois_fixed_fields", "galois_fixing_subgroups"])
    assert.doesNotMatch(loaded.sources[name], /\baxiom\s|\bpostulate\s*\(/, name);
});

test("F4 fixed elements have actual F2 preimages; subobject recovery uses explicit decisions", () => {
  for (const name of ["f4_frobenius_fixed_in_base", "f4_fixed_in_base", "f4_base_is_fixed", "f4_fixed_field_is_base",
    "f4_intermediate_with_alpha", "f4_intermediate_without_alpha"])
    check(name, []);
  for (const name of ["f4_fixed_predicate_is_base", "f4_fixed_intermediate_is_base", "f4_intermediate_classification",
    "f4_fixing_fixed_subgroup", "f4_fixed_fixing_intermediate"])
    check(name, constructive);
  for (const name of ["f4_intermediate_classification", "f4_fixed_fixing_intermediate"])
    assert.match([...c.outputs, ...c.imports].find(o => o.name === name).type, /Decidable\(/);
  assert.match(c.outputs.find(o => o.name === "f4_fixing_fixed_subgroup").type, /Decidable\(/);
});

test("small-indexed intersections are subfields and satisfy the universal property", async () => {
  const loaded = await loadProof("web/proofs/subfield_intersections.proof");
  const compiled = compile(module, loaded.source, loaded.sources);
  try {
    for (const name of ["subfield_intersection_laws", "subfield_intersection_lower", "subfield_intersection_greatest", "subfield_inclusion_antisymmetric"])
      assert.ok(compiled.kernel.verify(name + "_type", name), name);
    assert.deepEqual(compiled.kernel.axiomsFor("subfield_intersection_laws"), ["lib_funext"]);
    for (const name of ["subfield_intersection_lower", "subfield_intersection_greatest"])
      assert.deepEqual(compiled.kernel.axiomsFor(name), [], name);
  } finally { compiled.kernel.dispose(); }
});

test("the kernel rejects the false claim that every automorphism fixes alpha", () => {
  assert.throws(() => compile(module, loaded.source + `
    theorem false_fixed : F4Fixed(f4_2) {
      intro e; intro member; exact refl(f4_2);
    }
  `, loaded.sources), /Expected|differ/);
});

test("the kernel rejects identifying the base field with the whole F4", () => {
  assert.throws(() => compile(module, loaded.source + `
    theorem false_base : F2Image(f4_2) { exact (f2_0, refl(f4_0)); }
  `, loaded.sources), /Expected|differ/);
});

test("fixed inverse closure cannot skip the uniqueness argument", () => {
  const original = loaded.sources.galois_fixed_fields;
  const changed = replaceSyntax(original,
    "algebraic_inverse_unique(A, ops, af_set(F), field_ring_data(A, ops, af_laws(F)), x, f(y), y, imageInverse, inverseLaw)",
    "refl(y)");
  assert.notEqual(changed, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, galois_fixed_fields: changed }), /Expected|differ/);
});

test("the order interface derives variance and idempotence for the actual Galois assignments", async () => {
  const loaded = await loadProof("web/proofs/galois_orders.proof");
  const compiled = compile(module, loaded.source, loaded.sources);
  try {
    for (const name of ["antitone_compose", "antitone_connection_extensive", "antitone_connection_reverses", "antitone_connection_closure_idempotent"])
      assert.deepEqual(compiled.kernel.axiomsFor(name), [], name);
    for (const name of ["galois_order_connection", "fixed_field_reverses_inclusion", "fixing_group_reverses_inclusion", "intermediate_galois_closure_monotone", "galois_subgroup_partial_order", "intermediate_partial_order", "intermediate_galois_closure_idempotent"]) {
      assert.ok(compiled.kernel.verify(name + "_type", name), name);
      assert.deepEqual(compiled.kernel.axiomsFor(name).sort(), constructive, name);
    }
  } finally { compiled.kernel.dispose(); }
  assert.throws(() => compile(module, loaded.source + `
    theorem wrong_variance(K : AlgebraicField, E : FieldExt(K)) :
      Monotone(GaloisSubgroup(K, E), IntermediateField(K, E),
        GaloisSubgroupIncluded(K, E), IntermediateIncluded(K, E), fixed_intermediate_field(K, E)) {
      exact fixed_field_reverses_inclusion(K, E);
    }
  `, loaded.sources), /Expected|differ/);
});
