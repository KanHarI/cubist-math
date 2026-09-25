import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
const module = await createCubical();
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const create = t => {
  const program = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => program.dispose()); return program;
};

test("S3 has six elements and a genuinely non-normal point stabilizer, without axioms", async t => {
  const program = create(t);
  const result = await program.check("import non_normal_subgroup; def verified_example : IsNormal(S3, S3PointStabilizer) -> Void { exact s3_point_stabilizer_not_normal; }", "s3_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["s3_has_six_elements", "s3_point_stabilizer_not_normal", "conjugate_swap12_moves_point0"]) {
    const symbol = program.symbols[`non_normal_subgroup__${name}`];
    assert.equal(symbol.verified, true, name);
    assert.deepEqual(symbol.axioms, [], name);
  }
});

test("finite bases give unique coordinates and cubical carrier transport without choice", async t => {
  const program = create(t);
  const result = await program.check(`import linear_span;
    import finite_fields;
    def f2_basis : FiniteBasis(F2, ScalarSpace(F2), 1) { exact scalar_space_basis(F2); }
    def f4_basis_over_itself : FiniteBasis(F4, ScalarSpace(F4), 1) { exact scalar_space_basis(F4); }
    def coordinate_plane_basis(K : AlgebraicField) : FiniteBasis(K, CoordinateSpace(K, 2), 2) {
      exact standard_basis(K, 2);
    }
    def scalar_transport_computes(K : AlgebraicField, x : af_carrier(K)) :
      transport((fun (A : U0) => A), (Fin(1) -> af_carrier(K)), af_carrier(K),
        ua(U0, (Fin(1) -> af_carrier(K)), af_carrier(K),
          linear_iso_equiv(K, CoordinateSpace(K, 1), ScalarSpace(K), scalar_space_basis(K))),
        (fun (i : Fin(1)) => x)) = x {
      exact UnivalenceBeta(U0, (Fin(1) -> af_carrier(K)), af_carrier(K),
        linear_iso_equiv(K, CoordinateSpace(K, 1), ScalarSpace(K), scalar_space_basis(K)),
        (fun (i : Fin(1)) => x));
    }
  `, "basis_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const symbol of result.outputs) {
    assert.equal(symbol.verified, true, symbol.name);
    assert.deepEqual(symbol.axioms, [], symbol.name);
  }
  for (const name of ["basis_coordinates_unique", "basis_carrier_path", "scalar_space_basis"]) {
    const symbol = program.symbols[`finite_bases__${name}`];
    assert.equal(symbol.verified, true, name); assert.deepEqual(symbol.axioms, [], name);
  }
});

test("nonlinear constant maps and a silently changed basis length are rejected", async t => {
  const program = create(t);
  const result = await program.check(`import finite_bases;
    import finite_fields;
    def constant_one_is_not_linear : LinearMap(F2, ScalarSpace(F2), ScalarSpace(F2)) {
      exact ((fun (x : F2Carrier) => f2_1),
        (fun (x : F2Carrier) => fun (y : F2Carrier) => refl(f2_1)),
        (fun (a : F2Carrier) => fun (x : F2Carrier) => refl(f2_1)));
    }
    def wrong_basis(K : AlgebraicField) : FiniteBasis(K, CoordinateSpace(K, 0), 1) {
      exact standard_basis(K, 1);
    }
  `, "invalid_linear");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(symbol => !symbol.verified));
  assert.ok(result.gaps.every(gap => gap.module === "invalid_linear"), JSON.stringify(result.gaps));
});

test("spans are least subspaces and independent chains have bounds, including empty and U1-indexed chains", async t => {
  const program = create(t);
  const result = await program.check(`import span_subspace;
    import independent_order;
    def empty_family(K : AlgebraicField, V : VectorSpace(K), i : Void) : IndependentSubset(K, V) { exact absurd(i); }
    def empty_chain(K : AlgebraicField, V : VectorSpace(K)) :
      PredicateChain(Void, vector_carrier(K, V), (fun (i : Void) => independent_members(K, V, empty_family(K, V, i)))) {
      intro i; exact absurd(i);
    }
    def empty_union_bound(K : AlgebraicField, V : VectorSpace(K)) :
      IndependentIncluded(K, V, IndependentUnion(K, V, Void, empty_family(K, V), empty_chain(K, V)), EmptyIndependentSubset(K, V)) {
      exact independent_union_least(K, V, Void, empty_family(K, V), empty_chain(K, V), EmptyIndependentSubset(K, V),
        (fun (i : Void) => typed(IndependentIncluded(K, V, empty_family(K, V, i), EmptyIndependentSubset(K, V)), absurd(i))));
    }
    def large_constant_family(K : AlgebraicField, V : VectorSpace(K), A : U0) = EmptyIndependentSubset(K, V);
    def large_constant_chain(K : AlgebraicField, V : VectorSpace(K)) :
      PredicateChain(U0, vector_carrier(K, V), (fun (A : U0) => independent_members(K, V, large_constant_family(K, V, A)))) {
      intro A; intro B;
      exact field_exists_intro(
        IndependentIncluded(K, V, EmptyIndependentSubset(K, V), EmptyIndependentSubset(K, V)) or
        IndependentIncluded(K, V, EmptyIndependentSubset(K, V), EmptyIndependentSubset(K, V)),
        left(independent_inclusion_refl(K, V, EmptyIndependentSubset(K, V))));
    }
    def large_union(K : AlgebraicField, V : VectorSpace(K)) =
      IndependentUnion(K, V, U0, large_constant_family(K, V), large_constant_chain(K, V));
  `, "chain_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  const checked = [
    ["finite_combinations", "linear_combination_append"], ["finite_combinations", "linear_combination_scale"],
    ["vector_subspaces", "span_least"], ["span_subspace", "SpanSubspace"], ["span_subspace", "span_idempotent_path"],
    ["independent_unions", "chain_union_independent"], ["independent_order", "independent_partial_order"],
    ["independent_order", "independent_union_least"],
  ];
  for (const [file, name] of checked) {
    const symbol = program.symbols[file + "__" + name];
    assert.equal(symbol.verified, true, name);
    const assumptions = symbol.axioms.map(binding => program.checker.assumptionLabels.get(binding));
    assert.ok(assumptions.every(name => /^Truncate/.test(name)), JSON.stringify(assumptions));
  }
  assert.deepEqual(program.symbols.independent_order__independent_partial_order.axioms, []);
});

test("the general basis theorem derives maximality from choice, with its exact assumptions visible", async t => {
  const program = create(t);
  const result = await program.check(`import vector_basis_existence;
    import finite_fields;
    def any_vector_space(K : AlgebraicField, V : VectorSpace(K)) : FieldExists(VectorBasis(K, V)) {
      exact vector_space_has_basis(K, V);
    }
    def empty_coordinate_space(K : AlgebraicField) : FieldExists(VectorBasis(K, CoordinateSpace(K, 0))) {
      exact vector_space_has_basis(K, CoordinateSpace(K, 0));
    }
    def binary_field_basis : FieldExists(VectorBasis(F2, ScalarSpace(F2))) {
      exact vector_space_has_basis(F2, ScalarSpace(F2));
    }
  `, "general_basis_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const assumptions = name => {
    const symbol = program.symbols[name];
    assert.equal(symbol?.verified, true, name);
    return symbol.axioms.map(binding => program.checker.assumptionLabels.get(binding)).sort();
  };
  for (const name of ["vector_arithmetic__vector_scale_injective", "finite_omission__fin_omit_cover",
    "finite_omission__linear_combination_omit", "chain_complete_orders__partial_order_is_set"])
    assert.deepEqual(assumptions(name), [], name);
  assert.ok(assumptions("bourbaki_witt__bourbaki_witt").every(name => /^(Truncate|LEM)/.test(name)));
  assert.ok(assumptions("independent_extension__adjoin_independent").every(name => /^(Truncate|LEM)/.test(name)));
  const basisAxioms = assumptions("vector_basis_existence__vector_space_has_basis");
  assert.ok(basisAxioms.includes("Choice(U1)"), JSON.stringify(basisAxioms));
  assert.ok(basisAxioms.includes("LEM(U0)"), JSON.stringify(basisAxioms));
  assert.ok(basisAxioms.every(name => /^(Choice\(U1\)|LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U[01]\))$/.test(name)), JSON.stringify(basisAxioms));
  assert.deepEqual(assumptions("general_basis_regression__any_vector_space"), basisAxioms);
});

test("basis existence cannot silently select a basis or justify adjoining the zero vector", async t => {
  const program = create(t);
  const result = await program.check(`import vector_basis_existence;
    def cannot_untruncate(K : AlgebraicField, V : VectorSpace(K)) : VectorBasis(K, V) {
      exact vector_space_has_basis(K, V);
    }
    def zero_is_not_outside(K : AlgebraicField, V : VectorSpace(K)) :
      Span(K, V, (fun (x : vector_carrier(K, V)) => Void), vector_zero(K, V)) -> Void {
      intro member; exact member;
    }
  `, "invalid_basis_selection");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(symbol => !symbol.verified));
  assert.ok(result.gaps.every(gap => gap.module === "invalid_basis_selection"), JSON.stringify(result.gaps));
});
