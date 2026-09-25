import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

const module = await createCubical();
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const create = t => {
  const program = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => program.dispose());
  return program;
};
const checked = (program, name) => {
  const symbol = program.symbols[name];
  assert.equal(symbol?.verified, true, name);
  return symbol;
};
const axioms = (program, name) => checked(program, name).axioms.map(binding => program.checker.assumptionLabels.get(binding)).sort();

test("finite dimensions include zero, are unique for arbitrary bases, and need no choice", async t => {
  const program = create(t);
  const result = await program.check(`import dimension;
    def empty_dimension(K : AlgebraicField) :
      dimension(K, CoordinateSpace(K, 0), finite_dimensional_basis(K, CoordinateSpace(K, 0), 0, standard_basis(K, 0))) = 0 {
      exact refl(0);
    }
    def plane_dimension(K : AlgebraicField, n : Nat, basis : FiniteBasis(K, CoordinateSpace(K, 2), n)) : n = 2 {
      exact finite_dimension_invariance(K, CoordinateSpace(K, 2), n, 2, basis, standard_basis(K, 2));
    }
    def scalar_dimension(K : AlgebraicField, n : Nat, basis : FiniteBasis(K, ScalarSpace(K), n)) : n = 1 {
      exact finite_dimension_invariance(K, ScalarSpace(K), n, 1, basis, scalar_space_basis(K));
    }
    def mere_coordinates_suffice(K : AlgebraicField, V : VectorSpace(K), finite : Mere(exists n : Nat. FiniteBasis(K, V, n))) : FiniteDimensional(K, V) {
      exact finite_dimensional_from_mere(K, V, finite);
    }
    def swap_coordinates(K : AlgebraicField, n : Nat, i : Fin(succ(n)), finite : FiniteDimensional(K, CoordinateSpace(K, succ(n)))) :
      dimension(K, CoordinateSpace(K, succ(n)), finite) = succ(n) {
      exact dimension_of_basis(K, CoordinateSpace(K, succ(n)), finite, succ(n), coordinate_swap_iso(K, n, i));
    }
  `, "dimension_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const name of ["coordinate_elimination__pivot_reduced_injective", "linear_constructions__linear_kernel_injective"])
    assert.deepEqual(axioms(program, name), [], name);
  const assumptions = axioms(program, "finite_dimension__finite_dimension_invariance");
  assert.ok(assumptions.includes("LEM(U0)"), JSON.stringify(assumptions));
  assert.ok(assumptions.every(name => /^(LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U0\))$/.test(name)), JSON.stringify(assumptions));
  for (const name of ["dimension__finite_dimensional_prop", "dimension__dimension_unique", "dimension__dimension_linear_iso", "dimension__dimension_path"])
    assert.ok(axioms(program, name).every(name => /^(LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U0\))$/.test(name)), name);
});

test("extension degree is positive, has identity degree one, and respects univalent extension equality", async t => {
  const program = create(t);
  const result = await program.check(`import extension_degree;
    import finite_fields;
    def degree_of_identity : extension_degree(F2, embedding_as_extension(F2, F2, field_embedding_identity(F2)), identity_extension_finite(F2)) = 1 {
      exact refl(1);
    }
    def no_zero_degree(K : AlgebraicField, E : FieldExt(K), degree : ExtensionDegree(K, E, 0)) : Void {
      exact extension_dimension_not_zero(K, E, degree);
    }
    def equivalent_extensions(K : AlgebraicField, E : FieldExt(K), F : FieldExt(K), iso : ExtensionIso(K, E, F), finiteE : FiniteExtension(K, E), finiteF : FiniteExtension(K, F)) :
      extension_degree(K, E, finiteE) = extension_degree(K, F, finiteF) {
      exact extension_degree_iso(K, E, F, iso, finiteE, finiteF);
    }
  `, "degree_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const name of ["extension_degree__extension_degree_unique", "extension_degree__extension_degree_iso", "extension_degree__extension_dimension_not_zero"])
    assert.ok(axioms(program, name).every(name => /^(LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U0\))$/.test(name)), name);
});

test("the product basis and numerical tower law check for arbitrary fields and a commuting triangle", async t => {
  const program = create(t);
  const result = await program.check(`import extension_degree;
    def arbitrary_tower(K : AlgebraicField, L : AlgebraicField, M : AlgebraicField,
      e : FieldEmbedding(K, L), d : FieldEmbedding(L, M), c : FieldEmbedding(K, M), triangle : FieldTower(K, L, M, e, d, c),
      lower : FiniteExtension(K, embedding_as_extension(K, L, e)), upper : FiniteExtension(L, embedding_as_extension(L, M, d)),
      whole : FiniteExtension(K, embedding_as_extension(K, M, c))) :
      extension_degree(K, embedding_as_extension(K, M, c), whole) = multiply_count(extension_degree(L, embedding_as_extension(L, M, d), upper), extension_degree(K, embedding_as_extension(K, L, e), lower)) {
      exact tower_law(K, L, M, e, d, c, triangle, lower, upper, whole);
    }
    def identity_triangle(K : AlgebraicField) : FieldTower(K, K, K, field_embedding_identity(K), field_embedding_identity(K), field_embedding_identity(K)) {
      exact field_embedding_left_identity(K, K, field_embedding_identity(K));
    }
    def identity_tower(K : AlgebraicField) :
      ExtensionDegree(K, embedding_as_extension(K, K, field_embedding_identity(K)), 1) {
      exact extension_degree_tower(K, K, K, field_embedding_identity(K), field_embedding_identity(K), field_embedding_identity(K), identity_triangle(K), 1, 1,
        identity_extension_degree(K), identity_extension_degree(K));
    }
  `, "tower_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const name of ["scalar_restriction__field_tower_basis", "extension_degree__field_tower_basis_triangle"])
    assert.deepEqual(axioms(program, name), [], name);
  assert.ok(axioms(program, "extension_degree__extension_degree_tower").every(name => /^Truncate(?:Intro|Prop|Elim)?\(U0\)$/.test(name)));
  assert.ok(axioms(program, "extension_degree__tower_law").every(name => /^(LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U0\))$/.test(name)));
  checked(program, "extension_degree__finite_extension_tower");
});

test("dimension does not choose a basis, forget linearity, or ignore a tower's embedding", async t => {
  const program = create(t);
  const result = await program.check(`import extension_degree;
    def choose_basis(K : AlgebraicField, V : VectorSpace(K), n : Nat, size : HasDimension(K, V, n)) : FiniteBasis(K, V, n) { exact size; }
    def wrong_scalar_degree(K : AlgebraicField) : ExtensionDegree(K, embedding_as_extension(K, K, field_embedding_identity(K)), 2) { exact identity_extension_degree(K); }
    def arbitrary_bijection_is_linear(K : AlgebraicField, m : Nat, n : Nat, b : Bijection((Fin(m) -> af_carrier(K)), (Fin(n) -> af_carrier(K)))) : m = n {
      exact coordinate_dimension_invariant(K, m, n, b);
    }
    def unrelated_embedding(K : AlgebraicField, L : AlgebraicField, M : AlgebraicField,
      e : FieldEmbedding(K, L), d : FieldEmbedding(L, M), c : FieldEmbedding(K, M),
      lower : FiniteExtension(K, embedding_as_extension(K, L, e)), upper : FiniteExtension(L, embedding_as_extension(L, M, d))) :
      FiniteExtension(K, embedding_as_extension(K, M, c)) {
      exact finite_extension_tower(K, L, M, e, d, field_embedding_compose(K, L, M, e, d), refl(field_embedding_compose(K, L, M, e, d)), lower, upper);
    }
  `, "invalid_dimension");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 4);
  assert.ok(result.outputs.every(symbol => !symbol.verified));
  assert.ok(result.gaps.every(gap => gap.module === "invalid_dimension"), JSON.stringify(result.gaps));
});
