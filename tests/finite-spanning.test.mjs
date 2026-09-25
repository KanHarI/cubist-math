import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
const module = await createCubical();
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const create = t => { const p = new CubicalProgram(module, readSource, { collectReferences: false }); t.after(() => p.dispose()); return p; };
const assumptions = (p, name) => { const s = p.symbols[name]; assert.equal(s?.verified, true, name); return s.axioms.map(id => p.checker.assumptionLabels.get(id)); };

test("finite spanning families contain an indexed subfamily basis without choice", async t => {
  const p = create(t);
  const result = await p.check(`import spanning_subfamilies;
    def extract(K : AlgebraicField, V : VectorSpace(K), n : Nat, v : Fin(n) -> vector_carrier(K, V), spans : FiniteSpanningFamily(K, V, n, v)) : Mere(SubfamilyBasis(K, V, n, v)) {
      exact finite_spanning_subfamily_basis(K, V, n, v, spans);
    }
    def generator_coordinates(K : AlgebraicField, V : VectorSpace(K), n : Nat, v : Fin(n) -> vector_carrier(K, V), basis : FamilyBasis(K, V, n, v)) : FiniteBasis(K, V, n) {
      exact family_basis_coordinates(K, V, n, v, basis);
    }
  `, "spanning_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["finite_linear_lifts__finite_linear_lift", "spanning_subfamilies__finite_spanning_subfamily_basis", "finite_spanning__finite_spanning_basis"])
    assert.ok(assumptions(p, name).every(a => /^(LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U0\))$/.test(a)), name);
});

test("arbitrary finite subspaces have bases and finiteness descends both ways in a tower", async t => {
  const p = create(t);
  const result = await p.check(`import subspace_carriers;
    import finite_towers;
    def subspace_basis(K : AlgebraicField, V : VectorSpace(K), finite : FiniteDimensional(K, V), S : Subspace(K, V)) : Mere(exists n : Nat, FiniteBasis(K, SubspaceVectorSpace(K, V, S), n)) {
      exact finite_subspace_basis(K, V, finite, S);
    }
    def tower_converse(K : AlgebraicField, L : AlgebraicField, M : AlgebraicField,
      e : FieldEmbedding(K, L), d : FieldEmbedding(L, M), c : FieldEmbedding(K, M), triangle : FieldTower(K, L, M, e, d, c), finite : FiniteExtension(K, embedding_as_extension(K, M, c))) :
      FiniteExtension(K, embedding_as_extension(K, L, e)) and FiniteExtension(L, embedding_as_extension(L, M, d)) {
      exact finite_extension_tower_converse(K, L, M, e, d, c, triangle, finite);
    }
  `, "finite_tower_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["subspace_carriers__finite_subspace_basis", "finite_towers__finite_extension_tower_iff"])
    assert.ok(assumptions(p, name).every(a => /^(LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U0\))$/.test(a)), name);
  assert.deepEqual(assumptions(p, "subspace_carriers__SubspaceVectorSpace"), []);
});

test("finite extraction does not choose a basis or equate finiteness with independence", async t => {
  const p = create(t);
  const result = await p.check(`import spanning_subfamilies;
    def cannot_choose(K : AlgebraicField, V : VectorSpace(K), n : Nat, v : Fin(n) -> vector_carrier(K, V), spans : FiniteSpanningFamily(K, V, n, v)) : SubfamilyBasis(K, V, n, v) {
      exact finite_spanning_subfamily_basis(K, V, n, v, spans);
    }
    def cannot_keep_duplicates(K : AlgebraicField, V : VectorSpace(K), n : Nat, v : Fin(n) -> vector_carrier(K, V), spans : FiniteSpanningFamily(K, V, n, v)) : FamilyBasis(K, V, n, v) {
      exact (family_linear_surjective(K, V, n, v, spans), family_linear_surjective(K, V, n, v, spans));
    }
  `, "invalid_spanning");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(s => !s.verified));
  assert.ok(result.gaps.every(g => g.module === "invalid_spanning"), JSON.stringify(result.gaps));
});
