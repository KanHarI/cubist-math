import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
const module = await createCubical();
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const create = t => { const p = new CubicalProgram(module, readSource, { collectReferences: false }); t.after(() => p.dispose()); return p; };
const allowed = /^(LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U0\))$/;
const checkedWithoutNewAxioms = (p, name) => {
  const s = p.symbols[name];
  assert.equal(s?.verified, true, name);
  const axioms = s.axioms.map(id => p.checker.assumptionLabels.get(id));
  assert.ok(axioms.every(a => allowed.test(a)), `${name}: ${axioms}`);
};

test("formal division, uniqueness, root bounds and Bezout are checked without extra axioms", async t => {
  const p = create(t);
  const result = await p.check(`import polynomial_root_bound;
    import polynomial_irreducible;
    def division(K : AlgebraicField, p : Polynomial(K), q : Polynomial(K), nz : PolynomialNonzero(K, q)) : PolynomialDivision(K, p, q) {
      exact polynomial_division(K, p, q, nz);
    }
  `, "polynomial_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["polynomial_division__polynomial_division", "polynomial_division_unique__polynomial_division_unique", "polynomial_root_bound__polynomial_root_bound", "polynomial_bezout__polynomial_bezout"])
    checkedWithoutNewAxioms(p, name);
});

test("adjoined roots and embeddings into a root field are constructed, not assumed", async t => {
  const p = create(t);
  const result = await p.check(`import polynomial_root_embeddings;
    import polynomial_annihilator;
    def root(K : AlgebraicField, M : PolynomialModulus(K), irr : PolynomialIrreducible(K, modulus_polynomial(K, M))) :
      PolynomialRoot(K, PolynomialResidueField(K, M, irr), residue_embedding(K, M, irr), modulus_polynomial(K, M), adjoined_root(K, M)) {
      exact adjoined_root_is_root(K, M, irr);
    }
  `, "adjoined_root_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["polynomial_residue_field__PolynomialResidueField", "polynomial_adjoin__adjoined_root_is_root", "polynomial_root_embeddings__adjoin_root_embedding", "polynomial_annihilator__annihilator_generator_irreducible"])
    checkedWithoutNewAxioms(p, name);
});

test("zero polynomial is excluded from root bounds and division by zero", async t => {
  const p = create(t);
  const result = await p.check(`import polynomial_root_bound;
    def zero_has_no_roots(K : AlgebraicField) : RootFamily(K, polynomial_zero(K), 1) -> Void {
      exact polynomial_root_bound(K, polynomial_zero(K), polynomial_one_not_zero(K));
    }
    def divide_by_zero(K : AlgebraicField, p : Polynomial(K)) : PolynomialDivision(K, p, polynomial_zero(K)) {
      exact polynomial_division(K, p, polynomial_zero(K), polynomial_one_not_zero(K));
    }
  `, "invalid_polynomial_claims");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(s => !s.verified));
  assert.ok(result.gaps.every(g => g.module === "invalid_polynomial_claims"), JSON.stringify(result.gaps));
});
