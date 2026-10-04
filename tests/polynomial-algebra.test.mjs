import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";
const module = await createCubical();
// The programs are cubist-tests/polynomial_algebra_*.cubist, whose
// comments state each refusal (tests/cubist-tests.test.mjs); here, the
// assumptions of the archive's lemmas and of the cases.
const cases = (t, name) => checkTestModule(t, name, { module, options: { collectReferences: false } });
const allowed = /^(LEM|Truncate(?:Intro|Prop|Elim)?)$/;
const checkedWithoutNewAxioms = (p, name) => {
  const s = p.symbols[name];
  assert.equal(s?.verified, true, name);
  const axioms = s.axioms.map(id => p.checker.assumptionLabels.get(id));
  assert.ok(axioms.every(a => allowed.test(a)), `${name}: ${axioms}`);
};

test("formal division, uniqueness, root bounds and Bezout are checked without extra axioms", async t => {
  const { program: p, result } = await cases(t, "polynomial_algebra_polynomial_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["polynomial_division__polynomial_division", "polynomial_division_unique__polynomial_division_unique", "polynomial_root_bound__polynomial_root_bound", "polynomial_bezout__polynomial_bezout"])
    checkedWithoutNewAxioms(p, name);
});

test("adjoined roots and embeddings into a root field are constructed, not assumed", async t => {
  const { program: p, result } = await cases(t, "polynomial_algebra_adjoined_root_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["polynomial_residue_field__PolynomialResidueField", "polynomial_adjoin__adjoined_root_is_root", "polynomial_root_embeddings__adjoin_root_embedding", "polynomial_annihilator__annihilator_generator_irreducible"])
    checkedWithoutNewAxioms(p, name);
});

test("zero polynomial is excluded from root bounds and division by zero", async t => {
  const { result } = await cases(t, "polynomial_algebra_invalid_polynomial_claims");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(s => !s.verified));
  assert.ok(result.gaps.every(g => g.module === "polynomial_algebra_invalid_polynomial_claims"), JSON.stringify(result.gaps));
});
