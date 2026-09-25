import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

const module = await createCubical();
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const create = t => {
  const p = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => p.dispose());
  return p;
};
const allowed = /^(LEM\(U0\)|Truncate(?:Intro|Prop|Elim)?\(U[01]\))$/;

test("finite algebraic extensions, actual splitting fields, normality and general separable embedding counts are checked", async t => {
  const p = create(t);
  const result = await p.check(`import embedding_counts;
    import normal_extensions;
    import finitely_generated_algebraic; def checked : Unit { exact tt; }`, "algebraic_milestones");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of [
    "minimal_polynomials__minimal_polynomial_irreducible",
    "finite_algebraic_extensions__finite_extension_algebraic",
    "finitely_generated_algebraic__finitely_generated_algebraic_is_finite",
    "finitely_generated_algebraic__algebraic_finitely_generated_extension_finite",
    "simple_algebraic_extensions__simple_root_field_equality",
    "finite_embedding_extensions__finite_extension_embedding_exists",
    "splitting_fields__finite_splitting_field_exists",
    "normal_extensions__finite_splitting_field_normal",
    "separability_base_change__separable_elements_enlarge_base",
    "embedding_tower_types__embedding_tower_type_equality",
    "embedding_counts__finite_separable_embedding_count",
  ]) {
    const symbol = p.symbols[name];
    assert.equal(symbol?.verified, true, name);
    const axioms = symbol.axioms.map(id => p.checker.assumptionLabels.get(id));
    assert.ok(axioms.every(a => allowed.test(a)), `${name}: ${axioms.join(", ")}`);
  }
  // The intermediate finite-choice construction is constructive. Univalence
  // transports the resulting count; it is not an extra axiom in this kernel.
  assert.ok(p.symbols.finite_dependent_counts__finite_mere_choice.axioms.every(id => /^Truncate(?:Intro|Prop|Elim)?\(U0\)$/.test(p.checker.assumptionLabels.get(id))));

  const negative = create(t);
  const invalid = await negative.check(`import embedding_counts;
    def embedding_without_closed_target(K : AlgebraicField, L : AlgebraicField,
      e : FieldEmbedding(K, L), finite : FiniteExtension(K, embedding_as_extension(K, L, e)),
      T : AlgebraicField, j : FieldEmbedding(K, T)) : Mere(EmbeddingsOver(K, L, e, T, j)) {
      exact finite_extension_embedding_exists(K, L, e, finite, T, j);
    }
    def all_separable_extensions_have_one_embedding(K : AlgebraicField, L : AlgebraicField,
      e : FieldEmbedding(K, L), finite : FiniteExtension(K, embedding_as_extension(K, L, e)),
      separable : SeparableExtension(K, L, e), T : AlgebraicField, closed : AlgebraicallyClosed(T),
      j : FieldEmbedding(K, T)) : HasCardinality(EmbeddingsOver(K, L, e, T, j), 1) {
      exact finite_separable_embedding_count(K, L, e, finite, separable, T, closed, j);
    }`, "invalid_embedding_claims");
  assert.equal(invalid.complete, false);
  assert.equal(invalid.outputs.length, 2);
  assert.ok(invalid.outputs.every(o => !o.verified));
  assert.ok(invalid.gaps.every(g => g.module === "invalid_embedding_claims"), JSON.stringify(invalid.gaps));
});

test("the formal F2 polynomial computes the two F4 roots and rejects zero as a root", async t => {
  const p = create(t);
  const result = await p.check("import f4_formal_polynomial; def checked : Unit { exact tt; }", "formal_f4_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["f2_quadratic_alpha_root", "f2_quadratic_other_root", "f2_quadratic_nonzero", "f2_quadratic_roots_distinct"])
    assert.equal(p.symbols[`f4_formal_polynomial__${name}`]?.verified, true, name);
  const negative = create(t);
  const invalid = await negative.check(`import f4_formal_polynomial;
    def zero_is_a_root : PolynomialRoot(F2, F4, f2_f4_embedding, f2_quadratic, f4_0) {
      exact f2_quadratic_alpha_root;
    }`, "invalid_f4_root");
  assert.equal(invalid.complete, false);
  assert.equal(invalid.outputs[0].verified, false);
  assert.ok(invalid.gaps.every(g => g.module === "invalid_f4_root"), JSON.stringify(invalid.gaps));
});

test("embedding roundtrip stays within the conversion budget with inspector references enabled", async t => {
  // This import order previously exhausted 100 million steps in the roundtrip.
  // Keep reference collection enabled: inspection can change elaboration caches.
  const p = new CubicalProgram(module, readSource, {
    collectReferences: true,
    onDeclarationStart: (moduleName, declaration) => {
      const isRoundtrip = moduleName === "simple_extension_embeddings"
        && declaration.name.text === "embedding_root_roundtrip";
      const budget = isRoundtrip ? 10000000n : 100000000n;
      p.kernel.stepBudget = budget;
      p.kernel.module._cb_step_budget(p.kernel.handle, Number(budget), 0);
    },
  });
  t.after(() => p.dispose());
  p.kernel.withGrowingBudget = operation => operation();
  const result = await p.check("import separable_divisors; def checked : Unit { exact tt; }", "roundtrip_budget");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.equal(p.symbols.simple_extension_embeddings__embedding_root_roundtrip.verified, true);
});

test("finite separable count step keeps tower and root-count conversions bounded", async t => {
  // Use a deterministic native work budget rather than a CI wall-clock limit.
  // The standalone corpus benchmark separately checks the one-second target.
  const bounded = new Set(["embedding_tower_degree_count", "finite_separable_count_step"]);
  const p = new CubicalProgram(module, readSource, {
    collectReferences: true,
    onDeclarationStart: (moduleName, declaration) => {
      const budget = moduleName === "embedding_counts" && bounded.has(declaration.name.text)
        ? 10000000n : 100000000n;
      p.kernel.stepBudget = budget;
      p.kernel.module._cb_step_budget(p.kernel.handle, Number(budget), 0);
    },
  });
  t.after(() => p.dispose());
  p.kernel.withGrowingBudget = operation => operation();
  const result = await p.check("import embedding_counts; def checked : Unit { exact tt; }", "count_step_budget");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of [...bounded, "finite_separable_embedding_count"])
    assert.equal(p.symbols[`embedding_counts__${name}`]?.verified, true, name);
});
