import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

const module = await createCubical();
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");

test("evaluation vectors of distinct embeddings separate coefficients", async t => {
  const p = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => p.dispose());
  const result = await p.check("import artin_fixed_evaluation; def checked : Unit { exact tt; }", "artin_evaluation_regression");
  assert.deepEqual(result.gaps, []);
  for (const name of [
    "artin_evaluation__embedding_evaluations_separate",
    "artin_evaluation__embedding_evaluations_detect_nonzero",
    "artin_evaluation__loop_evaluations_separate",
    "artin_evaluation__loop_evaluations_detect_nonzero",
    "artin_evaluation_matrix__coordinate_rows_separating_bound",
    "artin_evaluation_matrix__coordinate_dot_rows_zero",
    "artin_evaluation_matrix__coordinate_map_not_kernel_trivial",
    "artin_evaluation_matrix__coordinate_nontrivial_implication_witness",
    "artin_evaluation_matrix__coordinate_map_nonzero_kernel",
    "artin_evaluation_matrix__embedding_evaluation_rank_step",
    "artin_evaluation_matrix__embedding_evaluation_outside_span",
    "artin_evaluation_matrix__embedding_evaluation_extend_independent",
    "artin_evaluation_matrix__coordinate_square_injective_surjective",
    "artin_evaluation_basis__distinct_embeddings_evaluation_basis",
    "artin_evaluation_basis__distinct_extension_loops_evaluation_basis",
    "artin_fixed_evaluation__finite_subgroup_evaluation_basis",
    "artin_fixed_evaluation__finite_subgroup_evaluation_basis",
  ]) assert.equal(p.symbols[name]?.verified, true, name);

  const allowed = ["LEM(U0)", "Truncate(U0)", "TruncateElim(U0)", "TruncateIntro(U0)", "TruncateProp(U0)"];
  for (const name of [
    "artin_evaluation_matrix__embedding_evaluation_rank_step",
    "artin_evaluation_basis__distinct_embeddings_evaluation_basis",
    "artin_evaluation_basis__distinct_extension_loops_evaluation_basis",
  ]) {
    const axioms = p.symbols[name].axioms.map(id => p.checker.assumptionLabels.get(id)).sort();
    assert.deepEqual(axioms, allowed, name);
  }
});
