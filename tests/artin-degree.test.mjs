import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

const module = await createCubical();
const readSource = name => readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");

test("Artin fixed-field degree theorem is checked for a merely finite automorphism subgroup", async t => {
  const p = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => p.dispose());
  const result = await p.check("import artin_degree; def checked : Unit { exact tt; }", "artin_degree_regression");
  assert.deepEqual(result.gaps, []);
  for (const name of [
    "artin_equivariance__subgroup_evaluation_coefficient_fixed",
    "artin_equivariance__subgroup_evaluation_spans_fixed_field",
    "artin_degree__subgroup_evaluation_points_independent",
    "artin_degree__finite_subgroup_fixed_degree_upper_bound",
    "artin_degree__finite_subgroup_fixed_degree_lower_bound",
    "artin_degree__artin_fixed_field_degree",
  ]) assert.equal(p.symbols[name]?.verified, true, name);

  const axioms = p.symbols["artin_degree__artin_fixed_field_degree"].axioms
    .map(id => p.checker.assumptionLabels.get(id)).sort();
  assert.deepEqual(axioms, ["LEM(U0)", "Truncate(U0)", "TruncateElim(U0)", "TruncateIntro(U0)", "TruncateProp(U0)"]);
});
