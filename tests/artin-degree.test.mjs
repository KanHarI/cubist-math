import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { archiveReader } from "../tools/module-sources.mjs";

const module = await createCubical();

test("Artin fixed-field degree theorem is checked for a merely finite automorphism subgroup", async t => {
  const p = new CubicalProgram(module, archiveReader("artin_degree_regression"), { collectReferences: false });
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
  assert.deepEqual(axioms, ["LEM", "Truncate", "TruncateElim", "TruncateIntro", "TruncateProp"]);
});
