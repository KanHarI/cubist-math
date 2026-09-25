import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

const module = await createCubical();
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");

test("Artin classification and the finite normal separable correspondence are checked", async t => {
  const p = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => p.dispose());
  const result = await p.check(
    "import galois_intermediate_roundtrip; def checked : Unit { exact tt; }",
    "galois_finite_correspondence_regression",
  );
  assert.deepEqual(result.gaps, []);
  for (const name of [
    "artin_degree__artin_fixed_field_degree",
    "artin_classification__artin_fixed_field_automorphism_classification",
    "artin_classification__artin_fixing_fixed_subgroup",
    "galois_normal_target__finite_normal_separable_intermediate_automorphism_count",
    "galois_intermediate_roundtrip__finite_normal_separable_fixed_fixing_intermediate",
    "galois_intermediate_roundtrip__finite_normal_separable_full_fixed_field",
    "galois_intermediate_roundtrip__finite_galois_cardinality_tower_law",
    "finite_decidable_subtypes__finite_predicate_of_finite",
    "galois_intermediate_roundtrip__finite_galois_correspondence",
  ]) assert.equal(p.symbols[name]?.verified, true, name);

  const axioms = p.symbols["galois_intermediate_roundtrip__finite_galois_correspondence"].axioms
    .map(id => p.checker.assumptionLabels.get(id)).sort();
  assert.deepEqual(axioms, [
    "LEM(U0)", "Truncate(U0)", "Truncate(U1)", "TruncateElim(U0)",
    "TruncateElim(U1)", "TruncateIntro(U0)", "TruncateProp(U0)",
  ]);
});
