import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { archiveReader } from "../tools/module-sources.mjs";

const module = await createCubical();

test("a finite automorphism subgroup gives distinct embeddings over its fixed field", async t => {
  const p = new CubicalProgram(module, archiveReader("artin_fixed_regression"), { collectReferences: false });
  t.after(() => p.dispose());
  const result = await p.check("import artin_fixed_embeddings; def checked : Unit { exact tt; }", "artin_fixed_regression");
  assert.deepEqual(result.gaps, []);

  for (const name of [
    "galois_field_embedding",
    "fixing_automorphism_over_intermediate",
    "galois_field_embedding_injective",
    "fixed_subgroup_embedding",
    "fixed_subgroup_embedding_injective",
    "fixed_subgroup_loop_embedding",
    "fixed_subgroup_loop_embedding_action",
    "fixed_subgroup_loop_embedding_injective",
    "fixed_subgroup_distinct_embeddings",
  ]) {
    assert.equal(p.symbols[`artin_fixed_embeddings__${name}`]?.verified, true, name);
  }
  for (const name of [
    "fixed_subgroup_embedding", "fixed_subgroup_embedding_injective",
    "fixed_subgroup_loop_embedding_action", "fixed_subgroup_loop_embedding_injective",
  ])
    assert.deepEqual(p.symbols[`artin_fixed_embeddings__${name}`].axioms, [], name);
  const countAxioms = p.symbols.artin_fixed_embeddings__fixed_subgroup_distinct_embeddings.axioms
    .map(id => p.checker.assumptionLabels.get(id)).sort();
  assert.deepEqual(countAxioms, ["Truncate", "TruncateElim", "TruncateIntro", "TruncateProp"].sort());
});
