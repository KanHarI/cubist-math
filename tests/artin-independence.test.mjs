import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { archiveReader } from "../tools/module-sources.mjs";

const module = await createCubical();

test("finite families of distinct field embeddings and extension loops are linearly independent", async t => {
  const p = new CubicalProgram(module, archiveReader("artin_independence_regression"), { collectReferences: false });
  t.after(() => p.dispose());
  const result = await p.check(
    "import artin_finite_relations; import artin_loop_independence; def checked : Unit { exact tt; }",
    "artin_independence_regression",
  );
  assert.deepEqual(result.gaps, []);

  for (const name of [
    "artin_hom_independence__field_mul_left_cancel_nonzero",
    "artin_hom_independence__distinct_embeddings_two_independent",
    "artin_finite_relations__hom_family_twisted_relation",
    "artin_finite_relations__distinct_field_embeddings_independent",
    "artin_loop_independence__extension_loop_embedding_action",
    "artin_loop_independence__distinct_extension_loops_independent",
  ]) assert.equal(p.symbols[name]?.verified, true, name);

  const allowed = ["LEM", "Truncate", "TruncateElim"].sort();
  for (const name of [
    "artin_finite_relations__distinct_field_embeddings_independent",
    "artin_loop_independence__distinct_extension_loops_independent",
  ]) {
    const axioms = p.symbols[name].axioms.map(id => p.checker.assumptionLabels.get(id)).sort();
    assert.deepEqual(axioms, allowed, name);
  }
});
