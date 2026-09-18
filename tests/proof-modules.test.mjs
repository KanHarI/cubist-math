import test from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";

const selected = JSON.parse(process.env.MATHSCRIPT_TEST_PROOFS ?? "[]");
if (!selected.length) throw new Error("Select proof modules with npm test -- --module NAME.");
const module = await createKernel();
for (const path of selected) {
  test(`proof: ${path.split("/").at(-1)}`, async t => {
    const { source, sources } = await loadProof(path);
    const c = compile(module, source, sources);
    try {
      if (c.mode === "construction") {
        for (const check of c.checks) assert.ok(c.kernel.verify(check.proposition, check.proof), check.proof);
      } else {
        for (const output of c.outputs) {
          assert.ok(c.kernel.verify(output.proposition, output.binding), output.name);
        }
      }
      t.diagnostic(`${c.outputs.length} declarations; ${c.instructionCount.toLocaleString()} kernel steps; ${Object.keys(sources).length} source imports`);
      const axioms = [...new Set(c.outputs.flatMap(output => c.kernel.axiomsFor(output.binding)))].sort();
      t.diagnostic(`Axioms used: ${axioms.join(", ") || "none"}`);
    } finally { c.kernel.dispose(); }
  });
}
