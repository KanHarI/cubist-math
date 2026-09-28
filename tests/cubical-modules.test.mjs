import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { basename } from "node:path";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
const selected = JSON.parse(process.env.MATHSCRIPT_TEST_PROOFS ?? "[]");
if (!selected.length) throw new Error("Select sources with npm test -- MODULE.");
const module = await createCubical();
// Each selected file resolves its imports as the CLI's check does: an archive
// file only from the archive, any other file library-first after its directory.
for (const path of selected) {
  test(`cubical proof: ${basename(path)}`, async t => {
    const program = new CubicalProgram(module, sourceReader({ path }),
      { optimizations: JSON.parse(process.env.MATHSCRIPT_OPTIMIZATIONS ?? "{}") });
    t.after(() => program.dispose());
    const result = await program.check(await readFile(path, "utf8"), basename(path, ".cubist"));
    assert.equal(result.complete, true, JSON.stringify(result.gaps, null, 2));
    t.diagnostic(`${result.outputs.length} declarations; ${result.instructionCount.toLocaleString()} native C checking steps`);
    t.diagnostic(`Axioms used: ${result.axiomCount ?? 0}`);
  });
}
