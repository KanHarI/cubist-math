import { cubicalSourceFile } from "../web/cubical-sources.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { basename, dirname, resolve } from "node:path";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
const selected = JSON.parse(process.env.MATHSCRIPT_TEST_PROOFS ?? "[]");
if (!selected.length) throw new Error("Select sources with npm test -- --cubical MODULE.");
const module = await createCubical();
for (const path of selected) {
  test(`cubical proof: ${basename(path)}`, async t => {
    const program = new CubicalProgram(module,
      name => readFile(new URL(`../web/proofs/${cubicalSourceFile(name)}`, import.meta.url), "utf8"));
    t.after(() => program.dispose());
    const name = basename(path, ".proof");
    const sourcePath = resolve(dirname(path)) === resolve("web/proofs")
      ? new URL(`../web/proofs/${cubicalSourceFile(name)}`, import.meta.url) : path;
    const result = await program.check(await readFile(sourcePath, "utf8"), name);
    assert.equal(result.complete, true, JSON.stringify(result.gaps, null, 2));
    t.diagnostic(`${result.outputs.length} declarations; ${result.instructionCount.toLocaleString()} native C checking steps`);
    t.diagnostic(`Axioms used: ${result.axiomCount ?? 0}`);
  });
}
