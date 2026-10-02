import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// The archive's path_actions keeps the types its callers rely on: explicit
// contracts on its helpers' inferred types (docs/cubical/path-actions-migration.md).
test("path_actions keeps its public contracts", async t => {
  const path = fileURLToPath(new URL("./fixtures/path-actions-contracts.cubist", import.meta.url));
  const program = new CubicalProgram(await createCubical(), sourceReader({ path }), { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(await readFile(path, "utf8"), "path_actions_contracts");
  assert.equal(result.complete, true, JSON.stringify(result.gaps, null, 2));
  assert.equal(result.outputs.length, 8);
});
