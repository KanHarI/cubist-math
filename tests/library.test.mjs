import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { libraryModules } from "../web/mathscript/modules.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// The rebuilt library under library/: every module is listed and checks completely.
// Imports resolve as the CLI's check resolves them (web/module-resolution.mjs):
// a library module imports from the library, then the archive.

// The assumptions each module's declarations use; a module not listed uses none.
const assumptions = {
  classical_axioms: ["Choice", "LEM", "Truncate"],
  universe_automorphisms: ["LEM", "Truncate", "TruncateElim", "TruncateIntro", "TruncateProp"],
  h1_classical: ["Choice[h1_truncation.Trunc]", "LEM[h1_truncation.Trunc]"],
  h1_cauchy_quotient: ["Truncate", "TruncateElim", "TruncateIntro", "TruncateProp"],
  h1_zorn_step: ["LEM[h1_truncation.Trunc]"],
};

test("every library module is listed and checks completely", async t => {
  const files = (await readdir(new URL("../library/", import.meta.url))).filter(name => name.endsWith(".cubist"))
    .map(name => name.slice(0, -".cubist".length)).sort();
  assert.deepEqual(files, [...libraryModules].sort());
  for (const name of libraryModules) {
    const path = fileURLToPath(new URL(`../library/${name}.cubist`, import.meta.url));
    const program = new CubicalProgram(await createCubical(), sourceReader({ path }), {
      collectReferences: false,
    });
    t.after(() => program.dispose());
    const result = await program.check(await readFile(path, "utf8"), name);
    assert.equal(result.complete, true, `${name}: ${JSON.stringify(program.gaps)}`);
    assert.deepEqual(result.outputs.filter(output => !output.verified).map(output => output.name), [], name);
    const used = [...new Set(result.outputs.flatMap(output => output.axioms)
      .map(axiom => result.assumptionLabels[axiom] ?? axiom))].sort();
    assert.deepEqual(used, assumptions[name] ?? [], `${name}: its assumptions`);
  }
});
