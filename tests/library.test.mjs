import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { libraryModules } from "../web/mathscript/modules.mjs";
import { cubicalSourceFile } from "../web/cubical-sources.mjs";

// The rebuilt library under library/: every module is listed and checks completely.
// Imports resolve as in the CLI and the workspace: the library, then the archive.
const read = name => readFile(new URL(libraryModules.includes(name) ? `../library/${name}.cubist`
  : `../archive/first-library/${cubicalSourceFile(name)}`, import.meta.url), "utf8");

// The assumptions each module's declarations use; a module not listed uses none.
const assumptions = {
  classical_axioms: ["Choice", "LEM", "Truncate"],
  universe_automorphisms: ["LEM", "Truncate", "TruncateElim", "TruncateIntro", "TruncateProp"],
};

test("every library module is listed and checks completely", async t => {
  const files = (await readdir(new URL("../library/", import.meta.url))).filter(name => name.endsWith(".cubist"))
    .map(name => name.slice(0, -".cubist".length)).sort();
  assert.deepEqual(files, [...libraryModules].sort());
  for (const name of libraryModules) {
    const program = new CubicalProgram(await createCubical(), read, { collectReferences: false });
    t.after(() => program.dispose());
    const result = await program.check(await read(name), name);
    assert.equal(result.complete, true, `${name}: ${JSON.stringify(program.gaps)}`);
    assert.deepEqual(result.outputs.filter(output => !output.verified).map(output => output.name), [], name);
    const used = [...new Set(result.outputs.flatMap(output => output.axioms))]
      .map(axiom => axiom.replace(/^__assumption_/, "")).sort();
    assert.deepEqual(used, assumptions[name] ?? [], `${name}: its assumptions`);
  }
});
