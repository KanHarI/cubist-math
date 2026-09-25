import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { libraryModules } from "../web/mathscript/modules.mjs";

// The rebuilt library under library/: every module is listed and checks completely.
const read = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");

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
    assert.deepEqual(result.outputs.flatMap(output => output.axioms), [], `${name} uses no assumption`);
  }
});
