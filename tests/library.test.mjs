import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { libraryModules } from "../web/cubist/modules.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// The rebuilt library under library/: every listed module checks completely.
// Imports resolve as the CLI's check resolves them (web/module-resolution.mjs):
// a library module imports only from the library, so a module that checks is
// self-contained.

// The assumptions each module's declarations use; a module not listed uses none.
const assumptions = {
  classical_axioms: ["Choice", "LEM"],
  universe_automorphisms: ["LEM"],
  h1_classical: ["LEM"],
  continuum_axioms: ["CH", "DecidableCH", "DecidableGCH", "GCH"],
};

test("every library module checks completely", async t => {
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

// A library axiom is labelled by its bare name (web/cubical-assumptions.mjs),
// so no two library modules may assume under one name. Each is listed here,
// as each module's assumptions are above: adding one is a reviewed change.
// The legacy builtins' labels cannot meet them: they are reserved words,
// or carry brackets, as LEM[Truncate] does.
test("the library's axioms have distinct names, which are their labels", async () => {
  const axioms = [];
  for (const name of libraryModules) {
    const source = await readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");
    for (const declaration of parse(source).declarations)
      if (declaration.value?.kind === "axiom") axioms.push([declaration.name.text, name]);
  }
  const names = axioms.map(([name]) => name);
  assert.deepEqual(names.filter((name, index) => names.indexOf(name) !== index), [], JSON.stringify(axioms));
  assert.deepEqual(axioms, [["LEM", "classical_axioms"], ["Choice", "classical_axioms"], ["CH", "continuum_axioms"],
    ["DecidableCH", "continuum_axioms"], ["GCH", "continuum_axioms"], ["DecidableGCH", "continuum_axioms"]]);
});
