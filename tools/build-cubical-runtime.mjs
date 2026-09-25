// Package the same cubical syntax/elaboration sources used by native tests.
// Generated browser copies are build artifacts, never a second implementation.
import { mkdir, readFile, writeFile } from "node:fs/promises";
const output = new URL("../web/dist/cubical-runtime/", import.meta.url);
await mkdir(output, { recursive: true });
for (const name of ["core", "lattice", "syntax-graph", "equivalence", "translate", "proof-rewrite", "simp-registry", "number-transport", "pushouts", "path-over", "path-algebra", "public-equivalence", "dimension-slots", "dependent-transport", "adjointification"]) {
  const source = await readFile(new URL(`../lib/cubical/${name}.mjs`, import.meta.url), "utf8");
  // The copy lives in web/dist/cubical-runtime/, so imports of web/ modules
  // move up two directories instead of naming web/.
  await writeFile(new URL(`${name}.mjs`, output), source.replaceAll("../../web/", "../../"));
}
