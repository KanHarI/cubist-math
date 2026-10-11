// node tools/migrate-induction-hypotheses.mjs [--write] FILE.cubist ...
// Check first, migrate checked binders, and prove identical terms, types and
// assumptions before writing. With no --write, report the proposed changes.
import { readFile, writeFile } from "node:fs/promises";
import { basename, resolve } from "node:path";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "./module-sources.mjs";
import { verifyMigration } from "./proof-migration.mjs";
import { checkedHypothesisStarts, migrateInductionHypotheses } from "./induction-migration.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";

const args = process.argv.slice(2), write = args.includes("--write"), paths = args.filter(arg => arg !== "--write");
if (!paths.length || paths.some(path => !path.endsWith(".cubist")))
  throw Error("Usage: node tools/migrate-induction-hypotheses.mjs [--write] FILE.cubist ...");
assertFreshBuild();
const kernel = await createCubical();
for (const file of paths) {
  const path = resolve(file), name = basename(path, ".cubist"), source = await readFile(path, "utf8");
  const reader = sourceReader({ path }), program = new CubicalProgram(kernel, reader);
  let migration;
  try {
    const result = await program.check(source, name);
    if (!result.complete) throw Error(`${file} does not check: ${JSON.stringify(result.gaps)}`);
    migration = migrateInductionHypotheses(source, checkedHypothesisStarts(program, name));
  } finally { program.dispose(); }
  if (migration.clauses) {
    const original = Object.assign((module, importer) => module === name ? source : reader(module, importer), reader);
    const edited = Object.assign((module, importer) => module === name ? migration.source : reader(module, importer), reader);
    const [report] = await verifyMigration({ modules: [name], readOriginal: original, readEdited: edited, level: "identical" });
    if (report.failures.length) throw Error(`${file}: ${JSON.stringify(report.failures)}`);
    if (write) await writeFile(path, migration.source);
  }
  console.log(`${file}: ${migration.clauses} clauses ${write ? "migrated" : "to migrate"}`);
}
