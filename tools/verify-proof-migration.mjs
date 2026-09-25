// Check that edited library modules keep their checked meaning.
//   node tools/verify-proof-migration.mjs [--base REV] [--level identical|types]
//     [--json FILE] [--no-dependents] [module ...]
// Without module names, every web/proofs module modified relative to the base
// revision (default HEAD) is checked. Every module that imports a checked
// module, directly or not, is compared too, against the edited definitions;
// --no-dependents skips them. See tools/proof-migration.mjs.
import { readFile, readdir, writeFile } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { verifyMigration } from "./proof-migration.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));
const args = process.argv.slice(2), option = name => {
  const index = args.indexOf(name);
  if (index < 0) return undefined;
  const value = args[index + 1];
  args.splice(index, 2);
  return value;
};
const noDependents = args.includes("--no-dependents");
if (noDependents) args.splice(args.indexOf("--no-dependents"), 1);
const base = option("--base") ?? "HEAD", level = option("--level") ?? "identical", json = option("--json");
if (args.some(arg => arg.startsWith("--"))) throw new Error(`Unknown option: ${args.find(arg => arg.startsWith("--"))}`);
const git = gitArgs => execFileSync("git", gitArgs, { cwd: root, encoding: "utf8", maxBuffer: 1 << 28 });
const modules = args.length ? args : git(["diff", "--name-only", base, "--", "web/proofs"]).split("\n")
  .filter(path => path.endsWith(".cubist")).map(path => path.slice("web/proofs/".length, -".cubist".length));
if (!modules.length) { console.log("No modified library modules."); process.exit(0); }

const readEdited = name => readFile(`${root}web/proofs/${name}.cubist`, "utf8");
const changed = new Set(modules);
if (!noDependents) {
  const importers = new Map();
  for (const file of (await readdir(`${root}web/proofs`)).filter(name => name.endsWith(".cubist"))) {
    const name = file.slice(0, -".cubist".length);
    for (const [, dependency] of (await readEdited(name)).matchAll(/^\s*import\s+([A-Za-z_][A-Za-z_0-9]*)\s*;/gm))
      importers.set(dependency, [...(importers.get(dependency) ?? []), name]);
  }
  for (const module of modules) for (const importer of importers.get(module) ?? [])
    if (!modules.includes(importer)) modules.push(importer);
}
const originals = new Map();
const readOriginal = async name => {
  if (!originals.has(name)) originals.set(name, git(["show", `${base}:web/proofs/${name}.cubist`]));
  return originals.get(name);
};
const reports = await verifyMigration({ modules, readOriginal, readEdited, level });
let failures = 0;
for (const report of reports) {
  failures += report.failures.length;
  console.log(`${report.failures.length ? "FAIL" : "ok  "} ${report.module}${changed.has(report.module) ? "" : " (dependent)"}: ${report.identical} identical, ` +
    `${report.typesPreserved} with preserved types, ${report.templates} templates`);
  for (const { name, reason } of report.failures) console.log(`       ${name}: ${reason}`);
  for (const note of report.notes ?? []) console.log(`       note: ${note}`);
}
if (json) await writeFile(json, JSON.stringify({ base, level, reports }, null, 2) + "\n");
console.log(`${modules.length} modules (${modules.length - changed.size} dependents), ${failures} failures (level: ${level}).`);
process.exitCode = failures ? 1 : 0;
