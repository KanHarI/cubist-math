// Check that edited library modules keep their checked meaning.
//   node tools/verify-proof-migration.mjs [--base REV] [--level identical|types]
//     [--json FILE] [--ledger FILE] [--no-dependents] [--experimental h1]
//     [--edited-root DIR]
//     [--edited-file FILE --declarations name,...] [module ...]
// Without module names, every archive/first-library module modified relative to the base
// revision (default HEAD) is checked. Every module that imports a checked
// module, directly or not, is compared too, against the edited definitions;
// --no-dependents skips them. See tools/proof-migration.mjs.
import { readFile, readdir, writeFile } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";
import { verifyMigration } from "./proof-migration.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";

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
const ledgerFile = option("--ledger");
const ledger = ledgerFile ? JSON.parse(await readFile(ledgerFile,"utf8")) : null;
const editedRoot = resolve(root,option("--edited-root") ?? "archive/first-library");
const editedFile = option("--edited-file");
const selected = option("--declarations")?.split(",");
// Kernel extensions under review to enable, as the CLI's --experimental=h1.
const experimental = (option("--experimental") ?? "").split(",").filter(Boolean);
if (args.some(arg => arg.startsWith("--"))) throw new Error(`Unknown option: ${args.find(arg => arg.startsWith("--"))}`);
const git = gitArgs => execFileSync("git", gitArgs, { cwd: root, encoding: "utf8", maxBuffer: 1 << 28 });
const modules = args.length ? args : git(["diff", "--name-only", base, "--", "archive/first-library"]).split("\n")
  .filter(path => path.endsWith(".cubist")).map(path => path.slice("archive/first-library/".length, -".cubist".length));
if (!modules.length) { console.log("No modified library modules."); process.exit(0); }
if((editedFile || selected) && (modules.length!==1 || !noDependents))
  throw Error("--edited-file and --declarations require one explicit module and --no-dependents.");

const readEdited = async name => {
  if(editedFile && name===modules[0])return readFile(resolve(root,editedFile),"utf8");
  try { return await readFile(`${editedRoot}/${name}.cubist`,"utf8"); }
  catch(error) { if(error.code!=="ENOENT")throw error; return readFile(`${root}archive/first-library/${name}.cubist`,"utf8"); }
};
const changed = new Set(modules);
if (!noDependents) {
  const importers = new Map();
  for (const file of (await readdir(`${root}archive/first-library`)).filter(name => name.endsWith(".cubist"))) {
    const name = file.slice(0, -".cubist".length);
    for (const [, dependency] of (await readEdited(name)).matchAll(/^\s*import\s+([A-Za-z_][A-Za-z_0-9]*)\s*;/gm))
      importers.set(dependency, [...(importers.get(dependency) ?? []), name]);
  }
  for (const module of modules) for (const importer of importers.get(module) ?? [])
    if (!modules.includes(importer)) modules.push(importer);
}
const originals = new Map();
const readOriginal = async name => {
  if (!originals.has(name)) {
    const paths = [`library/${name}.cubist`,`archive/first-library/${name}.cubist`];
    const available = new Set(git(["ls-tree","--name-only",base,"--",...paths]).trim().split("\n"));
    const path = paths.find(path=>available.has(path));
    // New shared foundation modules have no archived predecessor. Both
    // checked versions may import them; compared modules still use the base.
    if(!path && modules.includes(name))throw Error(`No baseline for compared module ${name} at ${base}.`);
    originals.set(name,path ? git(["show",`${base}:${path}`]) : await readFile(`${root}library/${name}.cubist`,"utf8"));
  }
  return originals.get(name);
};
// A stale WASM kernel or translator copy would run code it does not contain.
assertFreshBuild();
const declarations=selected ? {[modules[0]]:selected} : null;
const reports = await verifyMigration({ modules, readOriginal, readEdited, level, experimental, ledger, declarations });
let failures = 0;
for (const report of reports) {
  failures += report.failures.length;
  console.log(`${report.failures.length ? "FAIL" : "ok  "} ${report.module}${changed.has(report.module) ? "" : " (dependent)"}: ${report.identical} identical, ` +
    `${report.typesPreserved} with preserved types, ${report.ledgerAccepted} exact ledger changes`);
  if(report.selectedDeclarations)console.log(`       scope: ${report.selectedDeclarations.join(", ")} only`);
  for (const { name, reason } of report.failures) console.log(`       ${name}: ${reason}`);
  for (const note of report.notes ?? []) console.log(`       note: ${note}`);
}
if (json) await writeFile(json, JSON.stringify({ base, level, reports }, null, 2) + "\n");
console.log(`${modules.length} modules (${modules.length - changed.size} dependents), ${failures} failures (level: ${level}).`);
process.exitCode = failures ? 1 : 0;
