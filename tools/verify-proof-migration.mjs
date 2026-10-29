// Check that edited library modules keep their checked meaning.
//   node tools/verify-proof-migration.mjs [--base REV] [--level identical|types]
//     [--json FILE] [--ledger FILE] [--no-dependents]
//     [--edited-root DIR]
//     [--edited-file FILE --declarations name,...] [module ...]
// Without module names, every archive/first-library module modified relative to the base
// revision (default HEAD) is checked. Every module that imports a checked
// module, directly or not, is compared too, against the edited definitions;
// --no-dependents skips them. See tools/proof-migration.mjs.
import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { isAbsolute } from "node:path";
import { archiveModules } from "../web/cubist/modules.mjs";
import { verifyMigration } from "./proof-migration.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";
import { migrationSourceReader, historicalModulePaths, historicalMigrationSources, unaryNaturalBase } from "./migration-sources.mjs";
import { readFileAt } from "./module-sources.mjs";
import { moduleRoots, searchOrder } from "../web/module-resolution.mjs";
import { historicalRenamingAt, historicalSource } from "../web/cubist/legacy-syntax.mjs";
import { parse } from "../web/cubist/parser.mjs";

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
const requestedBase = option("--base"), level = option("--level") ?? "identical", json = option("--json");
const ledgerFile = option("--ledger");
const ledger = ledgerFile ? JSON.parse(await readFile(ledgerFile,"utf8")) : null;
const base = requestedBase ?? ledger?.base ?? "HEAD";
// Paths below the repository's root, as the operating system reads them:
// resolve would drop a `link/..` as text, where reading leaves the link's
// target (module-sources.mjs, canonicalFile).
const fromRoot = path => isAbsolute(path) ? path : `${root}${path}`;
const editedRoot = fromRoot(option("--edited-root") ?? "archive/first-library");
const editedFile = option("--edited-file");
const selected = option("--declarations")?.split(",");
if (args.some(arg => arg.startsWith("--"))) throw new Error(`Unknown option: ${args.find(arg => arg.startsWith("--"))}`);
const git = gitArgs => execFileSync("git", gitArgs, { cwd: root, encoding: "utf8", maxBuffer: 1 << 28 });
if (ledger?.base && git(["rev-parse", base]).trim() !== git(["rev-parse", ledger.base]).trim())
  throw Error(`Ledger baseline is ${ledger.base}; requested --base ${base} names a different revision.`);
const modules = args.length ? args : git(["diff", "--name-only", base, "--", "archive/first-library"]).split("\n")
  .filter(path => path.endsWith(".cubist")).map(path => path.slice("archive/first-library/".length, -".cubist".length));
if (!modules.length) { console.log("No modified library modules."); process.exit(0); }
if((editedFile || selected) && (modules.length!==1 || !noDependents))
  throw Error("--edited-file and --declarations require one explicit module and --no-dependents.");

// A stale WASM kernel would run code it does not contain.
assertFreshBuild();

const editedPlaces = new Map();
const readEdited = async name => {
  const candidates = editedFile && name===modules[0] ? [fromRoot(editedFile)]
    : [`${editedRoot}/${name}.cubist`,`${root}archive/first-library/${name}.cubist`];
  for (const path of candidates) {
    try {
      // Read as its place is taken: one file for both (readFileAt).
      const found = await readFileAt(path);
      editedPlaces.set(name,found.root); return found.text;
    } catch(error) { if(error.code!=="ENOENT")throw error; }
  }
  throw Error(`No edited source for ${name}.`);
};
readEdited.placeOf = name => editedPlaces.get(name);
const changed = new Set(modules);
if (!noDependents) {
  const importers = new Map();
  for (const name of [...archiveModules].sort()) {
    for (const [, dependency] of (await readEdited(name)).matchAll(/^\s*import\s+([A-Za-z_][A-Za-z_0-9]*)\s*;/gm))
      importers.set(dependency, [...(importers.get(dependency) ?? []), name]);
  }
  for (const module of modules) for (const importer of importers.get(module) ?? [])
    if (!modules.includes(importer)) modules.push(importer);
}
const originals = new Map();
const available = new Set(git(["ls-tree","-r","--name-only",base,"--","library","archive/first-library"]).trim().split("\n"));
// Until 2026-10-05 every module had Nat without importing it, from the
// kernel and then from an implicit import of nat; a base of that time is read
// with the import (legacy-syntax.mjs, historicalSource). A later base has
// bundledNat (later bundledUNat) in its program and uses explicit imports.
const implicitNat = (() => { try { return !/bundled(?:U)?Nat/.test(git(["show",`${base}:web/cubical-program.mjs`])); } catch { return true; } })();
// Read the actual base foundation, not today's public Nat alias. The
// location can precede the foundation's move out of the archive.
const unaryNat=unaryNaturalBase({available,readSource:path=>git(["show",`${base}:${path}`])});
// Until 2026-10-06 prefix - reversed paths and coordinates; a base of that
// time is read with ~ for it. A later base's legacy rewrite knows minusReverses.
const minusReverses = (() => { try { return !git(["show",`${base}:web/cubist/legacy-syntax.mjs`]).includes("minusReverses"); } catch { return true; } })();
// Until L2.10j an operator or numeral outside any selection was read by
// name. A base of that time is read so: its modules keep the reading, and
// today's modules select its nat's notation (historicalSource).
const nameBased = (() => { try { return !git(["show",`${base}:web/translator/translate.mjs`]).includes("nameBased"); } catch { return true; } })();
// Until #317 (2026-10-26) axiom meant nothing, and a source could name
// anything by it; a base since reads `def Name := axiom F;` as the axiom
// form and reserves the word (legacy-syntax.mjs, historicalKeywords).
const axiomForm = (() => { try { return git(["show",`${base}:web/cubist/parser.mjs`]).includes('kind: "axiom"'); } catch { return false; } })();
const historical = new Set();
// A module moved from the archive into the library since the base, as nat
// was, is read from its old path but lives in the library, where
// today's checks place it, so that a check holds it once.
const movedToLibrary = new Set([...available].filter(path => path.startsWith(moduleRoots.archive))
  .map(path => path.slice(moduleRoots.archive.length, -".cubist".length))
  .filter(name => existsSync(`${root}${moduleRoots.library}${name}.cubist`)
    && !existsSync(`${root}${moduleRoots.archive}${name}.cubist`)));
// The shared renaming plan, once made: module paths read its renamed
// modules by the words they rename.
let renaming = null;
const paths = historicalModulePaths({ available, movedToLibrary, unaryNat, spellings: () => renaming ?? historicalRenamingAt({ axiomForm }) });
const originalModulePath = paths.modulePath;
const historicalSources = historicalMigrationSources({ available, ...paths, implicitNat, axiomForm,
  readSource: path => git(["show", `${base}:${path}`]),
});
// Build one plan across the selected checks before rewriting any dependency.
// Also include baseline dependencies introduced by an edited source.
const selectedPaths = new Set();
for (const name of modules) {
  const original = ["archive", "library"].map(place => originalModulePath(place, name)).find(path => available.has(path));
  if (original) selectedPaths.add(original);
  const edited = parse(await readEdited(name));
  for (const dependency of edited.imports) {
    const path = searchOrder(readEdited.placeOf(name)).map(place => originalModulePath(place, dependency)).find(path => available.has(path));
    if (path) selectedPaths.add(path);
  }
}
renaming = historicalSources.renamingFor(selectedPaths);
const readOriginal = migrationSourceReader(async (place, name) => {
  const path = originalModulePath(place, name);
  if (path === null) return null;
  if (!originals.has(path)) {
    // A baseline may predate a syntax change, or the implicit import of nat;
    // it is read in today's syntax, with the imports it had then.
    let text = available.has(path) ? historicalSource(historicalSources.source(path), unaryNat&&name==="unat"?"nat":name,
      { implicitNat, minusReverses, renaming, unaryNat, axiomForm, importedDeclarations: historicalSources.importsOf(path) }) : null;
    if (text !== null) historical.add(name);
    // A new shared foundation has no predecessor. It is available only in
    // library resolution; archive importers never see this fallback.
    if (text === null && place === "library" && !modules.includes(name)) {
      try { text = await readFile(`${root}${path}`,"utf8"); }
      catch(error) { if(error.code!=="ENOENT")throw error; }
    }
    originals.set(path,text);
  }
  return originals.get(path);
}, modules);
readOriginal.nameBased = name => nameBased && historical.has(name);
const declarations=selected ? {[modules[0]]:selected} : null;
const reports = await verifyMigration({ modules, readOriginal, readEdited, level, ledger, declarations });
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
