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
import { readFile, readdir, writeFile } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { resolve } from "node:path";
import { verifyMigration } from "./proof-migration.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";
import { migrationSourceReader } from "./migration-sources.mjs";
import { placeOfFile } from "./module-sources.mjs";
import { moduleRoots } from "../web/module-resolution.mjs";
import { historicalSource, currentSyntax, reservedBindingRenaming } from "../web/cubist/legacy-syntax.mjs";
import { parse, languageKeywords } from "../web/cubist/parser.mjs";

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
const editedRoot = resolve(root,option("--edited-root") ?? "archive/first-library");
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

const editedPlaces = new Map();
const readEdited = async name => {
  const candidates = editedFile && name===modules[0] ? [resolve(root,editedFile)]
    : [`${editedRoot}/${name}.cubist`,`${root}archive/first-library/${name}.cubist`];
  for (const path of candidates) {
    try {
      const text = await readFile(path,"utf8");
      editedPlaces.set(name,placeOfFile(path)); return text;
    } catch(error) { if(error.code!=="ENOENT")throw error; }
  }
  throw Error(`No edited source for ${name}.`);
};
readEdited.placeOf = name => editedPlaces.get(name);
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
const available = new Set(git(["ls-tree","-r","--name-only",base,"--","library","archive/first-library"]).trim().split("\n"));
// A module name that was a keyword is migrated with its imports. Read its
// historical file by the old name while checking it in the current namespace.
const originalModulePath = (place, name) => {
  const current = `${moduleRoots[place]}${name}.cubist`;
  if (available.has(current)) return current;
  const old = name.endsWith("_") && languageKeywords.has(name.slice(0, -1))
    ? `${moduleRoots[place]}${name.slice(0, -1)}.cubist` : current;
  return available.has(old) ? old : current;
};
const originalSources = new Map(), originalSyntax = new Map();
const originalSource = path => {
  if (!originalSources.has(path)) originalSources.set(path, git(["show",`${base}:${path}`]));
  return originalSources.get(path);
};
// Fresh replacements must agree in a dependency and every importer, even
// when the conflicting local name occurs in only one of those modules.
const renaming = reservedBindingRenaming([...available].filter(path => path.endsWith(".cubist"))
  .map(path => currentSyntax(originalSource(path))));
const importedDeclarationsOf = (path, seen = new Set(), includeOwn = true) => {
  if (!available.has(path) || seen.has(path)) return [];
  seen.add(path);
  if (!originalSyntax.has(path)) {
    try { originalSyntax.set(path, parse(currentSyntax(originalSource(path)), false, { bindable: [...languageKeywords] })); }
    catch { originalSyntax.set(path, { declarations: [], imports: [] }); }
  }
  const syntax = originalSyntax.get(path), place = path.startsWith(moduleRoots.archive) ? "archive" : "library";
  const declarations = [];
  for (const dependency of syntax.imports) {
    const paths = place === "archive" ? [originalModulePath("archive", dependency)]
      : [originalModulePath("library", dependency), originalModulePath("archive", dependency)];
    const next = paths.find(path => available.has(path));
    if (next) declarations.push(...importedDeclarationsOf(next, seen));
  }
  if (includeOwn) declarations.push(...syntax.declarations);
  return declarations;
};
// Until 2026-10-05 every module had Nat without importing it, from the
// kernel and then from an implicit import of nat; a base of that time is read
// with the import (legacy-syntax.mjs, historicalSource). A later base has
// bundledNat in its program and imports nat where it uses it.
const implicitNat = (() => { try { return !git(["show",`${base}:web/cubical-program.mjs`]).includes("bundledNat"); } catch { return true; } })();
// Until 2026-10-06 prefix - reversed paths and coordinates; a base of that
// time is read with ~ for it. A later base's legacy rewrite knows minusReverses.
const minusReverses = (() => { try { return !git(["show",`${base}:web/cubist/legacy-syntax.mjs`]).includes("minusReverses"); } catch { return true; } })();
// Until L2.10j an operator or numeral outside any selection was read by
// name. A base of that time is read so: its modules keep the reading, and
// today's modules select its nat's notation (historicalSource).
const nameBased = (() => { try { return !git(["show",`${base}:web/translator/translate.mjs`]).includes("nameBased"); } catch { return true; } })();
const historical = new Set();
// A module moved from the archive into the library since the base, as nat
// was, is read from its old path but lives in the library, where
// today's checks place it, so that a check holds it once.
const movedToLibrary = new Set([...available].filter(path => path.startsWith(moduleRoots.archive))
  .map(path => path.slice(moduleRoots.archive.length, -".cubist".length))
  .filter(name => existsSync(`${root}${moduleRoots.library}${name}.cubist`)
    && !existsSync(`${root}${moduleRoots.archive}${name}.cubist`)));
const readOriginal = migrationSourceReader(async (place, name) => {
  if (movedToLibrary.has(name) && place !== "library") return null;
  const path = originalModulePath(movedToLibrary.has(name) ? "archive" : place, name);
  if (!originals.has(path)) {
    // A baseline may predate a syntax change, or the implicit import of nat;
    // it is read in today's syntax, with the imports it had then.
    let text = available.has(path) ? historicalSource(originalSource(path), name,
      { implicitNat, minusReverses, renaming, importedDeclarations: importedDeclarationsOf(path, new Set(), false) }) : null;
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
// A stale WASM kernel would run code it does not contain.
assertFreshBuild();
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
