#!/usr/bin/env node
// The baseline behind the default search fuel (web/translator/fuel.mjs; HoTT
// roadmap A4, work plan L1.3): what tactic searches and declarations spend on
// the checked workloads, with fuel unlimited. The fuel counts are
// deterministic; times, kernel work and memory are one run's observations.
//   node tools/search-fuel-baseline.mjs [--write]
// --write records the measurement, and the defaults it implies, in
// tests/fixtures/search-fuel.json, which tests/search-fuel.test.mjs keeps in
// agreement with fuel.mjs.
import { readFile, writeFile, readdir } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import os from "node:os";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { archiveModules } from "../web/cubist/modules.mjs";
import { cubicalSourceFile } from "../web/cubical-sources.mjs";
import { referenceExamples } from "../tests/reference-pages.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";
import { sourceReader } from "./module-sources.mjs";
// A stale WASM kernel would run code it does not contain.
assertFreshBuild();

const root = new URL("../", import.meta.url);
const text = path => readFile(new URL(path, root), "utf8");
// Each workload resolves its imports as its tests do. The archive's modules
// come from the archive, as do the proof-ergonomics examples' imports. The
// library, the reference's examples and the HoTT automation examples resolve
// by the CLI's contract (web/module-resolution.mjs): an example from its own
// directory first, then the library, then the archive.
const archive = name => text(`archive/first-library/${cubicalSourceFile(name)}`);
const exampleReader = path => sourceReader({ path: fileURLToPath(new URL(path, root)) });
const unlimited = Object.fromEntries(["visits", "candidates", "rewrites", "premises", "nodes", "queries"].map(kind => [kind, Infinity]));
const kinds = Object.keys(unlimited);

// One workload: a source, checked in a new kernel with its imports, and every
// declaration's fuel read back.
async function measure(name, source, readSource) {
  const program = new CubicalProgram(await createCubical(), readSource,
    { collectReferences: false, searchFuel: unlimited, declarationFuel: { queries: Infinity } });
  const started = performance.now(), before = program.kernel.work();
  try {
    const result = await program.check(source, name);
    const after = program.kernel.work();
    const declarations = [...result.imports, ...result.outputs];
    const most = Object.fromEntries(kinds.map(kind => [kind, { spent: 0, declaration: null }]));
    let searches = 0, queries = { spent: 0, declaration: null };
    // Declarations, and directives: evaluate, and simp_rule and simp_set,
    // whose registration searches each rule's pattern.
    const spenders = [...declarations.map(d => ({ name: d.binding, fuel: d.searchFuel })),
      ...(result.directiveFuel ?? []).map(d => ({ name: `${d.module}: ${d.kind} ${d.name}`, fuel: d.searchFuel }))];
    for (const { name: spender, fuel } of spenders) {
      if (!fuel) continue;
      searches += fuel.searches;
      for (const kind of kinds) if (fuel.most[kind] > most[kind].spent) most[kind] = { spent: fuel.most[kind], declaration: spender };
      if (fuel.queries > queries.spent) queries = { spent: fuel.queries, declaration: spender };
    }
    return { name, declarations: declarations.length, checked: declarations.filter(d => d.verified).length,
      gaps: result.gaps.length, searches, most, declarationQueries: queries,
      seconds: Number(((performance.now() - started) / 1000).toFixed(1)),
      kernelSteps: after.instructionSteps + after.querySteps - before.instructionSteps - before.querySteps };
  } finally { program.dispose(); }
}

const workloads = [];
const modules = archiveModules;
workloads.push(await measure("archive", modules.map(module => `import ${module};`).join("\n"), archive));
const rebuilt = (await readdir(new URL("library/", root))).filter(file => file.endsWith(".cubist")).map(file => file.slice(0, -7));
workloads.push(await measure("library", rebuilt.map(module => `import ${module};`).join("\n"), sourceReader()));
const examples = [
  ...["conversion-laws", "cubical-probes", "canonicity"].map(file => `docs/examples/hott-automation/${file}.cubist`)
    .map(path => [path, exampleReader(path)]),
  ...(await readdir(new URL("docs/examples/proof-ergonomics/implemented/", root))).map(file => `docs/examples/proof-ergonomics/implemented/${file}`)
    .map(path => [path, archive]),
  ...(await readdir(new URL("docs/examples/proof-ergonomics/current/", root))).filter(file => file.endsWith(".cubist"))
    .map(file => [`docs/examples/proof-ergonomics/current/${file}`, archive]),
];
for (const [path, readSource] of examples) workloads.push(await measure(path, await text(path), readSource));
// The reference's checked examples, accepted and rejected: a rejected one's
// search must still stop with the error it states, not for want of fuel.
const pages = ["language.html", ...(await readdir(new URL("web/reference/", root))).filter(name => name.endsWith(".html"))
  .map(name => `reference/${name}`)];
const reference = { name: "reference examples", declarations: 0, checked: 0, gaps: 0, searches: 0, seconds: 0, kernelSteps: 0,
  most: Object.fromEntries(kinds.map(kind => [kind, { spent: 0, declaration: null }])), declarationQueries: { spent: 0, declaration: null } };
for (const page of pages) {
  for (const { attrs, text: source, label } of referenceExamples(page, await text(`web/${page}`))) {
    if (!["accept", "reject"].includes(attrs["data-check"])) continue;
    let measured;
    try { measured = await measure(label, source, sourceReader()); } catch { continue; }
    for (const key of ["declarations", "checked", "gaps", "searches", "seconds", "kernelSteps"]) reference[key] += measured[key];
    for (const kind of kinds) if (measured.most[kind].spent > reference.most[kind].spent) reference.most[kind] = { ...measured.most[kind], declaration: `${label} ${measured.most[kind].declaration}` };
    if (measured.declarationQueries.spent > reference.declarationQueries.spent)
      reference.declarationQueries = { ...measured.declarationQueries, declaration: `${label} ${measured.declarationQueries.declaration}` };
  }
}
reference.seconds = Number(reference.seconds.toFixed(1));
workloads.push(reference);

// Each default is four times the most any search spent, rounded up to 1, 2
// or 5 times a power of ten; the declaration's limit on queries likewise. A
// kind with a bound of its own inside one search is at least four times that
// bound, so the bound, not the fuel, still decides: a simplification stops
// premise search after 64 attempts, and makes at most 64 rewrites.
const floors = { premises: 64, rewrites: 64 };
const nice = n => { const scale = 10 ** Math.floor(Math.log10(Math.max(n, 1))); return [1, 2, 5, 10].map(f => f * scale).find(v => v >= n); };
const most = Object.fromEntries(kinds.map(kind => {
  const top = workloads.map(w => ({ workload: w.name, ...w.most[kind] })).sort((a, b) => b.spent - a.spent)[0];
  return [kind, top];
}));
const declarationQueries = workloads.map(w => ({ workload: w.name, ...w.declarationQueries })).sort((a, b) => b.spent - a.spent)[0];
const defaults = { search: Object.fromEntries(kinds.map(kind => [kind, nice(4 * Math.max(most[kind].spent, floors[kind] ?? 0))])),
  declaration: { queries: nice(4 * declarationQueries.spent) } };

const git = args => { try { return execFileSync("git", args, { encoding: "utf8" }).trim(); } catch { return null; } };
const report = {
  version: 1, generatedAt: new Date().toISOString(),
  revision: git(["rev-parse", "HEAD"]), modified: git(["status", "--porcelain", "--untracked-files=no"]) !== "",
  machine: { node: process.version, platform: `${os.platform()} ${os.arch()}`, cpu: os.cpus()[0]?.model ?? null },
  method: "Each workload is checked in a new kernel with its imports, references off and declaration transactions on, "
    + "with every search's fuel unlimited. A search's spending is read from the record of its declaration or directive "
    + "(evaluate, simp_rule, simp_set): how many searches ran and the most any one spent of each kind; a declaration's "
    + "queries include its searches', its closing check and its admission. Fuel counts are deterministic; "
    + "seconds, kernel steps and peak memory are one run's observations on this machine.",
  rule: "Each default is four times the most any search spent, rounded up to 1, 2 or 5 times a power of ten; "
    + "for a kind with its own bound inside one search, at least four times that bound.",
  floors,
  peakRssMiB: Math.round(process.resourceUsage().maxRSS / 1024),
  workloads, most, declarationQueries, defaults,
};
console.log(JSON.stringify({ most, declarationQueries, defaults }, null, 2));
for (const w of workloads) console.log(`${w.name}: ${w.checked}/${w.declarations} declarations, ${w.gaps} gaps, ${w.searches} searches, ${w.seconds} s`);
if (process.argv.includes("--write"))
  await writeFile(new URL("tests/fixtures/search-fuel.json", root), JSON.stringify(report, null, 2) + "\n");
