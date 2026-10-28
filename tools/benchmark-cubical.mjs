// Temporary migration benchmark. Each source declaration gets one shared
// wall deadline for elaboration and the instruction kernel's derivations,
// excluding import discovery.
import { readFile, writeFile, mkdir } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import { cpus } from "node:os";
import { pathToFileURL, fileURLToPath } from "node:url";
import { createHash } from "node:crypto";
import { benchmark, benchmarkAreas } from "../web/benchmark-runner.mjs";
import { savedReport } from "../web/benchmark-areas.mjs";
import { sourceReader } from "./module-sources.mjs";
import { moduleRoots } from "../web/module-resolution.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";

// A file's bytes at a revision, or null where it has none.
export function committedSource(revision, path, cwd = fileURLToPath(new URL("../", import.meta.url))) {
  try { return execFileSync("git", ["show", `${revision}:${path}`], { cwd, maxBuffer: 1 << 28, stdio: ["ignore", "pipe", "ignore"] }); }
  catch { return null; }
}
// The sources a saved report's rows link to (web/benchmark-areas.mjs's
// declarationLink): each measured module whose text, as UTF-8, is its file's
// bytes at the recorded revision, with its path and their SHA-256. A module
// measured from working changes, edited or not yet committed, is left out,
// and its rows are not linked: a link pins the source as it was at the
// revision, which is not what was measured. So is a file that is not valid
// UTF-8: its text was decoded with replacement characters, which other bytes
// decode to as well, and encodes to no committed file's bytes.
export function pinnedSources(measured, committed) {
  return Object.fromEntries(measured.flatMap(({ name, path, text }) => {
    const bytes = Buffer.from(text, "utf8"), file = committed(path);
    return file && bytes.equals(file) ? [[name, { path, sha256: createHash("sha256").update(bytes).digest("hex") }]] : [];
  }));
}


if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  assertFreshBuild();
  const args = process.argv.slice(2), selected = args.filter(a => !a.startsWith("--"));
  const limitArg = args.find(a => a.startsWith("--limit-ms="));
  const limitMs = limitArg ? Number(limitArg.slice("--limit-ms=".length)) : 100;
  // The area measured: library, archive (the default) or tests.
  const areaArg = args.find(a => a.startsWith("--area="));
  const area = areaArg ? areaArg.slice("--area=".length) : "archive";
  if (!Object.hasOwn(benchmarkAreas, area)) throw Error(`--area is library, archive or tests, not ${area}.`);
  const optimizations = { shareSyntax: !args.includes("--no-share-syntax"),
    reuseChecks: !args.includes("--no-reuse-checks"), compactPaths: !args.includes("--no-compact-paths") };
  const known = /^(--verbose|--publish|--limit-ms=.+|--area=.+|--no-share-syntax|--no-reuse-checks|--no-compact-paths)$/;
  for (const arg of args) if (arg.startsWith("--") && !known.test(arg)) throw Error(`Unknown option: ${arg}`);
  const output = new URL(`../web/${savedReport(area)}`, import.meta.url);
  const verbose = args.includes("--verbose");
  const revision = execFileSync("git", ["rev-parse", "HEAD"], { encoding: "utf8" }).trim();
  const dirty = !!execFileSync("git", ["status", "--porcelain"], { encoding: "utf8" }).trim();
  // The benchmark's check imports as a module of the area does. Each text it
  // reads is kept, to compare with the file at the revision.
  const reader = sourceReader(), texts = new Map();
  reader.place("benchmark", area);
  const readSource = Object.assign(async (name, importer) => {
    const text = await reader(name, importer);
    texts.set(name, text);
    return text;
  }, reader);
  const report = await benchmark({ area, limitMs, optimizations, ...(selected.length ? { modules: selected } : {}),
    readSource,
    onResult: row => {
      if (verbose || row.category === "optimize" || row.category === "failed")
        console.log(`${row.category.padEnd(8)} ${row.elapsedMs.toFixed(1)}ms ${row.module}.${row.name}${row.reason ? ` — ${row.reason}` : ""}`);
    },
  });
  const sources = pinnedSources([...new Set(report.declarations.map(row => row.module))].sort()
    .map(name => ({ name, path: `${moduleRoots[reader.placeOf(name)]}${name}.cubist`, text: texts.get(name) })),
  path => committedSource(revision, path));
  Object.assign(report, { revision, dirty, sources, runtime: process.version, cpu: cpus()[0]?.model,
    complete: true, method: "One session; source order with imports checked once. Each declaration is elaborated with every check derived by the instruction kernel as it runs, and admitted by Define, within its deadline. Warm dependencies; transient arena terms and judgements compacted between declarations; no normalization request. Deadline polled cooperatively in JS and C." });
  await mkdir(new URL("../build/", import.meta.url), { recursive: true });
  await writeFile(new URL(`../build/cubical-benchmark${area === "archive" ? "" : `-${area}`}.json`, import.meta.url), JSON.stringify(report, null, 2) + "\n");
  if (!selected.length || args.includes("--publish")) {
    let previous = null;
    try { previous = JSON.parse(await readFile(output, "utf8")); } catch {}
    report.baseline = previous?.baseline ?? (previous?.complete ? { area, generatedAt: previous.generatedAt, counts: previous.counts, limitMs: previous.limitMs, optimizations: previous.optimizations } : null);
    await writeFile(output, JSON.stringify(report, null, 2) + "\n");
  }
  console.log(JSON.stringify({ ...report, declarations: report.declarations.length }, null, 2));
}
