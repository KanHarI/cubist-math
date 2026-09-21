// Temporary migration benchmark. Each source declaration gets one shared
// wall deadline for elaboration and C checking, excluding import discovery.
import { readFile, writeFile, mkdir } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import { cpus } from "node:os";
import { pathToFileURL } from "node:url";
import { benchmark } from "../web/benchmark-runner.mjs";
import { cubicalSourceFile } from "../web/cubical-sources.mjs";


if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  const args = process.argv.slice(2), selected = args.filter(a => !a.startsWith("--"));
  const output = new URL("../web/benchmark-results.json", import.meta.url);
  const verbose = args.includes("--verbose");
  const revision = execFileSync("git", ["rev-parse", "HEAD"], { encoding: "utf8" }).trim();
  const dirty = !!execFileSync("git", ["status", "--porcelain"], { encoding: "utf8" }).trim();
  const report = await benchmark({ ...(selected.length ? { modules: selected } : {}),
    readSource: name => readFile(new URL(`../web/proofs/${cubicalSourceFile(name)}`, import.meta.url), "utf8"),
    onResult: row => {
      if (verbose || row.category === "optimize" || row.category === "failed")
        console.log(`${row.category.padEnd(8)} ${row.elapsedMs.toFixed(1)}ms ${row.module}.${row.name}${row.reason ? ` — ${row.reason}` : ""}`);
    },
  });
  Object.assign(report, { revision, dirty, runtime: process.version, cpu: cpus()[0]?.model,
    complete: true, method: "One session; source order with imports checked once. Warm dependencies; transient arena terms compacted between declarations; no normalization request. Deadline polled cooperatively in JS and C. Universe templates counted separately." });
  await mkdir(new URL("../build/", import.meta.url), { recursive: true });
  await writeFile(new URL("../build/cubical-benchmark.json", import.meta.url), JSON.stringify(report, null, 2) + "\n");
  if (!selected.length || args.includes("--publish")) {
    let previous = null;
    try { previous = JSON.parse(await readFile(output, "utf8")); } catch {}
    report.baseline = previous?.baseline ?? (previous?.complete ? { generatedAt: previous.generatedAt, counts: previous.counts } : null);
    await writeFile(output, JSON.stringify(report, null, 2) + "\n");
  }
  console.log(JSON.stringify({ ...report, declarations: report.declarations.length }, null, 2));
}
