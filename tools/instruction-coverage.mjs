#!/usr/bin/env node
// How much of the archive derives in instruction mode, and what it costs.
// The archive is checked once, every check derived by the instruction kernel;
// then every definition's value is derived again by a fresh instruction
// driver at its type, with a time limit per definition. Writes a report,
// build/instruction-coverage.json unless --report names another file, and
// prints a summary.
//   node tools/instruction-coverage.mjs [--limit-ms=5000] [--oracle]
//        [--trajectories=FILE] [--select=REGEX] [--modules=a,b] [--report=FILE]
// The driver steers by its own guide; with --oracle, by the term checker's
// conversion instead, for comparison. --trajectories writes one JSON line per
// re-derived definition with every branch point of its search
// (tools/search-telemetry.mjs); --select re-derives only the definitions
// whose names match; --modules checks only those archive modules and their
// imports, instead of all of them.
//
// Cost is kernel work (CubicalKernel.work): instructions and queries, their
// steps of budget, and their failures, rejected instructions and the guide's
// queries included. Search counts are the driver's branch points and the
// outcomes of its moves. Times are one run's observations on this machine.
//
// The command succeeds when every import checks, there are no gaps, and
// every stored definition derives again; otherwise its exit status is 1.
import { readFile, writeFile, mkdir } from "node:fs/promises";
import { createWriteStream } from "node:fs";
import { execFileSync } from "node:child_process";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import os from "node:os";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionDriver, heuristicChooser, searchLimits } from "../web/cubical-instruction-driver.mjs";
import { sourceModules, cubicalSourceModules } from "../web/mathscript/modules.mjs";
import { cubicalSourceFile } from "../web/cubical-sources.mjs";
import { addWork, countingChooser, kernelSteps, recordingChooser, workSince } from "./search-telemetry.mjs";

const option = name => process.argv.find(arg => arg.startsWith(`--${name}=`))?.slice(name.length + 3);
const limitMs = option("limit-ms") ? Number(option("limit-ms")) : 5000;
const oracle = process.argv.includes("--oracle");
const trajectoryFile = option("trajectories");
const select = option("select") ? new RegExp(option("select")) : null;
const known = /^--(limit-ms|trajectories|select|modules|report)=|^--oracle$/;
const unknown = process.argv.slice(2).find(arg => !known.test(arg));
if (unknown) throw new Error(`Unknown option: ${unknown}`);

const projectRoot = fileURLToPath(new URL("../", import.meta.url));
const git = args => { try { return execFileSync("git", args, { cwd: projectRoot, encoding: "utf8" }).trim(); } catch { return null; } };
const environment = {
  revision: git(["rev-parse", "HEAD"]), modified: git(["status", "--porcelain", "--untracked-files=no"]) !== "",
  node: process.version, platform: `${os.platform()} ${os.arch()}`, cpu: os.cpus()[0]?.model ?? null,
  cpus: os.cpus().length, memoryGiB: Math.round(os.totalmem() / 2 ** 30),
};

const readSource = name => readFile(new URL(`../archive/first-library/${cubicalSourceFile(name)}`, import.meta.url), "utf8");
const program = new CubicalProgram(await createCubical(), readSource);
const kernel = program.kernel;
kernel.conversionOracle = oracle;
// The archive check shares one driver across declarations, the elaborator's.
const checkChooser = countingChooser(heuristicChooser);
kernel.chooser = checkChooser;
const modules = option("modules")?.split(",") ?? [...new Set([...sourceModules, ...cubicalSourceModules])];
const checkStarted = performance.now(), checkWork = kernel.work();
const checked = await program.check(modules.map(name => `import ${name};`).join("\n"), "coverage");
const check = { seconds: Number(((performance.now() - checkStarted) / 1000).toFixed(1)),
  work: workSince(checkWork, kernel.work()), search: checkChooser.counts };
const budgets = { limitMs, stepBudget: Number(kernel.stepBudget), ...searchLimits };

// Every definition again, each by a fresh driver on the checked session: the
// kernel's caches are warm, the driver's are empty.
const trajectories = trajectoryFile ? createWriteStream(trajectoryFile) : null;
const failures = {}, derivations = [], total = {}, search = countingChooser(heuristicChooser);
for (const [name, reference] of kernel.definitions) {
  if (select && !select.test(name)) continue;
  const { value, type } = kernel.definition(reference);
  const points = [];
  const chooser = trajectories ? recordingChooser(search, kernel, point => points.push(point)) : search;
  const before = kernel.work(), started = performance.now();
  let outcome = "derived";
  kernel.setDeadline(limitMs);
  try {
    new InstructionDriver(kernel, { chooser }).check(value, type);
  } catch (error) {
    outcome = error.message.replace(/: .*/, "");
    (failures[outcome] ??= []).push(name);
  } finally { kernel.setDeadline(); }
  const ms = performance.now() - started, work = workSince(before, kernel.work());
  addWork(total, work);
  derivations.push({ name, ms, steps: kernelSteps(work), derived: outcome === "derived", outcome, work });
  trajectories?.write(JSON.stringify({ definition: name, outcome, ms: Math.round(ms), work, points }) + "\n");
}
if (trajectories) await new Promise(resolve => trajectories.end(resolve));
const arena = kernel.arena();
program.dispose();

const imports = checked.imports ?? [];
const gaps = (checked.gaps ?? []).map(({ module, name, reason }) => ({ module, name, reason: reason?.replace(/: [^]*/, "") }));
const derived = derivations.filter(d => d.derived);
const definitions = select ? derivations.length : kernel.definitions.size;
const top = (key, format) => [...derived].sort((a, b) => b[key] - a[key]).slice(0, 10).map(format);
const report = {
  environment, budgets, oracle, chooser: search.name,
  session: "The archive is checked in one kernel session, whose elaborator keeps one driver; then each stored "
    + "definition is derived again by a fresh driver on that session, with the kernel's caches warm.",
  checked: { modules: modules.length, declarations: imports.length, verified: imports.filter(d => d.verified).length,
    gaps, ...check },
  definitions, derived: derived.length, selected: select?.source ?? null,
  seconds: Number((derivations.reduce((sum, d) => sum + d.ms, 0) / 1000).toFixed(1)),
  work: total, search: search.counts,
  memory: { peakRssMiB: Math.round(process.resourceUsage().maxRSS / 1024), arenaNodes: arena.nodes, arenaMiB: Math.round(arena.bytes / 2 ** 20) },
  // Every definition derived again, failed ones included, as rows of `fields`.
  perDefinition: { fields: ["name", "outcome", "ms", "instructions", "rejected", "instructionSteps", "queries", "failedQueries",
    "querySteps", "exhausted", "deadlines"],
    rows: derivations.map(d => [d.name, d.outcome, Number(d.ms.toFixed(1)), d.work.instructions, d.work.rejected,
      d.work.instructionSteps, d.work.queries, d.work.failedQueries, d.work.querySteps, d.work.exhausted, d.work.deadlines]) },
  slowest: top("ms", d => ({ name: d.name, ms: Math.round(d.ms) })),
  costliest: top("steps", d => ({ name: d.name, steps: d.steps })),
  failures: Object.fromEntries(Object.entries(failures).sort((a, b) => b[1].length - a[1].length)),
};
report.success = imports.length > 0 && report.checked.verified === imports.length && !gaps.length
  && definitions > 0 && report.derived === definitions;
const reportFile = resolve(option("report") ?? fileURLToPath(new URL("../build/instruction-coverage.json", import.meta.url)));
await mkdir(dirname(reportFile), { recursive: true });
await writeFile(reportFile, JSON.stringify(report, null, 2) + "\n");

const count = n => n.toLocaleString("en-US");
console.log(`Archive checked ${oracle ? "with the conversion oracle" : "with the driver's guide"} in ${check.seconds} s: `
  + `${count(report.checked.verified)} of ${count(imports.length)} declarations in ${modules.length} module${modules.length === 1 ? "" : "s"}, `
  + `${gaps.length} gap${gaps.length === 1 ? "" : "s"}; `
  + `kernel work ${count(check.work.instructions)} instructions, ${count(kernelSteps(check.work))} steps.`);
for (const gap of gaps) console.log(`  gap  ${gap.module}.${gap.name ?? "?"}: ${gap.reason}`);
console.log(`${count(report.derived)} of ${count(definitions)} definitions derive in instruction mode `
  + `(${(100 * report.derived / Math.max(definitions, 1)).toFixed(1)}%), in ${report.seconds} s; `
  + `kernel work ${count(total.instructions ?? 0)} instructions (${count(total.rejected ?? 0)} rejected), `
  + `${count(total.queries ?? 0)} queries, ${count(kernelSteps({ instructionSteps: 0, querySteps: 0, ...total }))} steps; `
  + `${count(search.counts.points)} branch points.`);
for (const [reason, names] of Object.entries(report.failures)) console.log(`${String(names.length).padStart(5)}  ${reason}  (${names.slice(0, 2).join(", ")})`);
console.log(report.success ? "Coverage complete." : "Coverage incomplete: see above.");
if (trajectoryFile) console.log(`Trajectories written to ${trajectoryFile}.`);
if (!report.success) process.exitCode = 1;
