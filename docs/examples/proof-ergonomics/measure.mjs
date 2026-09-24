// Planning baseline: one observation, not a performance comparison.
// Run from any directory; the existing C/WASM runtime must be built.
import { readFile, writeFile } from "node:fs/promises";
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { cpus } from "node:os";
import { fileURLToPath } from "node:url";
import { parse, tokenize } from "../../../web/mathscript/parser.mjs";
import { benchmark } from "../../../web/benchmark-runner.mjs";

const root = new URL("../../../", import.meta.url);
const selection = [
  ["primes", "nat_add_assoc"],
  ["paths", "right_unit"],
  ["finite_dependent_counts", "finite_uniform_fiber_count"],
  ["group_operations", "group_conjugate_multiply"],
  ["field_vector_spaces", "field_scalar_laws"],
];
const readSource = name => readFile(new URL(`web/proofs/${name}.cubist`, root), "utf8");
const report = await benchmark({ modules: selection.map(([module]) => module),
  limitMs: 1000, readSource });
if (report.importErrors.length || report.counts.failed || report.counts.blocked || report.counts.optimize)
  throw new Error(`Baseline did not fully check: ${JSON.stringify(report.counts)}`);

const selected = await Promise.all(selection.map(async ([module, name]) => {
  const source = await readSource(module);
  const declaration = parse(source).declarations.find(d => d.name.text === name);
  if (!declaration) throw new Error(`Missing baseline declaration ${module}.${name}`);
  const row = report.declarations.find(d => d.module === module && d.name === name);
  if (row?.category !== "checked") throw new Error(`Unchecked baseline ${module}.${name}`);
  const text = source.slice(declaration.start, declaration.end);
  return { module, name, sourcePath: `web/proofs/${module}.cubist`,
    sourceSha256: createHash("sha256").update(source).digest("hex"),
    declarationSha256: createHash("sha256").update(text).digest("hex"),
    sourceTokens: tokenize(text).length - 1,
    sourceLines: text.split("\n").length, observation: row };
}));

const snapshot = {
  version: 2, generatedAt: report.generatedAt,
  revision: execFileSync("git", ["rev-parse", "HEAD"], { cwd: fileURLToPath(root), encoding: "utf8" }).trim(),
  dirty: !!execFileSync("git", ["status", "--porcelain"], { cwd: fileURLToPath(root), encoding: "utf8" }).trim(),
  runtime: process.version, cpu: cpus()[0]?.model,
  method: "One selected import graph in source order with imports checked once, references disabled, no normalization request, native declaration transactions. Elapsed times include elaboration and checking, exclude import parsing, and are a single observation, not a statistical baseline or speedup claim. Native checking steps count every checker query during each declaration. Arena nodes/bytes snapshot the kernel at the final check, including earlier retained terms; they are not a per-declaration delta or peak. Tokens exclude comments, whitespace and EOF.",
  unmeasured: ["aggregate reduction steps", "peak temporary arena", "retained arena delta", "generated proof DAG size", "rewrite candidate visits", "repeated explicit parameter count", "repeated-run variance"],
  limitMs: report.limitMs, optimizations: report.optimizations,
  graph: { modules: report.modules, counts: report.counts, elapsedSeconds: report.elapsedSeconds },
  selected,
};
const destination = new URL("./baseline.json", import.meta.url);
await writeFile(destination, JSON.stringify(snapshot, null, 2) + "\n");
console.log(`Wrote ${fileURLToPath(destination)}; ${report.counts.checked} checked declarations, ${report.counts.template} templates.`);
