#!/usr/bin/env node
// How much of the archive derives in instruction mode. The archive is checked
// once, every check derived by the instruction kernel; then every definition's
// value is derived again by a fresh instruction driver at its type, with a
// time limit per definition. Writes build/instruction-coverage.json and prints a summary.
//   node tools/instruction-coverage.mjs [--limit-ms=5000]
import { readFile, writeFile, mkdir } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { sourceModules, cubicalSourceModules } from "../web/mathscript/modules.mjs";
import { cubicalSourceFile } from "../web/cubical-sources.mjs";

const limitArg = process.argv.find(arg => arg.startsWith("--limit-ms="));
const limitMs = limitArg ? Number(limitArg.slice("--limit-ms=".length)) : 5000;
const readSource = name => readFile(new URL(`../archive/first-library/${cubicalSourceFile(name)}`, import.meta.url), "utf8");
const program = new CubicalProgram(await createCubical(), readSource);
const modules = [...new Set([...sourceModules, ...cubicalSourceModules])];
await program.check(modules.map(name => `import ${name};`).join("\n"), "coverage");
const kernel = program.kernel, failures = {}, times = [];
for (const [name, reference] of kernel.definitions) {
  const { value, type } = kernel.definition(reference);
  const started = performance.now();
  kernel.setDeadline(limitMs);
  try {
    new InstructionDriver(kernel).check(value, type);
    times.push([performance.now() - started, name]);
  } catch (error) {
    const reason = error.message.replace(/: .*/, "");
    (failures[reason] ??= []).push(name);
  } finally { kernel.setDeadline(); }
}
program.dispose();
times.sort((a, b) => b[0] - a[0]);
const report = { definitions: kernel.definitions.size, derived: times.length, limitMs,
  seconds: Number((times.reduce((sum, [ms]) => sum + ms, 0) / 1000).toFixed(1)),
  slowest: times.slice(0, 10).map(([ms, name]) => ({ name, ms: Math.round(ms) })),
  failures: Object.fromEntries(Object.entries(failures).sort((a, b) => b[1].length - a[1].length)) };
await mkdir(new URL("../build/", import.meta.url), { recursive: true });
await writeFile(new URL("../build/instruction-coverage.json", import.meta.url), JSON.stringify(report, null, 2) + "\n");
console.log(`${report.derived} of ${report.definitions} definitions derive in instruction mode `
  + `(${(100 * report.derived / report.definitions).toFixed(1)}%), in ${report.seconds} s.`);
for (const [reason, names] of Object.entries(report.failures)) console.log(`${String(names.length).padStart(5)}  ${reason}  (${names.slice(0, 2).join(", ")})`);
