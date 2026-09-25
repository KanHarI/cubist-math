#!/usr/bin/env node
// Source is elaborated by JavaScript; all accepted judgements come from C/WASM.
import { readFile, writeFile } from "node:fs/promises";
import { basename, resolve, dirname, join } from "node:path";
import { createInterface } from "node:readline/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { cubicalText } from "../web/cubical-notation.mjs";
import { kernelAssembly, assemblyText } from "../web/cubical-assembly.mjs";
import { reduceView } from "../web/cubical-reduction.mjs";
const help = `Cubist Math — cubical C kernel
  check MODULE|FILE.cubist  Check source and imports
  inspect NAME             Show a checked expression, context, type and assumptions
  evaluate EXPRESSION      Normalize a closed expression that uses no assumption
  assembly NAME            Show the native kernel opcode graph
  beta [expression|type]   Perform one checked beta reduction
  delta [expression|type]  Unfold one named definition, checked by C
  export FILE.json         Save a replayable source inspection
  help                     Show this reference
  quit                     Exit

Noninteractive: node cli/repl.mjs check euclid
Optimizations: --[no-]share-syntax, --[no-]reuse-checks, --[no-]compact-paths`;
const args = process.argv.slice(2), optimizations = {};
const command = [];
for (const arg of args) {
  const match = arg.match(/^--(no-)?(share-syntax|reuse-checks|compact-paths)$/);
  if (match) optimizations[{ "share-syntax": "shareSyntax", "reuse-checks": "reuseChecks", "compact-paths": "compactPaths" }[match[2]]] = !match[1];
  else command.push(arg);
}
const module = await createCubical();
let program, view, binding, checkedModule, evaluations = 0;
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
function show() {
  const shown = view.folded ?? view;
  for (const entry of shown.context) console.log(`${entry.label ?? entry.name} : ${cubicalText(entry.type, view.symbols)}`);
  console.log(`${view.name}\nExpression: ${cubicalText(shown.reference ?? shown.expression, view.symbols)}\nType: ${cubicalText(shown.type, view.symbols)}`);
}
async function execute(line) {
  const [operation, ...parts] = line.trim().split(/\s+/), value = parts.join(" ");
  if (!operation) return;
  if (["help", "--help", "-h"].includes(operation)) { console.log(help); return; }
  if (["quit", "exit"].includes(operation)) return false;
  if (operation === "check") {
    if (!value) throw Error("check requires a module or .cubist file.");
    const source = value.endsWith(".cubist") ? await readFile(resolve(value), "utf8") : await readSource(value);
    const main = basename(value, ".cubist");
    program?.dispose(); view = null; binding = null;
    const localDirectory = value.endsWith(".cubist") ? dirname(resolve(value)) : null;
    const imports = async name => {
      if (localDirectory) {
        try { return await readFile(join(localDirectory, `${name}.cubist`), "utf8"); }
        catch (error) { if (error.code !== "ENOENT") throw error; }
      }
      return readSource(name);
    };
    program = new CubicalProgram(module, imports, { optimizations });
    const result = await program.check(source, main);
    if (!result.complete) throw Error(JSON.stringify(result.gaps, null, 2));
    checkedModule = main;
    console.log(`Checked ${result.outputs.length} declarations · ${result.instructionCount.toLocaleString()} kernel steps`);
    for (const evaluation of result.evaluations ?? [])
      console.log(`evaluate ${evaluation.name}${evaluation.module === main ? "" : ` (${evaluation.module})`}: ${evaluation.value}`);
    return;
  }
  if (!program) throw Error("Check a source first.");
  if (operation === "evaluate") {
    if (!value) throw Error("evaluate requires an expression.");
    // The checked module is cached, so this checks only the directive. Both
    // sides are the same term, so the directive reports its normal form.
    const scratch = `evaluate_${++evaluations}`;
    const result = await program.check(`import ${checkedModule};\nevaluate ${value} expecting ${value};`, scratch);
    const gap = program.gaps.find(item => item.module === scratch);
    if (gap) throw Error(gap.reason);
    console.log(result.evaluations.find(item => item.module === scratch).value);
    return;
  }
  if (["inspect", "assembly"].includes(operation)) {
    const matches = Object.values(program.symbols).filter(item => item.name === value);
    if (matches.length > 1) throw Error(`Ambiguous name; use a qualified binding: ${matches.map(item => item.binding).join(", ")}`);
    binding = matches[0]?.binding ?? value;
    view = program.inspect(binding);
    if (operation === "inspect") {
      show();
      const assumptions = program.symbols[binding]?.axioms;
      if (assumptions) console.log(`Assumptions: ${[...new Set(assumptions.map(name =>
        program.checker.assumptionLabels.get(name) ?? name))].sort().join(", ") || "none"}`);
    }
    else {
      const checked = program.checker.syntax.check(view.expression, view.type, view.context.map(e => [e.name, e.type]), new Map(view.dimensions ?? []));
      console.log(assemblyText(kernelAssembly(program, view, checked)));
    }
    return;
  }
  if (!view) throw Error("Inspect a checked name first.");
  if (["beta", "delta"].includes(operation)) {
    const side = value || "expression";
    if (!["expression", "type"].includes(side)) throw Error("Choose expression or type.");
    const reduced = reduceView(program, view, side, operation);
    if (reduced.change) { view = reduced.view; view.folded = null; show(); }
    else console.log("No applicable reduction.");
  } else if (operation === "export") {
    if (!value) throw Error("export requires a filename.");
    await writeFile(value, JSON.stringify(program.export(binding, "expression"), null, 2) + "\n");
  } else throw Error(`Unknown command ${operation}. Type help.`);
}
try {
  if (command.length) await execute(command.join(" "));
  else {
    console.log(help);
    const input = createInterface({ input: process.stdin, output: process.stdout, terminal: process.stdin.isTTY });
    try {
      for await (const line of input) {
        try { if (await execute(line) === false) break; }
        catch (error) { console.error(error.message); }
      }
    } finally { input.close(); }
  }
} catch (error) { console.error(error.message); process.exitCode = 1; }
finally { program?.dispose(); }
