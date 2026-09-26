#!/usr/bin/env node
// Source is elaborated by JavaScript; all accepted judgements come from C/WASM.
import { readFile, readdir, writeFile } from "node:fs/promises";
import { basename, resolve, dirname, join } from "node:path";
import { createInterface } from "node:readline/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { cubicalText } from "../web/cubical-notation.mjs";
import { kernelAssembly, assemblyText } from "../web/cubical-assembly.mjs";
import { reduceView } from "../web/cubical-reduction.mjs";
import { ReplSession, replStatements } from "../web/repl-session.mjs";
const help = `Cubist Math — cubical C kernel
  let NAME := TERM;        Define a name; def and any other declaration work too
  typeof TERM;             Show the type of a term
  evaluate TERM;           Show the value of a closed term that uses no assumption
  import MODULE;           Load a module into the session
  /modules [TEXT]          List the modules import can load, or those whose names contain TEXT
  /clear                   Clear the terminal
  /restart                 Start a new session: forget every name defined here
  check MODULE|FILE.cubist  Check source and imports; later entries see its names
  inspect NAME             Show a checked expression, context, type and assumptions
  assembly NAME            Show the native kernel opcode graph
  beta [expression|type]   Perform one checked beta reduction
  delta [expression|type]  Unfold one named definition, checked by C
  export FILE.json         Save a replayable source inspection
  help                     Show this reference
  quit                     Exit

Each entry is checked by the kernel as a small module on top of the ones
before it. An entry continues on the next line while a bracket is open.

Noninteractive: node cli/repl.mjs check euclid
                node cli/repl.mjs "import naturals; evaluate 2 + 3;"
Optimizations: --[no-]share-syntax, --[no-]reuse-checks, --[no-]compact-paths`;
const args = process.argv.slice(2), optimizations = {};
const command = [];
for (const arg of args) {
  const match = arg.match(/^--(no-)?(share-syntax|reuse-checks|compact-paths)$/);
  if (match) optimizations[{ "share-syntax": "shareSyntax", "reuse-checks": "reuseChecks", "compact-paths": "compactPaths" }[match[2]]] = !match[1];
  else command.push(arg);
}
const module = await createCubical();
let program, view, binding, checkedModule, session = null, sessionProgram = null;
// The rebuilt library comes first; the archived first library is the fallback.
const readSource = async name => {
  for (const root of ["../library/", "../archive/first-library/"]) {
    try { return await readFile(new URL(`${root}${name}.cubist`, import.meta.url), "utf8"); }
    catch (error) { if (error.code !== "ENOENT") throw error; }
  }
  throw Error(`No module named ${name} in library/ or archive/first-library/.`);
};
// What import can load, for the REPL's /modules.
const importable = async () => {
  const names = async root => (await readdir(new URL(root, import.meta.url)).catch(() => []))
    .filter(file => file.endsWith(".cubist")).map(file => file.slice(0, -".cubist".length));
  return { library: await names("../library/"), archive: await names("../archive/first-library/") };
};
function show() {
  const shown = view.folded ?? view;
  for (const entry of shown.context) console.log(`${entry.label ?? entry.name} : ${cubicalText(entry.type, view.symbols)}`);
  console.log(`${view.name}\nExpression: ${cubicalText(shown.reference ?? shown.expression, view.symbols)}\nType: ${cubicalText(shown.type, view.symbols)}`);
}
// Entries run in a session over the checked module, or over an empty program
// before any check. A new check keeps the session: its entries are replayed.
async function replSession() {
  if (program && session?.program !== program)
    session = session ? await session.rebase(program, checkedModule) : new ReplSession(program, { base: checkedModule, modules: importable });
  else if (!session) {
    sessionProgram = new CubicalProgram(module, readSource, { optimizations });
    session = new ReplSession(sessionProgram, { modules: importable });
  }
  return session;
}
const commands = new Set(["help", "--help", "-h", "quit", "exit", "check", "inspect", "assembly", "beta", "delta", "export"]);
async function execute(line) {
  const [operation, ...parts] = line.trim().split(/\s+/), value = parts.join(" ");
  if (!operation) return;
  if (line.trim().replace(/;$/, "") === "/help") { console.log(help); return; }
  if (line.trim().replace(/;$/, "") === "/clear") { console.clear(); return; }
  if (line.trim().replace(/;$/, "") === "/restart") {
    sessionProgram?.dispose();
    sessionProgram = null;
    session = null;
    console.log("Started a new session.");
    return;
  }
  if (!commands.has(operation)) {
    for (const { kind, text } of await (await replSession()).run(line))
      (kind === "error" ? console.error : console.log)(text);
    return;
  }
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
    const prompt = text => { if (process.stdin.isTTY) { input.setPrompt(text); input.prompt(); } };
    // An entry with an open bracket, such as a proof block, continues.
    let pending = "";
    prompt("cubist> ");
    try {
      for await (const line of input) {
        pending += (pending ? "\n" : "") + line;
        if (replStatements(pending).depth > 0) { prompt("...     "); continue; }
        const entry = pending;
        pending = "";
        try { if (await execute(entry) === false) break; }
        catch (error) { console.error(error.message); }
        prompt("cubist> ");
      }
    } finally { input.close(); }
  }
} catch (error) { console.error(error.message); process.exitCode = 1; }
finally { program?.dispose(); sessionProgram?.dispose(); }
