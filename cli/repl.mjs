#!/usr/bin/env node
// Source is elaborated by JavaScript; all accepted judgements come from C/WASM.
import { readFile, readdir, writeFile } from "node:fs/promises";
import { basename, resolve } from "node:path";
import { createInterface } from "node:readline/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { cubicalText } from "../web/cubical-notation.mjs";
import { kernelAssembly, assemblyText } from "../web/cubical-assembly.mjs";
import { reduceView } from "../web/cubical-reduction.mjs";
import { ReplSession, replStatements } from "../web/repl-session.mjs";
import { moduleRoots } from "../web/module-resolution.mjs";
import { diagnosticLine, withCode } from "../web/diagnostics.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { assertFreshBuild } from "../tools/build-stamp.mjs";
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
                node cli/repl.mjs "import nat; evaluate 2 + 3;"
Optimizations: --[no-]share-syntax, --[no-]reuse-checks, --[no-]compact-paths
Declared types (H1, inductive) are on by default. Import nat for Nat and its
numerals, w for W(U,V,A,B), and pushout for Pushout.`;
const args = process.argv.slice(2), optimizations = {};
const command = [];
for (const arg of args) {
  const match = arg.match(/^--(no-)?(share-syntax|reuse-checks|compact-paths)$/);
  if (match) optimizations[{ "share-syntax": "shareSyntax", "reuse-checks": "reuseChecks", "compact-paths": "compactPaths" }[match[2]]] = !match[1];
  else if (/^--experimental(=|$)/.test(arg)) {
    console.error("--experimental was removed: declared types (H1) are on by default.");
    process.exit(2);
  }
  else if (/^--representation(=|$)/.test(arg)) {
    console.error("--representation was removed with the differential fixtures: Nat, W and pushouts are source declarations.");
    process.exit(2);
  }
  else command.push(arg);
}
// A stale WASM kernel would run code it does not contain.
assertFreshBuild();
// An error as the checker prints it: a failed check's lines as they are,
// any other message with its code in front.
const shown = error => error.lines ? error.message : withCode(error.message);
const module = await createCubical();
let program, view, binding, checkedModule, session = null, sessionProgram = null;
// Imports resolve as web/module-resolution.mjs specifies: an archive module
// imports only from the archive; anything else imports library-first, and a
// checked file outside both roots first imports from its own directory.
// What import can load, for the REPL's /modules.
const importable = async () => {
  const names = async root => (await readdir(new URL(`../${root}`, import.meta.url)).catch(() => []))
    .filter(file => file.endsWith(".cubist")).map(file => file.slice(0, -".cubist".length));
  return { library: await names(moduleRoots.library), archive: await names(moduleRoots.archive) };
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
    sessionProgram = new CubicalProgram(module, sourceReader(), { optimizations });
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
    // A file is checked where it lives; a module name is found library-first.
    const file = value.endsWith(".cubist"), imports = sourceReader(file ? { path: value } : {});
    const source = file ? await readFile(resolve(value), "utf8") : await imports(value);
    const main = basename(value, ".cubist");
    program?.dispose(); view = null; binding = null;
    program = new CubicalProgram(module, imports, { optimizations });
    const result = await program.check(source, main);
    // Each failure on a line of its own, with its code (web/diagnostics.mjs).
    if (!result.complete) throw Object.assign(Error(result.gaps.map(gap => diagnosticLine({ code: gap.code, message: gap.reason,
      declaration: gap.name && (gap.module === main ? gap.name : `${gap.module}.${gap.name}`) })).join("\n") || `${main} did not check.`), { lines: true });
    checkedModule = main;
    console.log(`Checked ${result.outputs.length} declarations · ${result.instructionCount.toLocaleString()} kernel steps`);
    for (const warning of result.warnings ?? [])
      console.log(diagnosticLine({ severity: "warning", ...warning }));
    for (const evaluation of result.evaluations ?? [])
      console.log(`evaluate ${evaluation.name}${evaluation.module === main ? "" : ` (${evaluation.module})`}: ${evaluation.value}`);
    for (const print of result.prints ?? [])
      console.log(`print ${print.name}${print.module === main ? "" : ` (${print.module})`}: ${print.text}`);
    return;
  }
  if (!program) throw Error("Check a source first.");
  if (["inspect", "assembly"].includes(operation)) {
    const matches = Object.values(program.symbols).filter(item => item.name === value);
    if (matches.length > 1) throw Error(`Ambiguous name; use a qualified binding: ${matches.map(item => item.binding).join(", ")}`);
    binding = matches[0]?.binding ?? value;
    const signature = operation === "inspect" && program.signatureView(binding);
    if (signature) {
      // A declared type: its signature in normal form, as the kernel admitted
      // it, and its eliminator's clause types for a motive P.
      console.log(`inductive ${signature.name} : ${signature.former} (${signature.modifier})`);
      if (signature.recorded.length) console.log(`Recorded universe parameters: ${signature.recorded.join(", ")}`);
      for (const c of signature.constructors)
        console.log(`  ${c.name} : ${c.type}  [${c.data} data, ${c.positions} position${c.positions === 1 ? "" : "s"}, `
          + `${c.dimensions} dimension${c.dimensions === 1 ? "" : "s"}${c.generated ? ", generated" : ""}]`);
      const eliminator = signature.eliminator;
      if (eliminator) {
        console.log(`Eliminator, for a motive ${eliminator.motive}:`);
        for (const clause of eliminator.clauses) console.log(`  ${clause.name} : ${clause.type}`);
        if (eliminator.error) console.log(`  The remaining clause types could not be computed: ${eliminator.error}`);
      }
      console.log(`Kernel extensions: ${signature.extensions.join(", ") || "none"}`);
      view = null;
      return;
    }
    view = program.inspect(binding);
    if (operation === "inspect") {
      show();
      const assumptions = program.symbols[binding]?.axioms;
      if (assumptions) console.log(`Assumptions: ${[...new Set(assumptions.map(name =>
        program.checker.assumptionLabels.get(name) ?? name))].sort().join(", ") || "none"}`);
      // Kernel extensions under review are listed apart: they are not assumptions.
      const extensions = program.symbols[binding]?.extensions ?? [];
      if (extensions.length) console.log(`Kernel extensions: ${extensions.map(name => `kernel extension: ${name}`).join(", ")}`);
    }
    else {
      const checked = program.checker.checkView(view.expression, view.type, view.context.map(e => [e.name, e.type]), new Map(view.dimensions ?? []));
      console.log(assemblyText(kernelAssembly(program, view, checked)));
    }
    return;
  }
  if (!view) throw Error("Inspect a checked name first.");
  if (["beta", "delta"].includes(operation)) {
    const side = value || "expression";
    if (!["expression", "type"].includes(side)) throw Error("Expected expression or type.");
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
        catch (error) { console.error(shown(error)); }
        prompt("cubist> ");
      }
    } finally { input.close(); }
  }
} catch (error) { console.error(shown(error)); process.exitCode = 1; }
finally { program?.dispose(); sessionProgram?.dispose(); }
