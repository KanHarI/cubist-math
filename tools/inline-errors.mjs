// The checker's diagnostics and outputs of the Cubist test modules, inlined
// as comments.
//
//   node tools/inline-errors.mjs [--write] [module …]
//
// Each test module of cubist-tests/ (all of them, unless some are named) is
// checked as the command line checks the file. Every error and warning the
// checker reports is a comment directly above the declaration or directive
// it belongs to, and so is what each print directive shows:
//
//   // Error: E606: Type mismatch: found succ(zero) = succ(zero), expected zero = zero.
//   // Warning: W703: z is unused: the return type does not mention it. …
//   // Output: succ(succ(zero))
//   print(evaluate(double(1)));
//
// A comment too long for a line continues on `//   …` lines. Positions are
// left out: the comments themselves move what follows them. Every other
// comment stays as it is. With --write the tool rewrites each module's
// checked comments; without it, it reports each module whose comments
// differ from what the checker reports, and exits with status 1.
// tests/cubist-tests.test.mjs makes the same comparison.
import { readFile, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { cubistTestModules } from "../web/cubist/modules.mjs";
import { sourceReader } from "./module-sources.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";

export const testModulePath = name => fileURLToPath(new URL(`../cubist-tests/${name}.cubist`, import.meta.url));
const WIDTH = 100;
const comment = /^\s*\/\/ (Error|Warning|Output): (.*)$/, continued = /^\s*\/\/ {3}(.*)$/;
// Text as a comment holds it: its whitespace collapsed, and a message
// without the position that ends a reason.
const collapsed = text => text.replace(/\s+/g, " ").trim();
const normal = (text, label = "Error") => label === "Output" ? collapsed(text) : collapsed(text).replace(/ at \d+:\d+$/, "");
// Comments above one line come in this order.
const rank = { Output: 0, Error: 1, Warning: 2 };

// The source without its checked comments.
export function stripped(source) {
  const lines = source.split("\n"), kept = [];
  for (let i = 0; i < lines.length; i++) {
    if (!comment.test(lines[i])) { kept.push(lines[i]); continue; }
    while (i + 1 < lines.length && continued.test(lines[i + 1])) i++;
  }
  return kept.join("\n");
}

// What a check reports, each item at the line (from 0) of the declaration
// or directive it belongs to: a refused declaration's reason, a failed
// directive's, what a print directive shows, and each warning, at the
// declaration or directive it falls in.
export function reported(source, result, main) {
  const lineAt = offset => source.slice(0, offset).split("\n").length - 1;
  const prints = (result.prints ?? []).filter(print => print.module === main);
  const starts = [...result.outputs.map(output => lineAt(output.start)), ...prints.map(print => lineAt(print.start)),
    ...(result.gaps ?? []).filter(gap => gap.directive && gap.module === main && gap.start !== undefined).map(gap => lineAt(gap.start))]
    .sort((a, b) => a - b);
  const labelled = (code, message) => normal(code ? `${code}: ${message}` : message);
  const items = [];
  for (const output of result.outputs)
    if (!output.verified) items.push({ line: lineAt(output.start), label: "Error", text: labelled(output.code, output.reason) });
  for (const gap of result.gaps ?? [])
    if (gap.directive && gap.module === main) items.push({ line: lineAt(gap.start ?? 0), label: "Error", text: labelled(gap.code, gap.reason) });
  for (const print of prints) items.push({ line: lineAt(print.start), label: "Output", text: normal(print.text, "Output") });
  for (const warning of result.warnings ?? []) {
    const line = warning.line - 1;
    items.push({ line: starts.filter(start => start <= line).at(-1) ?? 0, label: "Warning", text: labelled(warning.code, warning.message) });
  }
  return items.sort((a, b) => a.line - b.line || rank[a.label] - rank[b.label]);
}

// What the comments state, each at the line below its comment block.
export function stated(source) {
  const lines = source.split("\n"), items = [];
  let pending = [];
  for (let i = 0; i < lines.length; i++) {
    const match = lines[i].match(comment);
    if (match) {
      let text = match[2];
      while (i + 1 < lines.length && continued.test(lines[i + 1])) text += ` ${lines[++i].match(continued)[1]}`;
      pending.push({ label: match[1], text: normal(text, match[1]) });
      continue;
    }
    if (/^\s*\/\//.test(lines[i])) continue;
    for (const item of pending) items.push({ line: i, ...item });
    pending = [];
  }
  return items;
}

// An item as comment lines, wrapped at spaces.
function commentLines(indent, label, text) {
  const out = [], words = text.split(" ");
  let line = `${indent}// ${label}:`;
  for (const word of words) {
    if (line.length + 1 + word.length > WIDTH && !/\/\/( {3}| \w+:)$/.test(line)) { out.push(line); line = `${indent}//  `; }
    line += ` ${word}`;
  }
  out.push(line);
  return out;
}

// The stripped source with each item written above its line.
export function inlined(source, items) {
  const lines = source.split("\n"), out = [];
  for (let i = 0; i < lines.length; i++) {
    const indent = lines[i].match(/^\s*/)[0];
    for (const item of items.filter(item => item.line === i)) out.push(...commentLines(indent, item.label, item.text));
    out.push(lines[i]);
  }
  return out.join("\n");
}

// A test module checked as the command line checks its file.
export async function checkedModule(name, module = null) {
  const path = testModulePath(name), source = await readFile(path, "utf8");
  const program = new CubicalProgram(module ?? await createCubical(), sourceReader({ path }));
  try { return { source, result: await program.check(source, name) }; }
  finally { program.dispose(); }
}

if (process.argv[1]?.endsWith("inline-errors.mjs")) {
  assertFreshBuild();
  const args = process.argv.slice(2), write = args.includes("--write");
  const names = args.filter(arg => !arg.startsWith("--"));
  const module = await createCubical();
  let differing = 0;
  for (const name of names.length ? names : cubistTestModules) {
    const path = testModulePath(name), source = await readFile(path, "utf8");
    if (write) {
      const plain = stripped(source);
      const program = new CubicalProgram(module, sourceReader({ path }));
      try {
        const result = await program.check(plain, name);
        const text = inlined(plain, reported(plain, result, name));
        if (text !== source) { await writeFile(path, text); console.log(`wrote ${name}`); }
      } finally { program.dispose(); }
    } else {
      const { result } = await checkedModule(name, module);
      if (JSON.stringify(reported(source, result, name)) !== JSON.stringify(stated(source))) {
        differing++;
        console.log(`${name}: its checked comments differ from what the checker reports`);
      }
    }
  }
  if (!write && differing) {
    console.log("Run node tools/inline-errors.mjs --write to rewrite them.");
    process.exitCode = 1;
  }
}
