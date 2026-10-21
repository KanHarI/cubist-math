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
import {checkedSource} from "./checked-source.mjs";
import {testProblems} from "../web/cubist/test-pragmas.mjs";
import { cubistTestModules } from "../web/cubist/modules.mjs";
import { sourceReader } from "./module-sources.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";
// The comments' syntax and what they state, which the benchmark reads too.
import { readComment, normal, stated } from "../web/cubist/stated-comments.mjs";

export { stated };

export const testModulePath = name => fileURLToPath(new URL(`../cubist-tests/${name}.cubist`, import.meta.url));
const WIDTH = 100;
// Comments above one line come in this order.
const rank = { Output: 0, Error: 1, Warning: 2 };

// The source without its checked comments.
export function stripped(source) {
  const lines = source.split("\n"), kept = [];
  for (let i = 0; i < lines.length; i++) {
    const block = readComment(lines, i);
    if (!block) { kept.push(lines[i]); continue; }
    i = block.end;
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
  const evaluations = (result.evaluations ?? []).filter(evaluation => evaluation.module === main && evaluation.start !== undefined);
  const starts = [...result.outputs.map(output => lineAt(output.start)), ...prints.map(print => lineAt(print.start)),
    ...evaluations.map(evaluation => lineAt(evaluation.start)),
    ...(result.gaps ?? []).filter(gap => (gap.directive || gap.duplicate) && gap.module === main && gap.start !== undefined).map(gap => lineAt(gap.start))]
    .sort((a, b) => a - b);
  const labelled = (code, message) => normal(code ? `${code}: ${message}` : message);
  const items = [];
  for (const output of result.outputs)
    if (!output.verified) items.push({ line: lineAt(output.start), label: "Error", text: labelled(output.code, output.reason) });
  for (const gap of result.gaps ?? [])
    if ((gap.directive || gap.duplicate) && gap.module === main) items.push({ line: lineAt(gap.start ?? 0), label: "Error", text: labelled(gap.code, gap.reason) });
  for (const print of prints) items.push({ line: lineAt(print.start), label: "Output", text: normal(print.text, "Output") });
  for (const warning of result.warnings ?? []) {
    const line = warning.line - 1;
    items.push({ line: starts.filter(start => start <= line).at(-1) ?? 0, label: "Warning", text: labelled(warning.code, warning.message) });
  }
  return items.sort((a, b) => a.line - b.line || rank[a.label] - rank[b.label]);
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
  return {source,...await checkedTestSource(source,name,path,module)};
}

async function checkedTestSource(source,name,path,module) {
  const checked=await checkedSource(source,name,{module,reader:sourceReader({path}),options:{testMode:true}});
  const problems=testProblems(checked.contracts);
  if(problems.length)throw new Error(problems.join("\n"));
  return checked;
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
      const {result}=await checkedTestSource(plain,name,path,module);
      const text = inlined(plain, reported(plain, result, name));
      if (text !== source) { await writeFile(path, text); console.log(`wrote ${name}`); }
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
