// The frontend-generation cases: Cubist modules in fixtures/frontend-generation/,
// each headed `// ID (phase): contract.` and stating its desired check as
// tools/inline-errors.mjs writes it: an `// Error:` or `// Warning:` comment
// above each declaration the checker must refuse or warn about, and nothing
// above one that must check. Before comparing comments, require imports to
// check and account for every local failure in the reported errors. The
// comparison sees local errors and warnings, at the line of their declaration.
// It does not see a declaration with no output, which reports nothing, where
// in its line a refusal lies, or the work a check did. So every case also
// observes the declarations without a comment that have no output of their
// own, and a case that needs them observes a refusal's range, the links at
// each use of a name, the names it must not publish or a work counter, each
// beside its desired value. A generated output has no line of its own: a
// written client uses each generated interface a case needs.
// frontend-generation.md says where the desired outputs come from.
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { parse } from "../web/cubist/parser.mjs";
import { normal } from "../web/cubist/stated-comments.mjs";
import { reported, stated } from "../tools/inline-errors.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";
import { precondition } from "./known-defect.mjs";

const directory = new URL("./fixtures/frontend-generation/", import.meta.url);
export const cases = readdirSync(directory).filter(file => file.endsWith(".cubist")).sort().map(file => {
  const path = fileURLToPath(new URL(file, directory)), source = readFileSync(path, "utf8");
  const header = source.split("\n")[0].match(/^\/\/ ([\w-]+) \(([^)]+)\): (.+)\.$/);
  assert.ok(header, `${file} needs a "// ID (phase): contract." first line`);
  const [, id, phase, contract] = header;
  return { id, group: id.split("-")[0], phase, contract, name: file.slice(0, -".cubist".length), path, source };
});
// The provenance and browser tests read a case's source by its ID.
export const gaps = Object.fromEntries(cases.map(c => [c.id, c]));

// The line (from 0) that holds a source position.
const lineOf = (source, at) => source.slice(0, at).split("\n").length - 1;
// The declarations written without a comment above them that have no output
// of their own, each as its first line: a declaration that a later one
// replaced, for example, reports nothing.
const missing = (source, result) => {
  const lines = source.split("\n"), commented = new Set(stated(source).map(item => item.line));
  return parse(source).declarations.map(d => ({ name: d.name.text, line: lineOf(source, d.start) }))
    .filter(({ name, line }) => !commented.has(line)
      && !result.outputs.some(output => output.name === name && lineOf(source, output.start) === line))
    .map(({ line }) => lines[line].trim());
};
// A declaration's refusals, each as the line where it starts, that line's
// text before it and the source it covers; an unlocated refusal is null.
const range = name => (source, result) => result.gaps.filter(gap => gap.name === name).map(({ start, end }) => {
  if (!Number.isInteger(start) || !Number.isInteger(end)) return null;
  const from = source.lastIndexOf("\n", start - 1) + 1, to = source.indexOf("\n", start);
  return { line: source.slice(from, to === -1 ? undefined : to).trim(), before: source.slice(from, start).trimStart(),
    covers: source.slice(start, end) };
});
// The distinct links at each written occurrence of `label` in `line`: the
// span relative to the occurrence and the target relative to the first
// occurrence, its binder.
const links = (line, label) => (source, result) => {
  assert.equal(source.split(line).length, 2, `${line} must occur once`);
  const at = source.indexOf(line);
  const positions = [...line.matchAll(new RegExp(`\\b${label}\\b`, "g"))].map(match => at + match.index);
  return positions.map(position => [...new Set(result.links
    .filter(link => link.start < position + label.length && link.end > position)
    .map(link => JSON.stringify({
      name: link.name, target: Number.isInteger(link.definitionStart) ? link.definitionStart - positions[0] : null,
      start: link.start - position, end: link.end - position - label.length,
    })))].map(text => JSON.parse(text)));
};
// The published outputs named by or under these names.
const published = (...names) => (source, result) => result.outputs.map(output => output.name)
  .filter(name => names.some(prefix => name === prefix || name.startsWith(`${prefix}.`)));
// The coherence searches a declaration started.
const searches = name => (source, result) => result.outputs.filter(output => output.name === name)
  .map(output => output.searchFuel?.searches);
// The coherence obligations elaborated for a declaration.
const obligations = declaration => (source, result, program, name) => program.steps(name)
  .filter(step => step.declaration === declaration && step.kind === "obligation").length;

// Each case's further observations, with their desired values.
export const extras = {
  "G1-initial": { published: [published("N.model", "N.fold_map", "N.fold"), []] },
  G3: { published: [published("T.Hom", "T.Iso"), []] },
  G8: { range: [range("h"), [{ line: "_ => t1;", before: "_ => ", covers: "t1" }]], searches: [searches("h"), [0]] },
  G9: { links: [links("law l(c : M) : k(c) = op(c, c);", "c"), Array(4).fill([{ name: "c", target: 0, start: 0, end: 0 }])] },
  "G12-range": { range: [range("T"), [{ line: "law nope(n : Nat) : iter(n) = c;", before: "law nope(n : Nat) : ",
    covers: "iter(n)" }]] },
  "control-paths-wrong": { obligations: [obligations("bad"), 0] },
  "control-paths-wrong-multi": { obligations: [obligations("bad"), 0] },
};

// A comment's place is the line it stands above, so that a comment moves
// no other.
// G10's contract is semantic. The mismatch's printed binder may be renamed
// by the capture fix; it checks the diagnostic code, not that display label.
const codeDiagnostics = new Set(["G10"]);
const placed = (source, items, codesOnly = false) => {
  const lines = source.split("\n");
  return items.map(({ line, label, text }) => ({ at: lines[line].trim(), label,
    text:codesOnly ? text.replace(/^([EW]\d+):[\s\S]*$/, "$1") : text }));
};
// What a case's check shows, and what it should show. A client must also
// check without assumptions.
export async function observe(t, c, module) {
  const { program, result } = await checkProgram(t, c.source, { module, reader: sourceReader({ path: c.path }), name: c.name });
  const diagnostics = reported(c.source, result, c.name);
  // Imports must check. Every local gap needs an error in the presentation;
  // consume each once, so one reported error cannot hide multiple failures.
  const errors = diagnostics.filter(item => item.label === "Error").map(item => item.text);
  const unreported = result.gaps.filter(gap => {
    if (gap.module !== c.name) return true;
    const at = errors.indexOf(normal(gap.code ? `${gap.code}: ${gap.reason}` : gap.reason));
    if (at < 0) return true;
    errors.splice(at, 1);
    return false;
  });
  precondition(() => assert.deepEqual(unreported, [], `${c.id}: checker failures outside the local checked comments`));
  const observed = {
    diagnostics: placed(c.source, diagnostics, codeDiagnostics.has(c.id)),
    missing: missing(c.source, result),
    assumes: result.outputs.filter(output => output.verified && output.axioms?.length).map(output => output.name),
  };
  const desired = { diagnostics: placed(c.source, stated(c.source), codeDiagnostics.has(c.id)), missing: [], assumes: [] };
  for (const [key, [view, value]] of Object.entries(extras[c.id] ?? {})) {
    observed[key] = view(c.source, result, program, c.name);
    desired[key] = value;
  }
  return { observed, desired };
}
