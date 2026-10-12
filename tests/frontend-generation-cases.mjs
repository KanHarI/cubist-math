// The frontend-generation cases: Cubist modules in fixtures/frontend-generation/,
// each headed `// ID (phase): contract.` and stating its desired check as
// tools/inline-errors.mjs writes it: an `// Error:` or `// Warning:` comment
// above each declaration the checker must refuse or warn about, and nothing
// above one that must check. What a comment cannot state, a source range, a
// navigation link, lint advice, a published name or a work counter, is
// observed below, beside its desired value. frontend-generation.md says where
// the desired outputs come from.
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { lint } from "../web/cubist/lint.mjs";
import { reported, stated } from "../tools/inline-errors.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";

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

// The line, trimmed, that holds a source position.
const lineAt = (source, at) => {
  const end = source.indexOf("\n", at);
  return source.slice(source.lastIndexOf("\n", at - 1) + 1, end === -1 ? undefined : end).trim();
};
// A declaration's refusals, each as the source it covers and the line where
// that starts; an unlocated refusal is null.
const range = name => (source, result) => result.gaps.filter(gap => gap.name === name).map(({ start, end }) =>
  Number.isInteger(start) && Number.isInteger(end) ? { line: lineAt(source, start), covers: source.slice(start, end) } : null);
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
// The linter's advice, with the source each warning covers.
const advice = source => lint(source).map(({ code, declaration, message, start, end }) =>
  ({ code, declaration, message, covers: source.slice(start, end) }));
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
  G5: { advice: [advice, []] },
  "G5-single": { advice: [advice, []] },
  G8: { range: [range("h"), [{ line: "_ => t1;", covers: "t1" }]], searches: [searches("h"), [0]] },
  G9: { links: [links("law l(c : M) : k(c) = op(c, c);", "c"), Array(4).fill([{ name: "c", target: 0, start: 0, end: 0 }])] },
  G10: { range: [range("T"), [{ line: "succ(c) => k(c);", covers: "c" }]] },
  "G12-range": { range: [range("T"), [{ line: "law nope(n : Nat) : iter(n) = c;", covers: "iter(n)" }]] },
  "control-paths-wrong": { obligations: [obligations("bad"), 0] },
  "control-paths-wrong-multi": { obligations: [obligations("bad"), 0] },
};

// A comment's place is the line it stands above, so that a comment moves
// no other.
const placed = (source, items) => {
  const lines = source.split("\n");
  return items.map(({ line, label, text }) => ({ at: lines[line].trim(), label, text }));
};
// What a case's check shows, and what it should show. A client must also
// check without assumptions.
export async function observe(t, c, module) {
  const { program, result } = await checkProgram(t, c.source, { module, reader: sourceReader({ path: c.path }), name: c.name });
  const observed = {
    diagnostics: placed(c.source, reported(c.source, result, c.name)),
    assumes: result.outputs.filter(output => output.verified && output.axioms?.length).map(output => output.name),
  };
  const desired = { diagnostics: placed(c.source, stated(c.source)), assumes: [] };
  for (const [key, [view, value]] of Object.entries(extras[c.id] ?? {})) {
    observed[key] = view(c.source, result, program, c.name);
    desired[key] = value;
  }
  return { observed, desired };
}
