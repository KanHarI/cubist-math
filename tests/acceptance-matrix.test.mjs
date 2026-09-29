// The H1 specification's acceptance matrix (its 10.10) against the tests:
// the matrix says which acceptance cases are traced, and the tests it lists
// name each case they trace by its ID, so each can be checked against the
// other, and neither drifts from the other unseen.
import test from "node:test";
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";

const read = path => readFileSync(new URL(`../${path}`, import.meta.url), "utf8");
const specification = read("docs/roadmaps/h1-signature-specification.md");
const prefixes = "AVNKETGRX";

// The text of a section, from its heading to the next heading at its level
// or above.
function section(heading) {
  const start = specification.indexOf(`\n${heading}`);
  assert.ok(start >= 0, heading);
  const level = heading.match(/^#+/)[0].length;
  const rest = specification.slice(start + 1);
  const next = rest.slice(1).search(new RegExp(`\\n#{1,${level}} `));
  return next < 0 ? rest : rest.slice(0, next + 1);
}

// A cell's entries, outside the parentheses that explain them: an entry is
// an ID or a range written A2–A17, and "in part" after it qualifies every
// case it names. A package ID such as K2.5 or K2.4a is not a case, but a
// case may end a sentence.
function outsideParentheses(text) {
  for (let previous; previous !== text;) [previous, text] = [text, text.replace(/\([^()]*\)/g, "")];
  return text;
}
function entries(text, prefix) {
  const full = new Set(), partial = new Set();
  const pattern = new RegExp(`\\b${prefix}(\\d+)(?:–${prefix}?(\\d+))?(?!\\d|\\.[\\da-z])(\\s+in part\\b)?`, "g");
  for (const match of outsideParentheses(text).matchAll(pattern)) {
    const from = Number(match[1]), to = Number(match[2] ?? match[1]);
    for (let n = from; n <= to; n++) (match[3] ? partial : full).add(`${prefix}${n}`);
  }
  return { full, partial, all: new Set([...full, ...partial]) };
}
const mentions = (text, prefix) => entries(text, prefix).all;

// Each case is defined by a table row of its own, in 7.3 and 10.1 to 10.9.
const defined = new Set([...specification.matchAll(new RegExp(`^\\| ([${prefixes}]\\d+) \\|`, "gm"))].map(match => match[1]));

const coverage = section("### 10.10 Coverage of the acceptance cases");
const introduction = coverage.slice(0, coverage.indexOf("\n|"));
// This checker is named there too, and names cases only to look for them.
const testFiles = [...introduction.matchAll(/`([^`]+\.(?:c|mjs))`/g)].map(match => match[1])
  .filter(path => path !== "tests/acceptance-matrix.test.mjs");
const named = new Map(testFiles.map(path => [path, read(path)]));
const namedIn = id => [...named].filter(([, source]) => new RegExp(`\\b${id}(?!\\d|\\.[\\da-z])`).test(source)).map(([path]) => path);

const rows = coverage.split("\n").filter(line => /^\| [A-Z][a-z]/.test(line) && !line.startsWith("| Group")).map(line => {
  const [group, traced, untraced, missing] = line.split("|").slice(1, -1).map(cell => cell.trim());
  const [, prefix, from, to] = group.match(/ ([A-Z])(\d+)–[A-Z](\d+)$/);
  const cases = [...mentions(`${prefix}${from}–${to}`, prefix)];
  // "All" in the missing column stands for every case, beside any it names.
  const named = { traced: mentions(traced, prefix), untraced: mentions(untraced, prefix), missing: mentions(missing, prefix) };
  return { group, prefix, cases, traced, untraced, missing, named, coverage: entries(traced, prefix),
    columns: { ...named, missing: /^All\b/.test(missing) ? new Set([...cases, ...named.missing]) : named.missing } };
});

test("the matrix's groups cover exactly the cases the specification defines", () => {
  assert.equal(rows.map(row => row.prefix).join(""), prefixes);
  assert.deepEqual(rows.flatMap(row => row.cases).sort(), [...defined].sort());
  assert.ok(defined.size > 100, "the case tables were found");
});

test("the matrix lists each of the test files it names", () => {
  assert.ok(testFiles.includes("kernel/tests/test_signatures.c") && testFiles.length >= 6, testFiles.join(", "));
  assert.ok(introduction.includes("`tests/acceptance-matrix.test.mjs`") && !testFiles.includes("tests/acceptance-matrix.test.mjs"));
  for (const path of testFiles) assert.ok(existsSync(new URL(`../${path}`, import.meta.url)), path);
});

test("each case is in the matrix, and a case has a remainder exactly when it is traced only in part", () => {
  for (const { group, cases, named, coverage, columns } of rows) {
    for (const [column, ids] of Object.entries(named))
      for (const id of ids) assert.ok(cases.includes(id), `${group}: the ${column} column names ${id}, which is no case of the group`);
    for (const id of cases) {
      const remainder = columns.untraced.has(id) || columns.missing.has(id);
      assert.ok(columns.traced.has(id) || remainder, `${group}: ${id} is in no column`);
      if (columns.traced.has(id) && !coverage.full.has(id))
        assert.ok(remainder, `${group}: ${id} is traced only in part, so its remainder must be listed`);
      if (columns.traced.has(id) && remainder)
        assert.ok(!coverage.full.has(id), `${group}: ${id} is traced in full, so it can have no remainder`);
    }
  }
});

// The traced column says where: a case after "Kernel:" is named in the
// kernel's tests, and one after "Driver:", "Source:" or "Verifier:" in the
// JavaScript tests.
function layers(traced) {
  const parts = traced.split(/\b(Kernel|Driver|Source|Verifier):/);
  const result = parts[0].trim() ? [{ layer: null, text: parts[0] }] : [];
  for (let i = 1; i < parts.length; i += 2) result.push({ layer: parts[i], text: parts[i + 1] });
  return result;
}
const filesOf = layer => testFiles.filter(path => !layer || (layer === "Kernel") === path.endsWith(".c"));

test("a traced case is named by its ID in a test of each layer that traces it", () => {
  for (const { group, prefix, traced } of rows) {
    for (const { layer, text } of layers(traced)) {
      for (const id of mentions(text, prefix)) {
        const files = filesOf(layer);
        assert.ok(namedIn(id).some(path => files.includes(path)),
          `${group}: ${layer ?? "the matrix"} traces ${id}, but none of ${files.join(", ")} names it`);
      }
    }
  }
});

test("a case a test names is traced", () => {
  for (const { group, cases, columns } of rows)
    for (const id of cases.filter(id => !columns.traced.has(id)))
      assert.deepEqual(namedIn(id), [], `${group}: a test names ${id}, but the matrix does not trace it`);
});
