// The H1 specification's acceptance matrix (its 10.10) against the tests:
// the matrix says which acceptance cases are traced, and the tests it lists
// name each case they trace by its ID, so each can be checked against the
// other, and neither drifts from the other unseen. The checker is a function
// of the specification and the test sources, so it is also tried on the
// mutated matrices its reviews found it had to refuse.
import test from "node:test";
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";

const read = path => readFileSync(new URL(`../${path}`, import.meta.url), "utf8");
const exists = path => existsSync(new URL(`../${path}`, import.meta.url));
const specification = read("docs/roadmaps/h1-signature-specification.md");
const prefixes = "AVNKETGRX";
// This checker is named in the matrix's introduction too, and names cases
// only to look for them.
const checker = "tests/acceptance-matrix.test.mjs";
const coverageHeading = "### 10.10 Coverage of the acceptance cases";

// The text of a section, from its heading to the next heading at its level
// or above.
function section(text, heading) {
  const start = text.indexOf(`\n${heading}`);
  assert.ok(start >= 0, heading);
  const level = heading.match(/^#+/)[0].length;
  const rest = text.slice(start + 1);
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

// The traced column says where: a case after "Kernel:" is named in the
// kernel's tests, and one after "Driver:", "Source:" or "Verifier:" in the
// JavaScript tests.
function layers(traced) {
  const parts = traced.split(/\b(Kernel|Driver|Source|Verifier):/);
  const result = parts[0].trim() ? [{ layer: null, text: parts[0] }] : [];
  for (let i = 1; i < parts.length; i += 2) result.push({ layer: parts[i], text: parts[i + 1] });
  return result;
}

// The matrix of a specification, with the sources of the tests it names;
// `groups` are its groups' prefixes, in order.
function matrix(text, source, groups = prefixes) {
  // Each case is defined by a table row of its own, in 7.3 and 10.1 to 10.9.
  const defined = new Set([...text.matchAll(new RegExp(`^\\| ([${groups}]\\d+) \\|`, "gm"))].map(match => match[1]));
  const coverage = section(text, coverageHeading);
  const introduction = coverage.slice(0, coverage.indexOf("\n|"));
  const testFiles = [...introduction.matchAll(/`([^`]+\.(?:c|mjs))`/g)].map(match => match[1]).filter(path => path !== checker);
  const sources = new Map(testFiles.map(path => [path, source(path)]));
  const namedIn = id => [...sources].filter(([, text]) => new RegExp(`\\b${id}(?!\\d|\\.[\\da-z])`).test(text)).map(([path]) => path);
  const rows = coverage.split("\n").filter(line => /^\| [A-Z][a-z]/.test(line) && !line.startsWith("| Group")).map(line => {
    const [group, traced, untraced, missing] = line.split("|").slice(1, -1).map(cell => cell.trim());
    const [, prefix, from, to] = group.match(/ ([A-Z])(\d+)–[A-Z](\d+)$/);
    const cases = [...mentions(`${prefix}${from}–${to}`, prefix)];
    // "All" in the missing column stands for every case, beside any it names.
    const named = { traced: mentions(traced, prefix), untraced: mentions(untraced, prefix), missing: mentions(missing, prefix) };
    return { group, prefix, cases, traced, named, coverage: entries(traced, prefix),
      columns: { ...named, missing: /^All\b/.test(missing) ? new Set([...cases, ...named.missing]) : named.missing } };
  });
  return { defined, introduction, testFiles, namedIn, rows };
}

// What the matrix gets wrong, against the cases the specification defines
// and against the tests: one finding each, none when it is right.
function findings(text, source = read, present = exists, groups = prefixes) {
  const { defined, testFiles, namedIn, rows } = matrix(text, source, groups), found = [];
  const order = rows.map(row => row.prefix).join("");
  if (order !== groups) found.push(`The matrix's groups are ${order}, where the cases are ${groups}.`);
  const covered = new Set(rows.flatMap(row => row.cases));
  for (const id of defined) if (!covered.has(id)) found.push(`${id} is a case, and no group covers it.`);
  for (const id of covered) if (!defined.has(id)) found.push(`A group covers ${id}, which is no case.`);
  for (const path of testFiles) if (!present(path)) found.push(`The matrix names ${path}, which does not exist.`);
  const filesOf = layer => testFiles.filter(path => !layer || (layer === "Kernel") === path.endsWith(".c"));
  for (const { group, prefix, cases, traced, named, coverage, columns } of rows) {
    // Each case is in the matrix, and has a remainder exactly when it is
    // traced only in part.
    for (const [column, ids] of Object.entries(named))
      for (const id of ids) if (!cases.includes(id)) found.push(`${group}: the ${column} column names ${id}, which is no case of the group.`);
    for (const id of cases) {
      const remainder = columns.untraced.has(id) || columns.missing.has(id);
      if (!columns.traced.has(id) && !remainder) found.push(`${group}: ${id} is in no column.`);
      if (columns.traced.has(id) && !coverage.full.has(id) && !remainder)
        found.push(`${group}: ${id} is traced only in part, so its remainder must be listed.`);
      if (columns.traced.has(id) && coverage.full.has(id) && remainder)
        found.push(`${group}: ${id} is traced in full, so it can have no remainder.`);
    }
    // A traced case is named by its ID in a test of each layer that traces
    // it, and a case a test names is traced.
    for (const { layer, text } of layers(traced))
      for (const id of mentions(text, prefix)) {
        const files = filesOf(layer);
        if (!namedIn(id).some(path => files.includes(path)))
          found.push(`${group}: ${layer ?? "the matrix"} traces ${id}, but none of ${files.join(", ")} names it.`);
      }
    for (const id of cases.filter(id => !columns.traced.has(id)))
      if (namedIn(id).length) found.push(`${group}: ${namedIn(id).join(", ")} name ${id}, but the matrix does not trace it.`);
  }
  return found;
}

test("the matrix is read as written: its cases, groups and test files", () => {
  const { defined, introduction, testFiles, rows } = matrix(specification, read);
  assert.ok(defined.size > 100, "the case tables were found");
  assert.equal(rows.map(row => row.prefix).join(""), prefixes);
  assert.ok(testFiles.includes("kernel/tests/test_signatures.c") && testFiles.length >= 6, testFiles.join(", "));
  assert.ok(introduction.includes(`\`${checker}\``) && !testFiles.includes(checker));
});

test("the matrix agrees with the cases and with the tests", () => {
  assert.deepEqual(findings(specification), []);
});

// The fixtures: a small specification of their own, so that they do not
// follow the real matrix as its cases are traced. Its cases are K1–K4 and
// X1–X2, traced in two test files; the checker's own source names every
// case, and is no evidence for any.
const small = ({ kan = "Kernel: K1 in part (with no tubes), K2. Source: K3", kanRest = "K1 with tubes",
  kanMissing = "K4: no generator", differential = "All: K2.4a" } = {}) => `
### 10.4 Kan structure
| ID | Case | Verdict |
| --- | --- | --- |
${["K1", "K2", "K3", "K4", "X1", "X2"].map(id => `| ${id} | a case | a verdict |`).join("\n")}
${coverageHeading}
Traced in \`kernel/tests/small.c\` and \`tests/small.test.mjs\`; \`${checker}\` checks this table.
| Group | Traced | Not traced | Missing, and why |
| --- | --- | --- | --- |
| Kan K1–K4 | ${kan} | ${kanRest} | ${kanMissing} |
| Differential X1–X2 | — | — | ${differential} |
`;
const smallSources = { "kernel/tests/small.c": "// K1, K2", "tests/small.test.mjs": "// K3", [checker]: "K1 K2 K3 K4 X1 X2" };
const findingsIn = (text, sources = {}) =>
  findings(text, path => ({ ...smallSources, ...sources })[path], path => path in smallSources, "KX");
const found = (all, finding) => assert.ok(all.includes(finding), `${finding}\nfound: ${all.join(" / ") || "nothing"}`);

test("the fixtures' matrix is right as it stands", () => {
  assert.deepEqual(findingsIn(small()), []);
  // A package ID such as K2.5 is no case.
  assert.deepEqual(findingsIn(small({ kanMissing: "K4: waits for K2.5" })), []);
});

// The matrix's frame: its groups against the cases defined, and the test
// files its introduction names, which are the only ones.
test("the checker refuses a matrix whose groups, cases or test files are wrong", () => {
  const withoutDifferential = findingsIn(small().replace(/^\| Differential .*\n/m, ""));
  found(withoutDifferential, "The matrix's groups are K, where the cases are KX.");
  found(withoutDifferential, "X1 is a case, and no group covers it.");
  found(findingsIn(small().replace("| Kan K1–K4 |", "| Kan K1–K5 |")), "A group covers K5, which is no case.");
  found(findingsIn(small().replace("`tests/small.test.mjs`", "`tests/small.test.mjs`, `tests/gone.test.mjs`")),
    "The matrix names tests/gone.test.mjs, which does not exist.");
  assert.deepEqual(findingsIn(small({ kanMissing: "K4: see `tests/other.test.mjs`" }), { "tests/other.test.mjs": "// K4" }), []);
});

// Missing test labels: a case the matrix traces in a layer that no test of
// that layer names, and a case a test names that the matrix does not trace.
// The checker's own source, which names every case, stands in for none.
test("the checker refuses a traced case whose label is gone", () => {
  found(findingsIn(small(), { "tests/small.test.mjs": "" }),
    "Kan K1–K4: Source traces K3, but none of tests/small.test.mjs names it.");
  found(findingsIn(small(), { "kernel/tests/small.c": "// K1" }),
    "Kan K1–K4: Kernel traces K2, but none of kernel/tests/small.c names it.");
  found(findingsIn(small(), { "kernel/tests/small.c": "// K1, K2, K4" }),
    "Kan K1–K4: kernel/tests/small.c name K4, but the matrix does not trace it.");
  // A label in the other layer's tests stands in for none, either way.
  found(findingsIn(small(), { "kernel/tests/small.c": "// K1, K2, K3", "tests/small.test.mjs": "" }),
    "Kan K1–K4: Source traces K3, but none of tests/small.test.mjs names it.");
  found(findingsIn(small(), { "kernel/tests/small.c": "// K1", "tests/small.test.mjs": "// K2, K3" }),
    "Kan K1–K4: Kernel traces K2, but none of kernel/tests/small.c names it.");
  // Nor does a package ID that begins with a case's.
  found(findingsIn(small(), { "kernel/tests/small.c": "// K1, K2.5" }),
    "Kan K1–K4: Kernel traces K2, but none of kernel/tests/small.c names it.");
  // A case before any layer is named in a test of either.
  const unlayered = small({ kan: "K2. Kernel: K1 in part (with no tubes). Source: K3" });
  assert.deepEqual(findingsIn(unlayered, { "kernel/tests/small.c": "// K1", "tests/small.test.mjs": "// K2, K3" }), []);
  found(findingsIn(unlayered, { "kernel/tests/small.c": "// K1" }),
    "Kan K1–K4: the matrix traces K2, but none of kernel/tests/small.c, tests/small.test.mjs names it.");
});

// Invalid IDs: a column naming an ID its group does not define, in each
// column, and beside "All".
test("the checker refuses an ID that is no case of its group", () => {
  found(findingsIn(small({ kan: "Kernel: K1 in part (with no tubes), K2, K7. Source: K3" })),
    "Kan K1–K4: the traced column names K7, which is no case of the group.");
  found(findingsIn(small({ kanRest: "K1 with tubes; K8" })),
    "Kan K1–K4: the untraced column names K8, which is no case of the group.");
  found(findingsIn(small({ kanMissing: "K4, K99: no generator" })),
    "Kan K1–K4: the missing column names K99, which is no case of the group.");
  found(findingsIn(small({ differential: "All: K2.4a; X99" })),
    "Differential X1–X2: the missing column names X99, which is no case of the group.");
});

// Missing remainders: a case traced in part whose rest is listed nowhere, a
// case in no column, and a case traced in full with a remainder.
test("the checker refuses a case whose remainder is missing, or that has one it cannot", () => {
  found(findingsIn(small({ kanRest: "—" })), "Kan K1–K4: K1 is traced only in part, so its remainder must be listed.");
  found(findingsIn(small({ kan: "Kernel: K1 in part (with no tubes). Source: K3" }), { "kernel/tests/small.c": "// K1" }),
    "Kan K1–K4: K2 is in no column.");
  found(findingsIn(small({ kanRest: "K1 with tubes; K2 with a tube" })),
    "Kan K1–K4: K2 is traced in full, so it can have no remainder.");
  // An ID repeated in its own note does not make its case traced in full.
  found(findingsIn(small({ kan: "Kernel: K1 in part (K1 with no tubes), K2. Source: K3", kanRest: "—" })),
    "Kan K1–K4: K1 is traced only in part, so its remainder must be listed.");
});

// Partial ranges: "in part" after a range qualifies every case in it.
test("the checker reads a range traced in part as each of its cases in part", () => {
  const range = "Kernel: K1–K2 in part (with no tubes). Source: K3";
  found(findingsIn(small({ kan: range })), "Kan K1–K4: K2 is traced only in part, so its remainder must be listed.");
  assert.deepEqual(findingsIn(small({ kan: range, kanRest: "K1 and K2 with tubes" })), []);
});
