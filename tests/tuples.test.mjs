import test from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { parse } from "../web/mathscript/parser.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";

const module = await createKernel();
const semantic = node => JSON.parse(JSON.stringify(node, (key, value) =>
  ["start", "end", "operatorStart", "operatorEnd", "tupleStart", "tupleEnd", "syntheticTuplePair", "valueStart", "valueEnd", "definitionStart"].includes(key) ? undefined : value));

test("tuples expand to right-associated pairs without changing comparison syntax", () => {
  for (const [sugar, expanded] of [
    ["(a, b)", "(a, b)"],
    ["(a, b, c, d)", "(a, (b, (c, d)))"],
    ["((a, b), c, d)", "((a, b), (c, d))"],
    ["(a < b, c, d)", "(a < b, (c, d))"],
    ["f((a, b, c), d)", "f((a, (b, c)), d)"],
  ]) assert.deepEqual(semantic(parse(sugar, true)), semantic(parse(expanded, true)), sugar);
  assert.equal(parse("a < b", true).kind, "binary");
  for (const invalid of ["()", "(a, b,)", "(a, b", "(a b)", "<a,b>"])
    assert.throws(() => parse(invalid, true));
  assert.throws(() => parse(`(${Array(129).fill("a").join(",")})`, true), /nesting/);
});

test("dependent tuple construction and obtain produce exactly the binary-pair kernel instructions", () => {
  const source = `
    def triple(n : Nat) : exists m : Nat, (m = n) and Nat {
      exact (n, refl(n), succ(n));
    }
    theorem unpacked : Nat {
      obtain (a, same, b) = triple(0);
      exact b;
    }
    theorem nested : (Nat and Nat) and Nat and Nat { exact ((0, 1), 2, 3); }
  `;
  const expanded = source.replace("(n, refl(n), succ(n))", "(n, (refl(n), succ(n)))")
    .replace("(a, same, b)", "(a, (same, b))").replace("((0, 1), 2, 3)", "((0, 1), (2, 3))");
  const a = compile(module, source), b = compile(module, expanded);
  try {
    assert.deepEqual(a.kernel.steps, b.kernel.steps);
    for (const output of a.outputs) assert.ok(a.kernel.verify(output.proposition, output.binding));
    const links = a.links.filter(l => l.role === "tuple macro");
    assert.equal(links.length, 6); // delimiters of each tuple with three or more components
    for (const link of links) {
      assert.ok(["(", ")"].includes(source.slice(link.start, link.end)));
      assert.ok(a.kernel.bindings.has(link.binding));
      assert.match(link.description, /Expands to/);
    }
    assert.ok(links.some(l => l.expansion === "(n, (refl(n), succ(n)))"));
    assert.ok(links.some(l => l.expansion === "(a, (same, b))"));
    assert.deepEqual(a.kernel.axiomsFor("triple"), []);
  } finally { a.kernel.dispose(); b.kernel.dispose(); }
  for (const source of [
    "theorem bad : Nat and Nat { exact (0, 1, 2); }",
    "theorem bad : exists n : Nat, (n = 0) and Nat { exact (1, refl(0), 2); }",
  ]) assert.throws(() => compile(module, source), /Expected|pair|type|differ/);
});

test("tuple formatting preserves nested delimiters, comments, comparisons and patterns", () => {
  const source = `theorem build(a:Nat,b:Nat):Nat and Nat and Nat{exact (a, // saved
b,0);} theorem unpacked : Nat { obtain (a,b,c) = build(0,0); exact c; }
  def nested = typed((Nat and Nat) and Nat and Nat, ((0,1),2,3));
  def relation(a:Nat,b:Nat) = a < b;
`;
  for (const printWidth of [40, 80, 100]) {
    const formatted = formatMathScript(source, { printWidth });
    assert.equal(formatMathScript(formatted, { printWidth }), formatted);
    assert.deepEqual(semantic(parse(formatted)), semantic(parse(source)));
    assert.match(formatted, /a, \/\/ saved\n/);
    assert.match(formatted, /a < b/);
  }
});

test("AST linearization preserves comments, grouping, left components and application arguments", async () => {
  const { linearizeTuples, expandedSyntax } = await import("../web/mathscript/tuples.mjs");
  const source = `// 🧮 A tuple with a paired first field and a right-associated tail.
    theorem build : (Nat and Nat) and Nat and Nat and Nat {
      exact ((0, 1), (2, // keep the tail note
        ((3, 4))));
    }
    theorem use : Nat { obtain ((a, b), (c, (d, e))) = build; exact e; }
    def call = f(a, b, c);
  `;
  const raw = linearizeTuples(source);
  const result = { ...raw, source: formatMathScript(raw.source) };
  assert.equal(result.count, 5);
  assert.equal(expandedSyntax(parse(result.source)), expandedSyntax(parse(source)));
  assert.match(result.source, /exact \(\(0, 1\), 2, \/\/ keep the tail note\n\s+3, 4\)/);
  assert.match(result.source, /obtain \(\(a, b\), c, d, e\)/);
  assert.match(result.source, /f\(a, b, c\)/);
  assert.deepEqual(linearizeTuples(result.source), { source: result.source, count: 0 });
  assert.deepEqual(linearizeTuples("construction Example;"), { source: "construction Example;", count: 0 });
});
