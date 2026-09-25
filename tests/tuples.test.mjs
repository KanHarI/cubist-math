import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/mathscript/parser.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";
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

test("tuple formatting preserves nested delimiters, comments, comparisons and patterns", () => {
  const source = `def build(a:Nat,b:Nat):Nat and Nat and Nat{exact (a, // saved
b,0);} def unpacked : Nat { obtain (a,b,c) := build(0,0); exact c; }
  def nested := typed((Nat and Nat) and Nat and Nat, ((0,1),2,3));
  def relation(a:Nat,b:Nat) := a < b;
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
    def build : (Nat and Nat) and Nat and Nat and Nat {
      exact ((0, 1), (2, // keep the tail note
        ((3, 4))));
    }
    def use : Nat { obtain ((a, b), (c, (d, e))) := build; exact e; }
    def call := f(a, b, c);
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

test("native tuple notation exposes its expansion and a checked inspector binding", async t => {
  const { default: createCubical } = await import("../web/dist/cubical.mjs");
  const { CubicalProgram } = await import("../web/cubical-program.mjs");
  const program = new CubicalProgram(await createCubical(), async () => "");
  t.after(() => program.dispose());
  const result = await program.check("def triple : Nat and Nat and Nat { exact (0, 1, 2); }", "tuples");
  assert.equal(result.complete, true);
  const links = result.links.filter(x => x.role === "tuple macro");
  assert.equal(links.length, 2);
  assert.equal(links[0].expansion, "(0, (1, 2))");
  assert.equal(program.inspect(links[0].binding).expression.tag, "Pair");
  const invalid = await program.check("def wrong : Nat and Nat { exact (0, 1, 2); }", "wrong");
  assert.equal(invalid.complete, false);
});
