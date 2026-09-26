import test from "node:test";
import assert from "node:assert/strict";
import { readdir, readFile } from "node:fs/promises";
import { formatMathScript } from "../web/mathscript/formatter.mjs";
import { parse, tokenize } from "../web/mathscript/parser.mjs";

const semantic = value => JSON.parse(JSON.stringify(value, (key, v) =>
  ["start", "end", "operatorStart", "operatorEnd", "definitionStart", "modifierStart", "valueStart", "valueEnd", "tupleStart", "tupleEnd"].includes(key) ? undefined : v));
test("formatting every bundled source preserves tokens, comments, syntax and is idempotent", async () => {
  const directory = new URL("../archive/first-library/", import.meta.url);
  for (const name of (await readdir(directory)).filter(n => n.endsWith(".cubist"))) {
    const source = await readFile(new URL(name, directory), "utf8");
    const formatted = formatMathScript(source);
    assert.equal(formatMathScript(formatted), formatted, name + " idempotence");
    assert.deepEqual(tokenize(formatted).map(t => t.text), tokenize(source).map(t => t.text), name);
    assert.deepEqual(formatted.match(/\/\/[^\r\n]*/g), source.match(/\/\/[^\r\n]*/g), name + " comments");
    if (tokenize(source)[0].text !== "construction")
      assert.deepEqual(semantic(parse(formatted)), semantic(parse(source)), name + " syntax tree");
    assert.doesNotMatch(formatted, /[ \t]+$/m, name + " trailing whitespace");
  }
});

test("nested pairs, equality carriers and line comments keep their boundaries", () => {
  const source = `// Header
def copy(A:U0,x:A):A and A{exact (x, // first component
x);}
def equality = 0 =[Nat] 0; // keep this comment
`;
  const formatted = formatMathScript(source, { printWidth: 40 });
  assert.match(formatted, /x, \/\/ first component\n\s+x/);
  assert.match(formatted, /0\s+=\[Nat\] 0;/);
  assert.deepEqual(semantic(parse(formatted)), semantic(parse(source)));
  assert.equal(formatMathScript(formatted, { printWidth: 40 }), formatted);
});

test("invalid input is rejected instead of rewritten", () => {
  assert.throws(() => formatMathScript("def x = (0;"));
  assert.throws(() => formatMathScript("def x = 0;", { printWidth: 0 }));
});

test("top-level declarations have blank lines and documentation stays together", () => {
  const source = `import logic;
def first = 0; // trailing
// Second declaration.
// Its documentation continues.
def second = 1;
def same : 0 = 0 { exact refl(0); }
def last = 2;`;
  const formatted = formatMathScript(source);
  assert.match(formatted, /first = 0; \/\/ trailing\n\n\/\/ Second declaration\.\n\/\/ Its documentation continues\.\ndef second/);
  assert.match(formatted, /second = 1;\n\ndef same/);
  assert.match(formatted, /}\n\ndef last/);
  assert.equal(formatMathScript(formatted), formatted);
});

test("annotated definition equalities indent the type without indenting the proof body", () => {
  const source = `def vector_scale_add_vectors(K : AlgebraicField, V : VectorSpace(K)) :
    forall a : af_carrier(K), forall x : vector_carrier(K, V), forall y : vector_carrier(K, V),
    vector_scale(K, V, a, vector_add(K, V, x, y)) = vector_add(K, V, vector_scale(K, V, a, x), vector_scale(K, V, a, y)) {
      obtain (one, assoc, vectors, scalars) = vector_scalar_laws(K, V); exact vectors;
    }`;
  for (const width of [60, 100, 140]) {
    const formatted = formatMathScript(source, { printWidth: width });
    assert.match(formatted, /\n  forall a/);
    assert.match(formatted, /\n  obtain /);
    assert.match(formatted, /\n  exact vectors;\n}\n$/);
    assert.doesNotMatch(formatted, /\n(?:forall|vector_scale|vector_add)/);
    assert.equal(formatMathScript(formatted, { printWidth: width }), formatted);
    assert.deepEqual(semantic(parse(formatted)), semantic(parse(source)));
  }
});

test("long quantified statements pack short binders and preserve function domains", () => {
  const source = "def CantorSchroederBernstein = forall A : U0, forall B : U0, IsSet(A) -> IsSet(B) -> forall f : A -> B, forall g : B -> A, Injective(A, B, f) -> Injective(B, A, g) -> Equiv(U0, A, B);";
  const formatted = formatMathScript(source);
  assert.equal(formatted, `def CantorSchroederBernstein =
  forall A : U0, forall B : U0, IsSet(A) -> IsSet(B) -> forall f : A -> B, forall g : B -> A,
  Injective(A, B, f) -> Injective(B, A, g) -> Equiv(U0, A, B);
`);
  for (const width of [60, 80, 100]) {
    const output = formatMathScript(source, { printWidth: width });
    assert.match(output, /forall f : A -> B/);
    assert.match(output, /forall g : B -> A/);
    assert.equal(formatMathScript(output, { printWidth: width }), output);
  }
});

test("the formatter automatically linearizes tuples while preserving their expanded AST", async () => {
  const { expandedSyntax } = await import("../web/mathscript/tuples.mjs");
  const source = "def triple : Nat and Nat and Nat { exact (0, (1, 2)); }";
  const formatted = formatMathScript(source);
  assert.match(formatted, /exact \(0, 1, 2\);/);
  assert.equal(expandedSyntax(parse(formatted)), expandedSyntax(parse(source)));
  assert.equal(formatMathScript(formatted), formatted);
  assert.match(formatMathScript(source, { linearizeTuples: false }), /exact \(0, \(1, 2\)\);/);
});

test("lambda binder groups are one comma-separated list; separate groups are rejected", () => {
  const formatted = formatMathScript("def f(F : Nat -> Nat -> U0) = fun (a : Nat,b : F(0)(1)) => a;\n");
  assert.match(formatted, /fun \(a : Nat, b : F\(0\)\(1\)\) => a;/);
  assert.throws(() => parse("def f = fun (a : Nat) (b : Nat) => a;"), /Separate binder groups with commas/);
});
