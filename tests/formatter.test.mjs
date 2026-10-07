import test from "node:test";
import assert from "node:assert/strict";
import { readdir, readFile } from "node:fs/promises";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { parse, tokenize } from "../web/cubist/parser.mjs";

const semantic = value => JSON.parse(JSON.stringify(value, (key, v) =>
  ["start", "end", "operatorStart", "operatorEnd", "definitionStart", "modifierStart", "valueStart", "valueEnd", "tupleStart", "tupleEnd", "open", "close"].includes(key) ? undefined : v));
test("formatting every bundled source preserves tokens, comments, syntax and is idempotent", async () => {
  const directory = new URL("../archive/first-library/", import.meta.url);
  for (const name of (await readdir(directory)).filter(n => n.endsWith(".cubist"))) {
    const source = await readFile(new URL(name, directory), "utf8");
    const formatted = formatCubist(source);
    assert.equal(formatCubist(formatted), formatted, name + " idempotence");
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
def equality := 0 =[Nat] 0; // keep this comment
`;
  const formatted = formatCubist(source, { printWidth: 40 });
  assert.match(formatted, /x, \/\/ first component\n\s+x/);
  assert.match(formatted, /0\s+=\[Nat\] 0;/);
  assert.deepEqual(semantic(parse(formatted)), semantic(parse(source)));
  assert.equal(formatCubist(formatted, { printWidth: 40 }), formatted);
});

test("projections stay tight, and a let states a type and proves it in a block", () => {
  const source = `def swap(A,B:U0,p:A and B):B and A:=(p.2,p.1);
def nested(t:Nat and Nat and Nat,f:Nat->Nat and Nat):Nat:=f(t.2.1).2;
def reduce(A,B:U0,a:A,f:A->B):B{let y:A:=a;exact f(y);}
def block(A,B:U0,a:A,f:A->B):B{let x:A{exact a;}exact f(x);}
`;
  const formatted = formatCubist(source);
  assert.match(formatted, /:= \(p\.2, p\.1\);/);
  assert.match(formatted, /f\(t\.2\.1\)\.2;/);
  assert.match(formatted, /\n  let y : A := a;\n  exact f\(y\);\n/);
  assert.match(formatted, /\n  let x : A \{\n    exact a;\n  \}\n  exact f\(x\);\n/);
  assert.deepEqual(semantic(parse(formatted)), semantic(parse(source)));
  assert.equal(formatCubist(formatted), formatted);
});

test("a projection of a block expression keeps its dot on the closing brace", () => {
  const source = `def a(n : Nat) : Nat := induction n as k return Nat and Nat { zero => (0, 0); succ h => h; }.1;
def b(v : Unit or Unit) : Nat := match v return Nat and Nat { left x => (0, 0); right y => (1, 1); }.2;
def c(p : Nat and Nat) : Nat := unpack p as (x, y) return Nat and Nat { (y, x); }.1;
def d(n : Nat, v : Unit or Unit) : Nat and Nat := (induction n as k return Nat and Nat { zero => (0, 0); succ h => h; }.1,
  match v return Nat and Nat { left x => (0, 0); right y => (1, 1); }.2);
`;
  const formatted = formatCubist(source);
  assert.equal(formatted.match(/\n *\}\.[12][;,)]/g)?.length, 5, formatted);
  assert.doesNotMatch(formatted, /\}\s+\./);
  assert.deepEqual(semantic(parse(formatted)), semantic(parse(source)));
  assert.equal(formatCubist(formatted), formatted);
});

test("invalid input is rejected instead of rewritten", () => {
  assert.throws(() => formatCubist("def x := (0;"));
  assert.throws(() => formatCubist("def x := 0;", { printWidth: 0 }));
});

test("top-level declarations have blank lines and documentation stays together", () => {
  const source = `import logic;
def first := 0; // trailing
// Second declaration.
// Its documentation continues.
def second := 1;
def same : 0 = 0 { exact refl(0); }
def last := 2;`;
  const formatted = formatCubist(source);
  assert.match(formatted, /first := 0; \/\/ trailing\n\n\/\/ Second declaration\.\n\/\/ Its documentation continues\.\ndef second/);
  assert.match(formatted, /second := 1;\n\ndef same/);
  assert.match(formatted, /}\n\ndef last/);
  assert.equal(formatCubist(formatted), formatted);
});

test("annotated definition equalities indent the type without indenting the proof body", () => {
  const source = `def vector_scale_add_vectors(K : AlgebraicField, V : VectorSpace(K)) :
    forall a : af_carrier(K). forall x : vector_carrier(K, V). forall y : vector_carrier(K, V).
    vector_scale(K, V, a, vector_add(K, V, x, y)) = vector_add(K, V, vector_scale(K, V, a, x), vector_scale(K, V, a, y)) {
      obtain (one, assoc, vectors, scalars) := vector_scalar_laws(K, V); exact vectors;
    }`;
  for (const width of [60, 100, 140]) {
    const formatted = formatCubist(source, { printWidth: width });
    assert.match(formatted, /\n  forall a/);
    assert.match(formatted, /\n  obtain /);
    assert.match(formatted, /\n  exact vectors;\n}\n$/);
    assert.doesNotMatch(formatted, /\n(?:forall|vector_scale|vector_add)/);
    assert.equal(formatCubist(formatted, { printWidth: width }), formatted);
    assert.deepEqual(semantic(parse(formatted)), semantic(parse(source)));
  }
});

test("long quantified statements pack short binders and preserve function domains", () => {
  const source = "def CantorSchroederBernstein := forall A : U0. forall B : U0. IsSet(A) -> IsSet(B) -> forall f : A -> B. forall g : B -> A. Injective(A, B, f) -> Injective(B, A, g) -> Equiv(U0, A, B);";
  const formatted = formatCubist(source);
  assert.equal(formatted, `def CantorSchroederBernstein :=
  forall A : U0. forall B : U0. IsSet(A) -> IsSet(B) -> forall f : A -> B. forall g : B -> A.
  Injective(A, B, f) -> Injective(B, A, g) -> Equiv(U0, A, B);
`);
  for (const width of [60, 80, 100]) {
    const output = formatCubist(source, { printWidth: width });
    assert.match(output, /forall f : A -> B/);
    assert.match(output, /forall g : B -> A/);
    assert.equal(formatCubist(output, { printWidth: width }), output);
  }
});

test("the formatter automatically linearizes tuples while preserving their expanded AST", async () => {
  const { expandedSyntax } = await import("../web/cubist/tuples.mjs");
  const source = "def triple : Nat and Nat and Nat { exact (0, (1, 2)); }";
  const formatted = formatCubist(source);
  assert.match(formatted, /exact \(0, 1, 2\);/);
  assert.equal(expandedSyntax(parse(formatted)), expandedSyntax(parse(source)));
  assert.equal(formatCubist(formatted), formatted);
  assert.match(formatCubist(source, { linearizeTuples: false }), /exact \(0, \(1, 2\)\);/);
});

test("lambda binder groups are one comma-separated list; separate groups are rejected", () => {
  const formatted = formatCubist("def f(F : Nat -> Nat -> U0) := fun (a : Nat,b : F(0)(1)) => a;\n");
  assert.match(formatted, /fun \(a : Nat, b : F\(0\)\(1\)\) => a;/);
  assert.throws(() => parse("def f := fun (a : Nat) (b : Nat) => a;"), /Separate binder groups with commas/);
});

test("a keyword keeps its space before a parenthesis; the reserved words written as calls are tight", () => {
  assert.equal(formatCubist("def p : Nat and Nat := (1, 2);\n\nevaluate(p) expecting(1, _);\n"),
    "def p : Nat and Nat := (1, 2);\n\nevaluate (p) expecting (1, _);\n");
  assert.match(formatCubist("def m(n : Nat) : Nat := match(n) { zero => n; succ(k) => k; };\n"), /:= match \(n\) \{/);
  assert.equal(formatCubist("def f := fun(n : Nat) => n;\n"), "def f := fun (n : Nat) => n;\n");
  // left(a), right(b), typed(T, e) and print's evaluate(e) are calls.
  assert.equal(formatCubist("def s : Unit or Nat := typed (Unit or Nat, left (tt));\n\nprint(evaluate (s));\n"),
    "def s : Unit or Nat := typed(Unit or Nat, left(tt));\n\nprint(evaluate(s));\n");
});

test("an empty block is {} on its declaration's line", () => {
  assert.equal(formatCubist("theory AbelianGroup(U < UU0) extends Group, CommMonoid {\n\n}\n"),
    "theory AbelianGroup(U < UU0) extends Group, CommMonoid {}\n");
  // A comment is no empty body.
  assert.equal(formatCubist("theory Later(U < UU0) extends Group {\n  // nothing yet\n}\n"),
    "theory Later(U < UU0) extends Group {\n  // nothing yet\n}\n");
});

test("a long value ending in brackets breaks inside them, its definition on one line", () => {
  const fields = "M := Nat, M_is_set := nat_is_set, mul := add, mul_assoc := nat_add_assoc, one := zero";
  assert.equal(formatCubist(`def additive : Monoid(U0) := Monoid.make(${fields}, one_mul := nat_zero_add);\n`),
    `def additive : Monoid(U0) := Monoid.make(\n  ${fields},\n  one_mul := nat_zero_add\n);\n`);
  // A value that fits on a line of its own goes there, whole.
  assert.equal(formatCubist("computable def same_ratio_props(f, g : Fraction) : IsProp(U, SameRatio(f, g)) := R_is_set(f.1 * g.2.1, g.1);\n"),
    "computable def same_ratio_props(f, g : Fraction) :\n  IsProp(U, SameRatio(f, g)) := R_is_set(f.1 * g.2.1, g.1);\n");
});
