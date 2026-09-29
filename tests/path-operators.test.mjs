import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { parse, tokenize } from "../web/mathscript/parser.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";

// Path operators: -p reverses a path, as sym(p) does; p ++ q concatenates two
// paths, as trans(p, q) does. Coordinate operators: -i reverses a coordinate,
// as flip(i) does; i & j is their meet and i | j their join, as meet(i, j) and
// join(i, j) are. Each elaborates through the same code as its built-in form.
// The kernel inspector still prints formulas with ∧ and ∨.
const module = await createCubical();
const readArchive = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
async function check(t, source, name = "operators") {
  const program = new CubicalProgram(module, readArchive);
  t.after(() => program.dispose());
  const result = await program.check(source, name);
  return Object.fromEntries(result.outputs.map(output => [output.name, output.verified ? true : output.reason]));
}
const accepted = verdicts => assert.ok(Object.values(verdicts).every(verdict => verdict === true), JSON.stringify(verdicts, null, 1));
// An expression's grouping, fully parenthesized.
const grouping = source => {
  const show = n => n.kind === "binary" || n.kind === "pathApply" ? `(${show(n.left)} ${n.operator} ${show(n.right)})`
    : n.kind === "unary" ? `(-${show(n.operand)})`
    : n.kind === "call" ? `${show(n.fn)}(${n.args.map(show).join(", ")})` : n.name ?? String(n.value);
  return show(parse(source, true));
};

test("-p binds tighter than @, and ++ associates to the left between + and =", () => {
  assert.equal(grouping("-p @ i"), "((-p) @ i)");
  assert.equal(grouping("p @ -i"), "(p @ (-i))");
  assert.equal(grouping("p ++ q ++ r"), "((p ++ q) ++ r)");
  assert.equal(grouping("-p ++ q = r"), "(((-p) ++ q) = r)");
  assert.equal(grouping("a + b ++ c"), "((a + b) ++ c)");
  assert.equal(grouping("-f(x) ++ g(y)"), "((-f(x)) ++ g(y))");
  assert.equal(grouping("x -> -p"), "(x -> (-p))");
  assert.equal(grouping("- -p"), "(-(-p))");
});

test("& binds tighter than |, and both tighter than @", () => {
  assert.equal(grouping("p @ i & j"), "(p @ (i & j))");
  assert.equal(grouping("p @ i & j | k"), "(p @ ((i & j) | k))");
  assert.equal(grouping("p @ i | j & k"), "(p @ (i | (j & k)))");
  assert.equal(grouping("p @ -i & j"), "(p @ ((-i) & j))");
  assert.equal(grouping("p @ -(i | j)"), "(p @ (-(i | j)))");
  assert.equal(grouping("-p @ i | j"), "((-p) @ (i | j))");
  assert.throws(() => tokenize("p @ i \u2227 j"), /Unexpected character/);
  assert.throws(() => tokenize("p @ i \u2228 j"), /Unexpected character/);
});

test("++ is two ASCII plus signs; the look-alike double plus is not a token", () => {
  assert.deepEqual(tokenize("p ++ q").slice(0, 3).map(token => token.text), ["p", "++", "q"]);
  assert.throws(() => tokenize("p ⧺ q"), /Unexpected character/);
});

test("-p, p ++ q and -i elaborate as sym, trans and flip do", async t => {
  const verdicts = await check(t, `
    def inverse(A : U0, x, y : A, p : x = y) : y = x := -p;
    def concatenation(A : U0, x, y, z : A, p : x = y, q : y = z) : x = z := p ++ q;
    def three(A : U0, w, x, y, z : A, p : w = x, q : x = y, r : y = z) : w = z := p ++ q ++ r;
    def mixed(A : U0, x, y, z : A, p : y = x, q : y = z) : x = z := -p ++ q;
    def reversed(A : U0, x, y : A, p : x = y) : y = x := path i => p @ -i;
    def twice(A : U0, x, y : A, p : x = y) : x = y := - -p;
    def inverse_is_sym(A : U0, x, y : A, p : x = y) : -p = sym(p) := refl(sym(p));
    def concatenation_is_trans(A : U0, x, y, z : A, p : x = y, q : y = z) : p ++ q = trans(p, q) := refl(trans(p, q));
    def left_nested(A : U0, w, x, y, z : A, p : w = x, q : x = y, r : y = z)
      : p ++ q ++ r = trans(trans(p, q), r) := refl(trans(trans(p, q), r));
    def coordinate(A : U0, x, y : A, p : x = y) : p @ -0 = y := refl(y);
    // The connection of the reference's cubical chapter, both ways.
    def to_start(A : U0, x, y : A, p : x = y) : PathP(fun (j : Interval) => x = p @ j, refl(x), p)
      := path j => path i => p @ i & j;
    def to_end(A : U0, x, y : A, p : x = y) : PathP(fun (j : Interval) => p @ j = y, p, refl(y))
      := path j => path i => p @ i | j;
    def meet_is_meet(A : U0, x, y : A, p : x = y) : PathP(fun (j : Interval) => x = p @ j, refl(x), p)
      := path j => path i => p @ meet(i, j);
    def same_square(A : U0, x, y : A, p : x = y) : to_start(A, x, y, p) = meet_is_meet(A, x, y, p)
      := refl(to_start(A, x, y, p));
    def reversed_meet(A : U0, x, y : A, p : x = y) : y = x := path i => p @ -(i & 1) | 0;
    // The operators do not depend on what the names sym and trans mean here.
    def shadowed(A : U0, x, y : A, p : x = y, sym : Nat, trans : Nat) : y = x := -p ++ refl(x) ++ p ++ -p;
  `);
  accepted(verdicts);
});

test("the operators on a non-path say which operator failed", async t => {
  const verdicts = await check(t, `
    def negated(n : Nat) : Nat := -n;
    def appended(n, m : Nat) : Nat := n ++ m;
    def unmatched(A : U0, x, y, z : A, p : x = y, q : x = z) : x = z := p ++ q;
    def conjunction(n, m : Nat) : Nat := n & m;
  `);
  assert.match(String(verdicts.conjunction), /& combines interval coordinates/);
  assert.match(String(verdicts.negated), /-p reverses a path/);
  assert.match(String(verdicts.appended), /p \+\+ q concatenates paths/);
  assert.match(String(verdicts.unmatched), /Path endpoints do not match/);
});

test("the formatter writes -p and -i tight and spaces ++, & and |", () => {
  const formatted = formatMathScript("def f(A : U0, x, y, z : A, p : y = x, q : y = z) : x = z := - p++q;\n");
  assert.match(formatted, /:= -p \+\+ q;/);
  assert.match(formatMathScript("def g(A : U0, x, y : A, p : x = y) : y = x := path i => p @ - i&1|0;\n"),
    /p @ -i & 1 \| 0;/);
});
