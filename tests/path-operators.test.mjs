import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse, tokenize } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";

// Path operators: ~p reverses a path, as sym(p) does; p ++ q concatenates two
// paths, as trans(p, q) does. Coordinate operators: ~i reverses a coordinate,
// as flip(i) does; i & j is their meet and i | j their join, as meet(i, j) and
// join(i, j) are. Each elaborates through the same code as its built-in form.
// The kernel inspector still prints formulas with ∧ and ∨.
// How the operators elaborate, and their refusals, are
// cubist-tests/path_operators.cubist (tests/cubist-tests.test.mjs); here,
// how they parse and format.
// An expression's grouping, fully parenthesized.
const grouping = source => {
  const show = n => n.kind === "binary" || n.kind === "pathApply" ? `(${show(n.left)} ${n.operator} ${show(n.right)})`
    : n.kind === "unary" ? `(~${show(n.operand)})`
    : n.kind === "call" ? `${show(n.fn)}(${n.args.map(show).join(", ")})` : n.name ?? String(n.value);
  return show(parse(source, true));
};

test("~p binds tighter than @, and ++ associates to the left between + and =", () => {
  assert.equal(grouping("~p @ i"), "((~p) @ i)");
  assert.equal(grouping("p @ ~i"), "(p @ (~i))");
  assert.equal(grouping("p ++ q ++ r"), "((p ++ q) ++ r)");
  assert.equal(grouping("~p ++ q = r"), "(((~p) ++ q) = r)");
  assert.equal(grouping("a + b ++ c"), "((a + b) ++ c)");
  assert.equal(grouping("~f(x) ++ g(y)"), "((~f(x)) ++ g(y))");
  assert.equal(grouping("x -> ~p"), "(x -> (~p))");
  assert.equal(grouping("~~p"), "(~(~p))");
  // (~p) @ i and p @ ~i are the same point.
  assert.equal(grouping("(~p) @ i"), "((~p) @ i)");
});

test("prefix - no longer reverses: the message names ~", () => {
  for (const source of ["-p", "p @ -i", "~p ++ -q", "- -p"])
    assert.throws(() => parse(source, true), /^Error: Reversal is written ~: ~p reverses a path and ~i a coordinate\. Prefix - is kept for arithmetic\.$/);
  // A truncation level's sign is not a reversal.
  assert.doesNotThrow(() => parse("inductive T(U < UU0, A : U) : trunc(-1) U { c; }"));
});

test("& binds tighter than |, and both tighter than @", () => {
  assert.equal(grouping("p @ i & j"), "(p @ (i & j))");
  assert.equal(grouping("p @ i & j | k"), "(p @ ((i & j) | k))");
  assert.equal(grouping("p @ i | j & k"), "(p @ (i | (j & k)))");
  assert.equal(grouping("p @ ~i & j"), "(p @ ((~i) & j))");
  assert.equal(grouping("p @ ~(i | j)"), "(p @ (~(i | j)))");
  assert.equal(grouping("~p @ i | j"), "((~p) @ (i | j))");
  assert.throws(() => tokenize("p @ i \u2227 j"), /Unexpected character/);
  assert.throws(() => tokenize("p @ i \u2228 j"), /Unexpected character/);
});

test("++ is two ASCII plus signs; the look-alike double plus is not a token", () => {
  assert.deepEqual(tokenize("p ++ q").slice(0, 3).map(token => token.text), ["p", "++", "q"]);
  assert.throws(() => tokenize("p ⧺ q"), /Unexpected character/);
});

test("the formatter writes ~p and ~i tight and spaces ++, & and |", () => {
  const formatted = formatCubist("def f(A : U0, x, y, z : A, p : y = x, q : y = z) : x = z := ~ p++q;\n");
  assert.match(formatted, /:= ~p \+\+ q;/);
  assert.match(formatCubist("def g(A : U0, x, y : A, p : x = y) : y = x := path i => p @ ~ i&1|0;\n"),
    /p @ ~i & 1 \| 0;/);
  assert.match(formatCubist("def h(A : U0, x, y : A, p : x = y) : x = y := ~ ~p;\n"), /:= ~~p;/);
});
