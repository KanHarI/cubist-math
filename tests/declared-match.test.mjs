// match on declared types, work-plan L2.2a: clauses elaborated against the
// clause types the kernel computes, dependent motives, path and squash
// clauses, structural recursion, the refusals, and the H1 release fixture:
// the circle's winding number, computed through univalence.
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

const module = await createCubical();
async function check(t, source) {
  const program = new CubicalProgram(module, sourceReader(), { experimental: ["h1"] });
  t.after(() => program.dispose());
  const result = await program.check(source, "main");
  return { result, get: name => {
    const found = result.outputs.find(output => output.name === name);
    assert.ok(found, `no declaration ${name}`);
    return found;
  } };
}
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};

const naturals = `inductive N { zero; succ(n : N); }
def add(n, m : N) : N := match n { zero => m; succ(k) => succ(add(k, m)); };
`;

test("structural recursion computes, with a parameter held fixed", async t => {
  const { get } = await check(t, `${naturals}
def double(n : N) : N := match n { zero => zero; succ(m) => succ(succ(double(m))); };
def four : double(succ(succ(zero))) = succ(succ(succ(succ(zero)))) { rfl; }
def three : add(succ(succ(zero)), succ(zero)) = succ(succ(succ(zero))) { rfl; }
def wrong : double(succ(zero)) = succ(zero) { rfl; }
`);
  for (const name of ["add", "double", "four", "three"]) ok(get(name));
  refused(get("wrong"), /./);
});

test("a dependent motive: each clause is checked at its own instance", async t => {
  const { get } = await check(t, `${naturals}
def zero_right(n : N) : add(n, zero) = n := match n as k return add(k, zero) = k {
  zero => refl(zero);
  succ(m) => cong(succ, zero_right(m));
};
`);
  ok(get("zero_right"));
});

test("data before positions: clauses name arguments in the order declared", async t => {
  const { get } = await check(t, `${naturals}
inductive Tree(U < UU0, A : U) { leaf; node(l : Tree(U, A), a : A, r : Tree(U, A)); }
def size(A : U0, t : Tree(U0, A)) : N := match t { leaf => zero; node(l, a, r) => succ(add(size(A, l), size(A, r))); };
def labels(t : Tree(U0, N)) : N := match t { leaf => zero; node(l, a, r) => add(a, add(labels(l), labels(r))); };
def small : Tree(U0, N) := node(node(leaf, succ(zero), leaf), zero, leaf);
def two : size(N, small) = succ(succ(zero)) { rfl; }
def one : labels(small) = succ(zero) { rfl; }
`);
  for (const name of ["size", "labels", "two", "one"]) ok(get(name));
});

test("a path constructor's clause is a path between the clauses at its ends", async t => {
  const { get } = await check(t, `${naturals}
inductive Circle { base; loop : base = base; }
def flat(x : Circle) : N := match x { base => zero; loop i => zero; };
def at_loop : flat(loop @ 1) = zero { rfl; }
def torn(x : Circle) : N := match x { base => zero; loop i => succ(zero); };
def unnamed(x : Circle) : N := match x { base => zero; loop => zero; };
def extra(x : Circle) : N := match x { base i => zero; loop i => zero; };
`);
  ok(get("flat"));
  ok(get("at_loop"));
  refused(get("torn"), /mismatch|clause/i);
  refused(get("unnamed"), /loop is a path constructor: name its 1 dimension after its arguments/);
  refused(get("extra"), /base has no dimensions to name/);
});

test("a truncation's squash clause, with T.squash and recursive results", async t => {
  const { get } = await check(t, `${naturals}
inductive Trunc(U < UU0, A : U) : prop { point(a : A); }
def same(x, y : Trunc(U0, N)) : x = y := Trunc.squash(x, y);
def rebuilt(t : Trunc(U0, N)) : Trunc(U0, N) := match t {
  point(a) => point(a);
  squash(x, y) i => Trunc.squash(rebuilt(x), rebuilt(y)) @ i;
};
def rebuilt_point : rebuilt(point(zero)) = point(zero) { rfl; }
def unsquashed(t : Trunc(U0, N)) : Trunc(U0, N) := match t { point(a) => point(a); };
`);
  for (const name of ["same", "rebuilt", "rebuilt_point"]) ok(get(name));
  refused(get("unsquashed"), /Give the squash clause, .*generated squash clauses come with automatic clauses \(L2\.2b\)/);
});

test("the refusals name the clause or the call", async t => {
  const { get } = await check(t, `${naturals}
def unknown(n : N) : N := match n { zero => zero; succ(m) => m; tail(x) => x; };
def twice(n : N) : N := match n { zero => zero; zero => zero; succ(m) => m; };
def partial(n : N) : N := match n { zero => zero; };
def arity(n : N) : N := match n { zero => zero; succ => zero; };
def growing(n : N) : N := match n { zero => zero; succ(m) => growing(succ(m)); };
def moving(n, m : N) : N := match n { zero => m; succ(k) => moving(k, succ(m)); };
def outside(n : N) : N := add(outside(n), match n { zero => zero; succ(m) => m; });
def untyped(n : N) := match n { zero => zero; succ(m) => m; };
def on_nat(n : Nat) : Nat := match n { zero => zero; succ(m) => m; };
`);
  refused(get("unknown"), /N has no constructor tail: its constructors are zero, succ/);
  refused(get("twice"), /zero has two clauses/);
  refused(get("partial"), /match on N needs a clause for succ/);
  refused(get("arity"), /succ takes 1 argument here/);
  refused(get("growing"), /not on an argument of the matched constructor: only structural recursion/);
  refused(get("moving"), /passes its other arguments unchanged: here m/);
  refused(get("outside"), /outside is being defined: it can call itself only on an argument of a constructor/);
  refused(get("untyped"), /match needs its result's type/);
  refused(get("on_nat"), /match requires a value of a declared type, or of a sum/);
});

test("the H1 release fixture: the circle's winding number computes through univalence", async t => {
  const source = await readFile(new URL("../docs/examples/h1/winding.cubist", import.meta.url), "utf8");
  const { result, get } = await check(t, source);
  for (const name of ["succ_equiv", "code", "winding", "winding_loop", "winding_twice", "winding_back", "code_on_loop"]) {
    ok(get(name));
    assert.deepEqual(get(name).extensions, ["H1"]);
    assert.deepEqual(get(name).axioms, [], `${name} uses no assumption: it computes`);
  }
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value),
    ["pos(succ(zero))", "pos(succ(succ(succ(zero))))", "pos(zero)"]);
  assert.ok(result.complete);
});

test("recursion recognizes the declaration's own parameter by its binder, not by its name", async t => {
  const { get } = await check(t, `${naturals}
def tricky(n : N) : N := (fun (n : N) => match n return N { zero => zero; succ(m) => tricky(m); })(zero);
def shadowed(n : N) : N := match n { zero => zero; succ(n) => shadowed(n); };
`);
  // The inner n is another variable: a call there is not recursion on it.
  refused(get("tricky"), /tricky is being defined: it can call itself only on an argument of a constructor/);
  // A clause may name its argument as the parameter was named.
  ok(get("shadowed"));
});

test("recursion only where the match is the whole body, and with the matched parameter rebound", async t => {
  const { get } = await check(t, `${naturals}
def wrapped(n : N) : N := succ(match n return N { zero => zero; succ(k) => wrapped(k); });
def captured(n : N) : N := match n { zero => n; succ(k) => captured(k); };
def constant_zero : captured(succ(succ(zero))) = zero { rfl; }
def not_identity : captured(succ(zero)) = succ(zero) { rfl; }
def via_block(n : N) : N { exact match n { zero => zero; succ(k) => via_block(k); }; }
def via_value(n : N) := match n return N { zero => zero; succ(k) => via_value(k); };
`);
  // Around the match, a call's recursive result would omit the succ.
  refused(get("wrapped"), /wrapped is being defined: it can call itself only on an argument of a constructor/);
  // n in the zero clause is zero there, on every recursive call: f is constant zero.
  for (const name of ["captured", "constant_zero", "via_block", "via_value"]) ok(get(name));
  refused(get("not_identity"), /./);
});

test("a clause's own names shadow the declaration's name and its matched parameter", async t => {
  const { get } = await check(t, `${naturals}
def f(n : N) : N := match n { zero => zero; succ(f) => f; };
def predecessor : f(succ(succ(zero))) = succ(zero) { rfl; }
def g(n : N) : N := match n { zero => zero; succ(n) => n; };
def also_predecessor : g(succ(succ(zero))) = succ(zero) { rfl; }
`);
  for (const name of ["f", "predecessor", "g", "also_predecessor"]) ok(get(name));
});

test("the formatter keeps a qualified name's dot tight", async () => {
  const { formatMathScript } = await import("../web/mathscript/formatter.mjs");
  const source = "def same(x, y : Trunc(U0, Nat)) : x = y := Trunc.squash(x, y);\n";
  const formatted = formatMathScript(source);
  assert.match(formatted, /Trunc\.squash\(x, y\)/);
  assert.equal(formatMathScript(formatted), formatted);
});

test("nested legacy matches are walked once: parsing and formatting stay linear", async () => {
  const { parse } = await import("../web/mathscript/parser.mjs");
  const { formatMathScript } = await import("../web/mathscript/formatter.mjs");
  let body = "0";
  for (let depth = 0; depth < 40; depth++) body = `match x return Nat { left a => ${body}; right b => 0; }`;
  const source = `def deep(x : Nat or Nat) : Nat := ${body};\n`;
  const started = performance.now();
  const match = parse(source).declarations[0].body[0].value;
  assert.ok(match.leftBody && match.clauses.length === 2, "the legacy fields and the clauses are both there");
  assert.ok(!Object.keys(match).includes("clauses"), "the legacy shape's clauses are not enumerated");
  formatMathScript(source);
  assert.ok(performance.now() - started < 5000, "a doubled walk would take 2^40 steps");
});

test("recursive calls are the calls written: their types, arities and arguments", async t => {
  const { get } = await check(t, `${naturals}
inductive Tag(n : N) : U0 { tag; }
def tagged(n : N) : Tag(n) := match n { zero => tag; succ(m) => tagged(m); };
def outer_motive(n : N) : Tag(n) := match n as z return Tag(n) { zero => tag; succ(m) => outer_motive(m); };
def refl_all(n : N) : n = n := match n { zero => refl(zero); succ(m) => refl(succ(m)); };
def applied(n : N) : N -> N := match n { zero => fun (x : N) => x; succ(m) => fun (x : N) => applied(m(x)); };
def dep(n : N, p : n = zero) : N := match n { zero => zero; succ(m) => dep(m, p); };
def f(f : N -> N, n : N) : N := match n { zero => f(zero); succ(m) => f(m); };
def shadowed_by_parameter : f(succ, succ(succ(zero))) = succ(succ(zero)) { rfl; }
`);
  // tagged(m) has type Tag(m), not Tag(n): the succ clause needs Tag(succ(m)).
  refused(get("tagged"), /mismatch/i);
  refused(get("outer_motive"), /The motive mentions n itself: write it over the matched value/);
  ok(get("refl_all"));
  refused(get("applied"), /m takes 0 arguments here, as an argument of the matched constructor/);
  refused(get("dep"), /passes p unchanged, but its type mentions n, which the call changes/);
  ok(get("f"));
  ok(get("shadowed_by_parameter"));
});

test("third review: a path of the matched type is recursed on at its dimensions", async t => {
  const { get } = await check(t, `${naturals}
inductive S : set { point; }
def ill_typed(s : S) : S := match s {
  point => point;
  squash(x, y, p, q) i j => S.squash(ill_typed(x), ill_typed(y), ill_typed(p), ill_typed(q)) @ i @ j;
};
def rebuilt(s : S) : S := match s {
  point => point;
  squash(x, y, p, q) i j => S.squash(rebuilt(x), rebuilt(y), path k => rebuilt(p @ k), path k => rebuilt(q @ k)) @ i @ j;
};
def rebuilt_point : rebuilt(point) = point { rfl; }
def too_many(s : S) : S := match s {
  point => point;
  squash(x, y, p, q) i j => S.squash(too_many(x @ i), too_many(y), path k => too_many(p @ k), path k => too_many(q @ k)) @ i @ j;
};
`);
  // p : x = y is not an S: too_many(p) would be ill-typed outside the definition.
  refused(get("ill_typed"), /p is a 1-dimensional path of the matched type, not an element: call ill_typed on it at its dimensions, as ill_typed\(p @ i\)/);
  ok(get("rebuilt"));
  ok(get("rebuilt_point"));
  refused(get("too_many"), /x is an element of the matched type, not a path/);
});

test("third review: a parameter that shadows its type's name still matches", async t => {
  const { get } = await check(t, `${naturals}
def count(N : N) : Nat := match N { zero => 0; succ(k) => count(k); };
def counted : count(succ(succ(zero))) = 0 { rfl; }
`);
  ok(get("count"));
  ok(get("counted"));
});
