import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";

// The value form of `evaluate e` and `print(evaluate(e))` is computed by the
// kernel's head queries (valueForm in web/translator/evaluation.mjs), as
// `!`, `!!`, `!!!`, patterns and exact expected values are: closures,
// higher sorts, binary numbers, the contracts and the library's Euclid
// here, and where the kernel's queries stop. Every construct of the
// language is evaluated in tests/evaluation-demand-marks.test.mjs.
const module = await createCubical();

const outcomes = result => [...result.prints.map(print => [print.start, print.text]),
  ...result.gaps.filter(gap => gap.directive).map(gap => [gap.declarationStart, `${gap.code}: ${gap.reason.replace(/ at \d+:\d+$/, "")}`])]
  .sort(([a], [b]) => a - b).map(([, outcome]) => outcome);
// Each head query a value form asks spends a query of its print's fuel.
const fuel = result => result.directiveFuel.filter(directive => directive.kind === "print").map(directive => directive.searchFuel.queries);

// The value forms of a source's prints, each of which must compute.
async function printed(t, source, { reader = sourceReader(), options = {} } = {}) {
  const program = new CubicalProgram(module, reader, options);
  t.after(() => program.dispose());
  const result = await program.check(source, "main");
  assert.deepEqual(result.gaps.filter(gap => gap.directive).map(gap => gap.reason), []);
  return result.prints.map(print => print.text);
}
const each = terms => terms.map(term => `print(evaluate(${term}));`).join("\n");

// The same call written twice in a function's body, through 24 definitions:
// the kernel's weak-head cache shares each g_i(tt) by its syntax, so each
// g_i is computed once.
const duplicated = ["def both(a, b : Unit) : Unit := unit_induction(fun (x : Unit) => Unit, b, a);", "def g0(u : Unit) : Unit := u;",
  ...Array.from({ length: 24 }, (_, i) => `def g${i + 1}(u : Unit) : Unit := both(g${i}(u), g${i}(u));`)].join("\n");
// The same call relayed: g_(i + 1) calls g_i once itself and once through
// h_i, whose body calls it in an application of its own. The kernel's cache
// shares the two by their syntax once substituted, g_i(tt) both.
const relayed = ["def both(a, b : Unit) : Unit := unit_induction(fun (x : Unit) => Unit, b, a);", "def g0(u : Unit) : Unit := u;",
  ...Array.from({ length: 24 }, (_, i) => `def h${i}(u : Unit) : Unit := g${i}(u);\ndef g${i + 1}(u : Unit) : Unit := both(g${i}(u), h${i}(u));`)]
  .join("\n");

test("value forms keep capture and shadowing, and leave an unused argument uncomputed", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;
inductive Flag : U0 {
  disabled;
  enabled;
}
inductive Circle : U0 {
  base;
  loop : base = base;
}
${relayed}
def capture : Flag := (fun (x : Flag) => (fun (f : Flag -> Flag) => (fun (x : Flag) => f(x))(disabled))(fun (y : Flag) => x))(enabled);
def unused_path : Unit := (fun (p : tt = tt) => tt)(refl(tt));
def unused_work : Unit := (fun (u : Unit) => tt)(g24(tt));
def single : UNat := 2 * 255;
def shared : UNat and UNat := (fun (x : UNat) => typed(UNat and UNat, (x, x)))(2 * 255);
print(evaluate(capture));
print(evaluate(unused_path));
print(evaluate(unused_work));
print(evaluate(single));
print(evaluate(shared));
print(evaluate(typed(Unit and Circle, (tt, base))));
`, { module });
  assert.deepEqual(outcomes(result), ["enabled", "tt", "tt", "510", "(510, 510)", "(tt, base)"]);
  // g24(tt), the unused argument, is never asked for: the print spends two
  // queries, the term's evaluation and one head query.
  assert.equal(fuel(result)[2], 2);
});

// The point constructors of any declared type, higher or truncated too, and
// their eliminators' clauses for them, compute as the kernel's iota does. A
// path constructor at an endpoint computes to its boundary, and an
// eliminator applied to a transported value stops at a composition.
test("value forms of the points and paths of a quotient, a circle and a truncation", async t => {
  const texts = await printed(t, `import quotients;
import h1_truncation;
use unat;
inductive Circle : U0 {
  base;
  loop : base = base;
}
inductive Gpd(A : U0) : trunc(1) {
  gpoint(a : A);
}
def reverse(c : Circle) : Circle := match c {
  base => base;
  loop @ i => loop @ ~i;
};
def R(m, n : UNat) : U0 := Unit;
def three : Quotient(U0, UNat, R) := class(3);
def doubled(q : Quotient(U0, UNat, R)) : Quotient(U0, UNat, R) := match q {
  class(a) => class(a + a);
} obligations by (fun (a, b : UNat, r : R(a, b)) => class_path(U0, UNat, R, a + a, b + b, tt));
${each([
  "three", "base", "typed(Quotient(U0, UNat, R) and Unit, (three, tt))", "typed(UNat and Unit, (3, tt))",
  "reverse(base)", "doubled(three)", "merely(U0, UNat, 3)",
  "mere_map(U0, U0, UNat, UNat, fun (n : UNat) => n + 1, point(3))", "typed(Gpd(UNat), gpoint(2))",
  "loop", "class_path(U0, UNat, R, 1, 3, tt)", "typed(Unit and Quotient(U0, UNat, R), (tt, doubled(three)))",
  "Trunc.squash(typed(Trunc(U0, UNat), point(1)), typed(Trunc(U0, UNat), point(2)))",
  "loop @ 0", "reverse(loop @ 1)", "doubled(class_path(U0, UNat, R, 1, 3, tt) @ 0)",
  "typed(Trunc(U0, UNat), Trunc.squash(point(1), point(2)) @ 1)",
  "reverse(transport base along loop in (fun (c : Circle) => Circle))",
  "doubled(transport three along refl(tt) in (fun (u : Unit) => Quotient(U0, UNat, R)))",
])}
`);
  assert.deepEqual(texts, ["class(3)", "base", "(class(3), tt)", "(3, tt)", "base", "class(6)", "point(3)",
    "point(4)", "gpoint(2)", "loop", "relate(1, 3, tt)", "(tt, class(6))", "squash(point(1), point(2))",
    "base", "base", "class(2)", "point(2)", "<composition>", "<composition>"]);
});

// Binary integers and rationals are set quotients, of differences of binary
// naturals and of fractions over them: their arithmetic, inverses and
// decisions compute, with components past 64 and 128 bits, and inside
// pairs, sums and lists. A decision that finds two values equal holds the
// quotient's path constructor, shown with its fields.
test("binary integer and rational value forms", async t => {
  const wide = "340282366920938463463374607431768211455", q = (n, d) => `class((bnat.(${n}), bnat.(${d})))`;
  const fraction = (n, d) => `class((${n}, ${d}, <fun>))`;
  const texts = await printed(t, `import binary_rationals;
use binary_rationals;
${each([
  "2/3 + 1/6", "(-2/3) * (-3/2)", "bq_inv(-2/3)", "bq_inv(0)", `bq_inv(-${wide}/18446744073709551615)`,
  `typed(BQ, 18446744073709551615/${wide})`, "typed(BQ, 18446744073709551615.125)", `bq_of_int(binary_integers.(-${wide}))`,
  "bq_decide(1/2, 2/3)", "bq_decide(1/2 + 1/3, 5/6)",
  `bint_add(binary_integers.(${wide}), binary_integers.(-1))`,
  "bint_mul(binary_integers.(18446744073709551615), binary_integers.(-18446744073709551615))", "bint_neg(binary_integers.(7))",
  `bint_decide(binary_integers.(${wide}), binary_integers.(-1))`, "bint_decide(binary_integers.(5), bint_add(binary_integers.(2), binary_integers.(3)))",
  "typed(BQ and BInt, (1/2, binary_integers.(-3)))", "typed(BQ or BInt, left(1/2 + 1/2))", "typed(List(U0, BQ), cons(1/2, cons(2/3 * 3/4, nil)))",
])}
`);
  assert.deepEqual(texts, [
    fraction(q(15, 0), q(18, 0)), fraction(q(6, 0), q(6, 0)), fraction(q(3, 0), q(0, 2)), fraction(q(0, 0), q(1, 0)),
    fraction(q("18446744073709551615", 0), q(0, wide)), fraction(q("18446744073709551615", 0), q(wide, 0)),
    fraction(q("18446744073709551615125", 0), q(1000, 0)), fraction(q(0, wide), q(1, 0)),
    "right(<fun>)", `left(relate((${q(5, 0)}, ${q(6, 0)}, <fun>), (${q(5, 0)}, ${q(6, 0)}, <fun>), relate((bnat.(30), bnat.(0)), (bnat.(30), bnat.(0)), <path>)))`,
    q(wide, 1), q(0, "340282366920938463426481119284349108225"), q(0, 7),
    "right(<fun>)", "left(relate((bnat.(5), bnat.(0)), (bnat.(5), bnat.(0)), <path>))",
    `(${fraction(q(1, 0), q(2, 0))}, ${q(0, 3)})`, `left(${fraction(q(4, 0), q(4, 0))})`,
    `cons(${fraction(q(1, 0), q(2, 0))}, cons(${fraction(q(6, 0), q(12, 0))}, nil))`,
  ]);
});

// The binary integer and rational contracts (tests/fixtures/contracts/), each
// evaluated term printed in place of its directive, whose expected value is
// checked as written: every value form computes.
for (const [file, count] of [["binary_integer_contracts", 5], ["binary_integer_domain_contracts", 6], ["binary_rational_contracts", 30]])
  test(`the value forms of ${file} compute`, async t => {
    const path = fileURLToPath(new URL(`./fixtures/contracts/${file}.cubist`, import.meta.url)), source = await readFile(path, "utf8");
    let shown = source;
    for (const directive of parse(source).directives.filter(directive => directive.kind === "evaluate" && !directive.assertion).reverse())
      shown = shown.slice(0, directive.start) + each([source.slice(directive.value.start, directive.value.end)]) + shown.slice(directive.end);
    const texts = await printed(t, shown, { reader: sourceReader({ path }), options: { testMode: true } });
    assert.equal(texts.length, count);
  });

// The kernel's weak-head query substitutes the total into each call, so the
// last calls it builds for 510 are more than 512 levels deep, past its syntax
// depth guard (web/reference/checking.html#print).
test("a value whose weak head the kernel builds too deep stops with K344, as the reference shows", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;
def count_into(n, total : UNat) : UNat := match n {
  zero => total;
  succ(k) => count_into(k, succ(total));
};
print(evaluate(count_into(2 * 254, 0)));
print(evaluate(count_into(2 * 255, 0)));
`, { module });
  assert.deepEqual(outcomes(result), ["508", "K344: Native prototype syntax depth exceeds 512."]);
});

// The library Euclid (library/euclid.cubist) computes by NUM1's strong
// recursion; the certificate's function is shown as such. 7! + 1 = 71 * 71
// takes the search past the kernel's syntax depth guard.
test("the library Euclid's value forms", async t => {
  const texts = await printed(t, `import euclid;
use nat;
${each(["euclid(3)", "euclid(4).1", "euclid(4)", "euclid(5).1", "euclid(6).1", "factorial(5)"])}
`);
  assert.deepEqual(texts, ["(7, (tt, <fun>), tt)", "5", "(5, (tt, <fun>), tt)", "11", "7", "120"]);
  const { result } = await checkProgram(t, "import euclid;\nuse nat;\nprint(evaluate(euclid(7).1));", { module });
  assert.deepEqual(outcomes(result), ["K344: Native prototype syntax depth exceeds 512."]);
});

test("a call written twice, or relayed through another function, is computed once", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;
${duplicated}
print(evaluate(g24(tt)));
print(evaluate(2 * 255));
print(evaluate(typed(UNat and UNat, (2 * 255, 2 * 255))));
`, { module });
  assert.deepEqual(outcomes(result), ["tt", "510", "(510, 510)"]);
  const { result: again } = await checkProgram(t, `${relayed}\nprint(evaluate(g24(tt)));\n`, { module });
  assert.deepEqual(outcomes(again), ["tt"]);
});

// factorial(40) over binary Nat takes the kernel's queries seconds.
test("the declaration's time limit bounds a value form's queries", async t => {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const session = new ReplSession(program);
  assert.ok((await session.run("import nat; use nat;")).every(result => result.kind !== "error"));
  program.kernel.setDeadline(150);
  const [answer] = await session.run("evaluate factorial(40);");
  program.kernel.setDeadline();
  assert.equal(answer.text, "E629: Declaration time limit exceeded.");
});
