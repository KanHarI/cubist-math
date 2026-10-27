import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { Translator } from "../web/translator/translate.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";

// The value form of `evaluate e` and `print(evaluate(e))` is observed by the
// runtime (web/cubical-runtime.mjs, EVAL3/EVAL4), and demand it reports
// unsupported is computed again, whole, by the kernel's head queries
// (valueFormOf in web/translator/translate.mjs). Each value it shows is the
// one the kernel's queries alone show, which runtimeEvaluation: false asks
// for; where the kernel's queries stop, at the syntax depth guard, the
// runtime can show more. A runtime stop at its limits is reported, not
// retried. `!`, `!!`, `!!!`, patterns and exact expected values stay on the
// kernel's queries. Every construct of the language is compared in
// tests/evaluation-demand-marks.test.mjs.
const module = await createCubical();

// Every print of a source, computed by the runtime and by the kernel alone.
async function bothWays(t, source) {
  const run = async runtimeEvaluation => (await checkProgram(t, source, { module, options: { runtimeEvaluation } })).result;
  return { runtime: await run(true), kernel: await run(false) };
}
const outcomes = result => [...result.prints.map(print => [print.start, print.text]),
  ...result.gaps.filter(gap => gap.directive).map(gap => [gap.declarationStart, `${gap.code}: ${gap.reason.replace(/ at \d+:\d+$/, "")}`])]
  .sort(([a], [b]) => a - b).map(([, outcome]) => outcome);
const by = result => result.prints.map(print => print.valueForm?.by);

test("closures keep capture and shadowing, leave unused arguments and share a thunk", async t => {
  const { runtime, kernel } = await bothWays(t, `import unat;
use unat;
inductive Flag : U0 {
  disabled;
  enabled;
}
inductive Circle : U0 {
  base;
  loop : base = base;
}
def both(a, b : Unit) : Unit := unit_induction(fun (x : Unit) => Unit, b, a);
def g0(u : Unit) : Unit := u;
${Array.from({ length: 24 }, (_, i) => `def g${i + 1}(u : Unit) : Unit := both(g${i}(u), g${i}(u));`).join("\n")}
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
`);
  assert.deepEqual(outcomes(runtime), ["enabled", "tt", "tt", "510", "(510, 510)", "(tt, base)"]);
  assert.deepEqual(outcomes(runtime), outcomes(kernel));
  assert.deepEqual(by(runtime), Array(6).fill("runtime"));
  assert.deepEqual(by(kernel), Array(6).fill("kernel"));
  const [, , unused, single, shared] = runtime.prints.map(print => print.valueForm);
  // g24(tt) would cost 2^24 calls: the unused argument is never forced,
  // and the steps are mostly the snapshot's copy of g0 to g24.
  assert.ok(unused.steps < 10000, `the unused argument took ${unused.steps} steps`);
  // Both components are the one argument thunk, computed once.
  assert.ok(shared.steps < 1.5 * single.steps, `the shared pair took ${shared.steps} steps, one number ${single.steps}`);
  // Each observation spends the query of fuel the head query it stands for
  // spends.
  const fuel = result => result.directiveFuel.filter(directive => directive.kind === "print").map(directive => directive.searchFuel.queries);
  assert.deepEqual(fuel(runtime), fuel(kernel));
});

// The value forms of a source, alternately by the runtime and by the
// kernel's queries alone, in one program: each print is written twice, and
// the first of each pair may ask the runtime. Checking a source's imports
// once serves both.
async function alternately(t, source, { reader = sourceReader(), options = {} } = {}) {
  const program = new CubicalProgram(module, reader, options);
  t.after(() => program.dispose());
  const valueFormOf = Translator.prototype.valueFormOf;
  let turn = 0;
  Translator.prototype.valueFormOf = function (...args) {
    this.checker.runtimeEvaluation = turn++ % 2 === 0;
    try { return valueFormOf.apply(this, args); } finally { this.checker.runtimeEvaluation = true; }
  };
  let result;
  try { result = await program.check(source, "main"); } finally { Translator.prototype.valueFormOf = valueFormOf; }
  assert.deepEqual(result.gaps.filter(gap => gap.directive).map(gap => gap.reason), []);
  assert.equal(result.prints.length % 2, 0);
  const pairs = [];
  for (let i = 0; i < result.prints.length; i += 2) {
    const [runtime, kernel] = result.prints.slice(i, i + 2);
    assert.equal(kernel.valueForm.by, "kernel");
    // The runtime's value form, or its fallback, is the kernel's.
    assert.equal(runtime.text, kernel.text, `the runtime's value form at ${runtime.start} is the kernel's`);
    pairs.push({ text: runtime.text, ...runtime.valueForm });
  }
  return pairs;
}
const twice = terms => terms.map(term => `print(evaluate(${term}));\nprint(evaluate(${term}));`).join("\n");
// What computed each value form: the runtime, or the demand it refused.
const computedBy = pairs => pairs.map(pair => pair.by === "runtime" ? "runtime" : pair.unsupported);
const pathConstructor = "Execution of a path constructor is not implemented.";
const pathApplied = "Runtime execution of PApp is not implemented.";
const composition = "Runtime execution of Comp is not implemented.";

// The runtime executes the point constructors of any declared type, higher
// or truncated too, and its eliminators' clauses for them, as the kernel's
// iota does. A path constructor, a path applied and a composition are
// refused where the walk meets them, never decided from the value's type:
// the fallback computes the whole value form again by the kernel's queries.
// The kernel selects an eliminator's path clause only under a dimension
// binder, as in the composition rule an eliminator applied to a
// transported value takes; at an endpoint, a path constructor computes to
// its boundary first. Either is demand the runtime refuses.
test("point constructors of a quotient, a circle and a truncation compute in the runtime, and their paths fall back", async t => {
  const pairs = await alternately(t, `import quotients;
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
${twice([
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
  assert.deepEqual(pairs.map(pair => pair.text), ["class(3)", "base", "(class(3), tt)", "(3, tt)", "base", "class(6)", "point(3)",
    "point(4)", "gpoint(2)", "loop", "relate(1, 3, tt)", "(tt, class(6))", "squash(point(1), point(2))",
    "base", "base", "class(2)", "point(2)", "<composition>", "<composition>"]);
  assert.deepEqual(computedBy(pairs), [...Array(9).fill("runtime"), pathConstructor, pathConstructor, "runtime", pathConstructor,
    ...Array(4).fill(pathApplied), composition, composition]);
  // Every fallback follows a runtime query, which met the demand itself.
  for (const pair of pairs) if (pair.by === "kernel") assert.ok(pair.runtime.snapshotNodes > 0);
});

// Binary integers and rationals are set quotients, of differences of binary
// naturals and of fractions over them: their arithmetic, inverses and
// decisions compute in the runtime, with components past 64 and 128 bits,
// and inside pairs, sums and lists. A decision that finds two values equal
// holds the quotient's path constructor, which falls back.
test("binary integer and rational value forms compute in the runtime", async t => {
  const wide = "340282366920938463463374607431768211455", q = (n, d) => `class((bnat.(${n}), bnat.(${d})))`;
  const fraction = (n, d) => `class((${n}, ${d}, <fun>))`;
  const pairs = await alternately(t, `import binary_rationals;
use binary_rationals;
${twice([
  "2/3 + 1/6", "(-2/3) * (-3/2)", "bq_inv(-2/3)", "bq_inv(0)", `bq_inv(-${wide}/18446744073709551615)`,
  `typed(BQ, 18446744073709551615/${wide})`, "typed(BQ, 18446744073709551615.125)", `bq_of_int(binary_integers.(-${wide}))`,
  "bq_decide(1/2, 2/3)", "bq_decide(1/2 + 1/3, 5/6)",
  `bint_add(binary_integers.(${wide}), binary_integers.(-1))`,
  "bint_mul(binary_integers.(18446744073709551615), binary_integers.(-18446744073709551615))", "bint_neg(binary_integers.(7))",
  `bint_decide(binary_integers.(${wide}), binary_integers.(-1))`, "bint_decide(binary_integers.(5), bint_add(binary_integers.(2), binary_integers.(3)))",
  "typed(BQ and BInt, (1/2, binary_integers.(-3)))", "typed(BQ or BInt, left(1/2 + 1/2))", "typed(List(U0, BQ), cons(1/2, cons(2/3 * 3/4, nil)))",
])}
`);
  assert.deepEqual(pairs.map(pair => pair.text), [
    fraction(q(15, 0), q(18, 0)), fraction(q(6, 0), q(6, 0)), fraction(q(3, 0), q(0, 2)), fraction(q(0, 0), q(1, 0)),
    fraction(q("18446744073709551615", 0), q(0, wide)), fraction(q("18446744073709551615", 0), q(wide, 0)),
    fraction(q("18446744073709551615125", 0), q(1000, 0)), fraction(q(0, wide), q(1, 0)),
    "right(<fun>)", `left(relate((${q(5, 0)}, ${q(6, 0)}, <fun>), (${q(5, 0)}, ${q(6, 0)}, <fun>), relate((bnat.(30), bnat.(0)), (bnat.(30), bnat.(0)), <path>)))`,
    q(wide, 1), q(0, "340282366920938463426481119284349108225"), q(0, 7),
    "right(<fun>)", "left(relate((bnat.(5), bnat.(0)), (bnat.(5), bnat.(0)), <path>))",
    `(${fraction(q(1, 0), q(2, 0))}, ${q(0, 3)})`, `left(${fraction(q(4, 0), q(4, 0))})`,
    `cons(${fraction(q(1, 0), q(2, 0))}, cons(${fraction(q(6, 0), q(12, 0))}, nil))`,
  ]);
  assert.deepEqual(computedBy(pairs), [...Array(9).fill("runtime"), pathConstructor, ...Array(4).fill("runtime"), pathConstructor,
    ...Array(3).fill("runtime")]);
});

// The binary integer and rational contracts (tests/fixtures/contracts/), each
// evaluated term printed in place of its directive, whose expected value
// stays on the kernel's queries: every value form is the kernel's. The
// domain's zero decision of a zero integer holds a path constructor.
for (const [file, expected] of [
  ["binary_integer_contracts", Array(5).fill("runtime")],
  ["binary_integer_domain_contracts", ["runtime", "runtime", pathConstructor, "runtime", "runtime", "runtime"]],
  ["binary_rational_contracts", Array(30).fill("runtime")],
]) test(`the value forms of ${file} are the kernel's, computed in the runtime`, async t => {
  const path = fileURLToPath(new URL(`./fixtures/contracts/${file}.cubist`, import.meta.url)), source = await readFile(path, "utf8");
  let printed = source;
  for (const directive of parse(source).directives.filter(directive => directive.kind === "evaluate" && !directive.assertion).reverse())
    printed = printed.slice(0, directive.start) + twice([source.slice(directive.value.start, directive.value.end)]) + printed.slice(directive.end);
  const pairs = await alternately(t, printed, { reader: sourceReader({ path }), options: { testMode: true } });
  assert.deepEqual(computedBy(pairs), expected);
});

test("the runtime shows a value whose weak head the kernel builds too deep, as the reference shows", async t => {
  const { runtime, kernel } = await bothWays(t, `import unat;
use unat;
def count_into(n, total : UNat) : UNat := match n {
  zero => total;
  succ(k) => count_into(k, succ(total));
};
print(evaluate(count_into(2 * 254, 0)));
print(evaluate(count_into(2 * 255, 0)));
`);
  assert.deepEqual(outcomes(runtime), ["508", "510"]);
  assert.deepEqual(outcomes(kernel), ["508", "K344: Native prototype syntax depth exceeds 512."]);
});

test("the runtime shows Euclid's primes past the kernel's syntax depth guard, and stops at its limits", async t => {
  const { runtime, kernel } = await bothWays(t, `import euclid;
use unat;
print(evaluate(euclid(3)));
print(evaluate(euclid(4).1));
print(evaluate(euclid(4)));
print(evaluate(euclid(5).1));
print(evaluate(euclid(6).1));
`);
  // The certificate's path and function are shown as such, not computed.
  assert.deepEqual(outcomes(runtime), ["(7, (5, <path>, <fun>), tt)", "5", "(5, (3, <path>, <fun>), tt)", "11",
    "E488: The runtime's evaluation of the value form exhausted its allocation budget of 20,000,000 cells."]);
  assert.deepEqual(by(runtime), ["runtime", "runtime", "runtime", "runtime"]);
  // A stop at the runtime's limits is the runtime's, not retried by the kernel.
  assert.equal(runtime.gaps.find(gap => gap.directive).failure, "resource");
  assert.deepEqual(outcomes(kernel), ["(7, (5, <path>, <fun>), tt)", ...Array(3).fill("K344: Native prototype syntax depth exceeds 512."),
    "K336: Native reduction recursion depth exceeded."]);
});

test("the declaration's time limit bounds the runtime, as it bounds the kernel's queries", async t => {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const session = new ReplSession(program);
  assert.deepEqual((await session.run("import euclid; use unat;")).map(result => result.kind), ["info", "info"]);
  program.kernel.setDeadline(150);
  const [answer] = await session.run("evaluate euclid(5).1;");
  program.kernel.setDeadline();
  assert.equal(answer.text, "E629: Declaration time limit exceeded.");
});
