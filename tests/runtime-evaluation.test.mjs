import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
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
  assert.deepEqual(by(runtime), ["runtime", "runtime", "runtime", "runtime", "runtime", "kernel"]);
  assert.deepEqual(by(kernel), Array(6).fill("kernel"));
  const [, , unused, single, shared, circle] = runtime.prints.map(print => print.valueForm);
  // g24(tt) would cost 2^24 calls: the unused argument is never forced,
  // and the steps are mostly the snapshot's copy of g0 to g24.
  assert.ok(unused.steps < 10000, `the unused argument took ${unused.steps} steps`);
  // Both components are the one argument thunk, computed once.
  assert.ok(shared.steps < 1.5 * single.steps, `the shared pair took ${shared.steps} steps, one number ${single.steps}`);
  assert.equal(circle.unsupported, "Higher and truncated data execution is not implemented.");
  // Each observation spends the query of fuel the head query it stands for
  // spends, and the type's weak head, which decides whether to ask the
  // runtime, one more.
  const fuel = result => result.directiveFuel.filter(directive => directive.kind === "print").map(directive => directive.searchFuel.queries);
  assert.deepEqual(fuel(runtime).slice(0, 5), fuel(kernel).slice(0, 5).map(queries => queries + 1));
});

// A value of a declared type the runtime does not execute, as a quotient or
// a higher inductive type, has such a constructor or a composition at its
// weak head: the fallback is decided from the type, with its reason and no
// snapshot. A value whose type is ordinary still asks the runtime, which
// reports the same demand where it meets it.
const early = { by: "kernel", unsupported: "Higher and truncated data execution is not implemented." };
test("a value of a quotient or higher sort falls back before the snapshot, and ordinary data does not", async t => {
  const { runtime, kernel } = await bothWays(t, `import quotients;
use unat;
inductive Circle : U0 {
  base;
  loop : base = base;
}
def R(m, n : UNat) : U0 := Unit;
def three : Quotient(U0, UNat, R) := class(3);
print(evaluate(three));
print(evaluate(base));
print(evaluate(typed(Quotient(U0, UNat, R) and Unit, (three, tt))));
print(evaluate(typed(UNat and Unit, (3, tt))));
`);
  assert.deepEqual(outcomes(runtime), outcomes(kernel));
  assert.deepEqual(outcomes(runtime), ["class(3)", "base", "(class(3), tt)", "(3, tt)"]);
  const [quotient, circle, pair, data] = runtime.prints.map(print => print.valueForm);
  assert.deepEqual([quotient, circle], [early, early]);
  // A pair's type decides nothing: the runtime is asked, and meets the
  // quotient's constructor itself.
  assert.equal(pair.by, "kernel");
  assert.equal(pair.unsupported, early.unsupported);
  assert.ok(pair.runtime.snapshotNodes > 0);
  assert.equal(data.by, "runtime");
});

test("a binary rational's value form goes to the kernel's queries before any snapshot", async t => {
  const { result } = await checkProgram(t, `import binary_rationals;
use binary_rationals;
print(evaluate(2/3 + 1/6));
`, { module });
  assert.deepEqual(result.gaps, []);
  assert.deepEqual(result.prints[0].valueForm, early);
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
