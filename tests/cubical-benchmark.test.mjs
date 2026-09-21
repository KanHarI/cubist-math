import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { benchmark, category } from "../web/benchmark-runner.mjs";

test("benchmark distinguishes invalid proofs, blocked uses, and independent checked declarations", async () => {
  const report = await benchmark({ modules: ["sample"], readSource: async () =>
    "def good = 0; theorem bad : 0 = 1 { exact refl(0); } def dependent = bad; def independent = 2;" });
  assert.deepEqual(report.declarations.map(d => d.category), ["checked", "failed", "blocked", "checked"]);
  assert.equal(report.declarations[2].rootBlocker, "sample__bad");
  assert.equal(report.importErrors.length, 0);
});

test("the native deadline rejects work without leaking a previous certificate, then recovers", async t => {
  const module = await createCubical(), kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  const nat = kernel.term("Nat"), zero = kernel.term("Zero");
  kernel.check(zero, nat);
  // Set C's deadline directly so this exercises C, not the JS preflight guard.
  module._cb_deadline_ms(kernel.handle, .01);
  const until = performance.now() + 2;
  while (performance.now() < until) { /* let the native deadline expire */ }
  assert.throws(() => kernel.check(zero, nat), /Declaration time limit exceeded/);
  assert.equal(module._cb_result(kernel.handle, 0), 0);
  module._cb_deadline_ms(kernel.handle, 0);
  assert.equal(kernel.node(kernel.check(zero, nat).expression).kind, "Zero");
});

test("rollback discards checked definitions and cached reductions from a rejected attempt", async t => {
  const module = await createCubical(), kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  const nat = kernel.term("Nat"), zero = kernel.term("Zero");
  const before = kernel.define("before", zero, nat);
  module._cb_checkpoint(kernel.handle);
  const late = kernel.define("late", kernel.term("Succ", 0, zero), nat);
  kernel.head(late);
  module._cb_rollback(kernel.handle);
  kernel.definitions.delete("late");
  assert.equal(module._cb_result(kernel.handle, 0), 0);
  assert.throws(() => kernel.check(late, nat));
  assert.equal(kernel.node(kernel.check(before, nat).type).kind, "Nat");
  assert.throws(() => kernel.check(kernel.term("Point"), nat));
});

test("a timeout remains a speed failure and templates are not counted as checked proofs", () => {
  assert.equal(category({ status: "checked-native-cubical" }, 1000.01, 1000), "optimize");
  assert.equal(category({ reason: "Declaration time limit exceeded." }, 1000, 1000), "optimize");
  assert.equal(category({ reason: "Universe schema: checked at uses" }, 0, 1000), "template");
});
