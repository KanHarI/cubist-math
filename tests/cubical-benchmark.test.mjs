import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { benchmark, category } from "../web/benchmark-runner.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { budget } from "./timing.mjs";

test("benchmark distinguishes invalid proofs, blocked uses, and independent checked declarations", async () => {
  const report = await benchmark({ modules: ["sample"], readSource: async () =>
    "def good := 0; def bad : 0 = 1 { exact refl(0); } def dependent := bad; def independent := 2;" });
  assert.deepEqual(report.declarations.map(d => d.category), ["checked", "failed", "blocked", "checked"]);
  assert.equal(report.declarations[2].rootBlocker, "sample__bad");
  for(const row of report.declarations) {
    assert.ok(Number.isSafeInteger(row.nativeCheckingSteps)&&row.nativeCheckingSteps>=0);
    assert.deepEqual(row.rewriteWork,{traversals:0,candidateVisits:0,eligibleMatches:0,
      successfulRewrites:0,premiseAttempts:0,premiseProofs:0,premiseRewriteSteps:0});
    if(row.category==="checked") {
      assert.ok(row.finalCheckArenaNodes>0);
      assert.ok(row.finalCheckArenaBytes>0);
    } else {
      assert.equal(row.finalCheckArenaNodes,null);
      assert.equal(row.finalCheckArenaBytes,null);
    }
  }
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
  assert.equal(category({ failure: "deadline", reason: "Declaration time limit exceeded." }, 1000, 1000), "optimize");
  assert.equal(category({ template: true, reason: "Universe schema: checked at uses" }, 0, 1000), "template");
});

test("successful compaction retains definitions and translates references while clearing stale results", async t => {
  const module = await createCubical(), kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  const nat = kernel.term("Nat"), zero = kernel.term("Zero");
  module._cb_checkpoint(kernel.handle);
  for (let i = 0; i < 300; i++) kernel.term("Var", kernel.symbol(`unused${i}`));
  const reference = kernel.define("retained", kernel.term("Succ", 0, zero), nat);
  kernel.head(reference);
  assert.equal(module._cb_commit_checkpoint(kernel.handle), 1);
  const moved = module._cb_relocated(kernel.handle, reference);
  assert.ok(moved < reference);
  kernel.definitions.set("retained", moved);
  assert.equal(kernel.node(kernel.head(moved)).kind, "Succ");
  assert.equal(kernel.node(kernel.check(moved, nat).type).kind, "Nat");
  assert.throws(() => kernel.check(moved, kernel.term("Unit")));
  module._cb_checkpoint(kernel.handle);
  const later = kernel.define("later", moved, nat);
  assert.equal(kernel.node(kernel.check(later, nat).type).kind, "Nat");
});

test("benchmark reports the selected deadline and optimizations and rejects invalid deadlines", async () => {
  const optimizations = { shareSyntax: false, reuseChecks: false, compactPaths: false };
  const report = await benchmark({ modules: ["sample"], limitMs: 250, optimizations, readSource: async () => "def one := 1;" });
  assert.equal(report.limitMs, 250);
  assert.deepEqual(report.optimizations, optimizations);
  assert.equal(report.counts.checked, 1);
  for (const limitMs of [0, -1, NaN, Infinity]) await assert.rejects(benchmark({ limitMs }), /positive number/);
});

test("benchmark checks local simp witnesses without collecting inspector references",async()=>{
  const report=await benchmark({modules:["ergonomics_registered"],limitMs:budget(1000),
    readSource:async name=>{
      const source=await readFile(name==="ergonomics_registered"
        ? new URL("../docs/examples/proof-ergonomics/implemented/registered-simp.cubist",import.meta.url)
        : new URL(`../archive/first-library/${name}.cubist`,import.meta.url),"utf8");
      return name==="ergonomics_registered"?`${source}
        def folded(n : Nat) := n + 0;
        def twice(n : Nat) := folded(n);
        def inner(n : Nat, h : n + 0 = n) : folded(n) = n { exact h; }
        def outer(n : Nat, h : folded(n) = n) : twice(n) = n { exact h; }
        def nested(n : Nat) : twice(n) = n { simp only [outer, inner, nat_add_zero]; }
      `:source;
    }});
  assert.equal(report.counts.failed,0,JSON.stringify(report.declarations.filter(d=>d.category==="failed")));
  for(const name of ["simplified_copy","conditional_rewrite","recursive_premise","nested"])
    assert.equal(report.declarations.find(d=>d.name===name)?.category,"checked",name);
  const work=report.declarations.find(d=>d.name==="nested").rewriteWork;
  assert.ok(work.candidateVisits>0&&work.premiseAttempts>=2&&work.premiseProofs>=2);
});

test("the instruction kernel admits each declaration the benchmark counts", async () => {
  const readSource = async () => "def good := 0; def uses := good;";
  const report = await benchmark({ modules: ["sample"], readSource });
  for (const row of report.declarations) {
    assert.equal(row.category, "checked");
    assert.ok(row.instructionJudgements > 0 && row.instructionMs >= 0, row.binding);
    assert.ok(row.elapsedMs >= row.instructionMs);
  }
  // What the instruction kernel cannot derive fails, and blocks what uses it.
  const check = InstructionDriver.prototype.check;
  InstructionDriver.prototype.check = function (value, type, context) {
    if (this.kernel.node(value).kind === "Zero") throw new Error("No rule for this yet.");
    return check.call(this, value, type, context);
  };
  try {
    const failing = await benchmark({ modules: ["sample"], readSource });
    assert.deepEqual(failing.declarations.map(d => d.category), ["failed", "blocked"]);
    assert.match(failing.declarations[0].reason, /^Instruction kernel: No rule for this yet/);
    assert.equal(failing.declarations[1].rootBlocker, "sample__good");
  } finally { InstructionDriver.prototype.check = check; }
});
