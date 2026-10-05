import "./fresh-build.mjs";
import {sourceReader} from "../tools/module-sources.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { benchmark, category } from "../web/benchmark-runner.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { budget } from "./timing.mjs";

// A kernel session with its instruction graph, and a definition of tt : Unit
// admitted by Define, recorded under its name as the elaborator records one.
async function session(t) {
  const module = await createCubical(), kernel = new CubicalKernel(module), graph = new InstructionGraph(kernel);
  t.after(() => kernel.dispose());
  const define = (name, value = graph.point()) => {
    const reference = graph.judgement(graph.define(name, value)).term;
    kernel.definitions.set(name, reference);
    return reference;
  };
  return { module, kernel, graph, define, typeOf: reference => kernel.node(graph.judgement(graph.lookup(reference)).type).kind };
}

test("benchmark distinguishes invalid proofs, blocked uses, and independent checked declarations", async () => {
  const report = await benchmark({ modules: ["sample"], readSource: async name => name === "sample" ?
    "import nat; def good := 0; def bad : 0 = 1 { exact refl(0); } def dependent := bad; def independent := 2;" : sourceReader()(name) });
  assert.deepEqual(report.declarations.filter(d=>d.module === "sample").map(d => d.category), ["checked", "failed", "blocked", "checked"]);
  assert.equal(report.declarations.find(d=>d.name === "dependent").rootBlocker, "sample__bad");
  for(const row of report.declarations.filter(d=>d.module === "sample")) {
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

test("the native deadline rejects work, then recovers", async t => {
  const { module, kernel, graph } = await session(t);
  graph.point();
  // Set C's deadline directly so this exercises C, not the JS preflight guard.
  module._cb_deadline_ms(kernel.handle, .01);
  const until = performance.now() + 2;
  while (performance.now() < until) { /* let the native deadline expire */ }
  assert.throws(() => graph.unit(), /Declaration time limit exceeded/);
  module._cb_deadline_ms(kernel.handle, 0);
  assert.equal(kernel.node(graph.judgement(graph.unit()).term).kind, "Unit");
});

test("rollback discards definitions and cached reductions from a rejected attempt", async t => {
  const { module, kernel, graph, define, typeOf } = await session(t);
  const before = define("before");
  module._cb_checkpoint(kernel.handle);
  const late = define("late");
  kernel.head(late);
  module._cb_rollback(kernel.handle);
  kernel.definitions.delete("late");
  assert.throws(() => graph.lookup(late));
  assert.equal(typeOf(before), "Unit");
});

test("a timeout remains a speed failure", () => {
  assert.equal(category({ status: "checked-native-cubical" }, 1000.01, 1000), "optimize");
  assert.equal(category({ failure: "deadline", reason: "Declaration time limit exceeded." }, 1000, 1000), "optimize");
});

test("successful compaction retains definitions and translates references", async t => {
  const { module, kernel, graph, define, typeOf } = await session(t);
  module._cb_checkpoint(kernel.handle);
  for (let i = 0; i < 300; i++) kernel.term("Var", kernel.symbol(`unused${i}`));
  const reference = define("retained");
  kernel.head(reference);
  assert.equal(module._cb_commit_checkpoint(kernel.handle), 1);
  const moved = module._cb_relocated(kernel.handle, reference);
  assert.ok(moved < reference);
  kernel.definitions.set("retained", moved);
  assert.equal(kernel.node(kernel.head(moved)).kind, "Point");
  assert.equal(typeOf(moved), "Unit");
  module._cb_checkpoint(kernel.handle);
  const later = define("later", graph.lookup(moved));
  assert.equal(typeOf(later), "Unit");
});

test("benchmark reports the selected deadline and optimizations and rejects invalid deadlines", async () => {
  const optimizations = { shareSyntax: false, reuseChecks: false, compactPaths: false };
  const report = await benchmark({ modules: ["sample"], limitMs: 250, optimizations, readSource: async name => name === "sample" ? "def one := tt;" : sourceReader()(name) });
  assert.equal(report.limitMs, 250);
  assert.deepEqual(report.optimizations, optimizations);
  assert.equal(report.counts.checked, 1);
  for (const limitMs of [0, -1, NaN, Infinity]) await assert.rejects(benchmark({ limitMs }), /positive number/);
});

test("benchmark checks local simp witnesses without collecting inspector references",async()=>{
  const report=await benchmark({modules:["ergonomics_registered"],limitMs:budget(10000),
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
  const readSource = async name => name === "sample" ? "import nat; def good := 0; def uses := good;" : sourceReader()(name);
  const report = await benchmark({ modules: ["sample"], readSource });
  for (const row of report.declarations.filter(d=>d.module === "sample")) {
    assert.equal(row.category, "checked");
    assert.ok(row.instructionJudgements > 0 && row.instructionMs >= 0, row.binding);
    assert.ok(row.elapsedMs >= row.instructionMs);
  }
  // What the instruction kernel cannot derive fails, and blocks what uses it.
  const check = InstructionDriver.prototype.check;
  InstructionDriver.prototype.check = function (value, type, context) {
    if (this.kernel.node(value).kind === "Con") throw new Error("No rule for this yet.");
    return check.call(this, value, type, context);
  };
  try {
    const failing = await benchmark({ modules: ["sample"], readSource });
    assert.deepEqual(failing.declarations.filter(d=>d.module === "sample").map(d => d.category), ["failed", "blocked"]);
    assert.match(failing.declarations.find(d=>d.name === "good").reason, /^Instruction kernel: No rule for this yet/);
    assert.equal(failing.declarations.find(d=>d.name === "uses").rootBlocker, "sample__good");
  } finally { InstructionDriver.prototype.check = check; }
});
