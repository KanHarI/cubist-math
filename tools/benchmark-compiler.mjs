import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { performance } from "node:perf_hooks";

const script = fileURLToPath(import.meta.url);
const root = fileURLToPath(new URL("../", import.meta.url));
const help = `Usage: node tools/benchmark-compiler.mjs [options] module-or-proof [...]

Compare baseline and optimized compilation in separate, sequential processes.
Every run verifies its results; comparisons require identical output statements
and axiom dependencies. Only selected proofs and their imports are compiled.

  --reuse-normal-forms     Compare baseline with normal-form reuse
  --memoize-instructions   Compare baseline with instruction memoization
  --index-fresh-contexts   Compare baseline with incremental context lookup
  --baseline-only          Measure only baseline compilation
  --replay                 Replay every instruction in a fresh kernel
  --json                   Print machine-readable results
  --help                   Show this help

Combine optimization flags to measure their combined effect. Without flags,
measure baseline, each optimization separately, and all together.
`;

function modeName(options) {
  return Object.entries(options).filter(([, enabled]) => enabled).map(([name]) => name).join(" + ") || "baseline";
}

async function measure(path, optimizations, replay) {
  const [{ default: createKernel }, { compile }, { Kernel }, { loadProof }] = await Promise.all([
    import("../web/dist/kernel.mjs"),
    import("../web/mathscript/compiler.mjs"),
    import("../web/kernel.mjs"),
    import("./test-selection.mjs"),
  ]);
  const { source, sources, label } = await loadProof(path);
  const module = await createKernel();
  let lastReport = performance.now();
  const started = performance.now();
  const c = compile(module, source, sources, {
    optimizations,
    onProgress(progress) {
      if (performance.now() - lastReport < 60000) return;
      lastReport = performance.now();
      process.stderr.write(`${label} (${modeName(optimizations)}): ${progress.instructions} kernel steps\n`);
    },
  });
  try {
    const compileMs = performance.now() - started;
    if (Object.values(optimizations).some(Boolean))
      assert.deepEqual(c.optimizations, optimizations, "Compiler must explicitly acknowledge each optimization");
    const checks = c.mode === "construction"
      ? c.checks.map(check => ({ ...check, binding: check.proof }))
      : c.outputs;
    for (const output of checks)
      assert.ok(c.kernel.verify(output.proposition, output.binding), output.name ?? output.binding);
    const statements = c.outputs.map(output => ({
      name: output.name,
      type: output.type,
      axioms: c.kernel.axiomsFor(output.binding).sort(),
    }));
    const operations = {};
    for (const step of c.kernel.steps) operations[step.op] = (operations[step.op] ?? 0) + 1;
    let replayMs;
    if (replay) {
      const checked = new Kernel(module, c.allowAxioms);
      const replayStarted = performance.now();
      try {
        for (const step of c.kernel.steps) checked.apply(step);
        for (const output of checks) {
          assert.ok(checked.verify(output.proposition, output.binding), `replay: ${output.name ?? output.binding}`);
          assert.deepEqual(checked.axiomsFor(output.binding).sort(), c.kernel.axiomsFor(output.binding).sort());
        }
        replayMs = performance.now() - replayStarted;
      } finally { checked.dispose(); }
    }
    return {
      proof: label, optimizations, instructions: c.instructionCount,
      compileMs, replayMs, stats: c.kernel.stats(), operations, statements,
    };
  } finally { c.kernel.dispose(); }
}

async function main(args) {
  if (args[0] === "--worker") {
    const [path, optimizations, replay] = JSON.parse(args[1]);
    console.log(JSON.stringify(await measure(path, optimizations, replay)));
    return;
  }
  const proofs = [];
  const selected = { normalForms: false, instructions: false, freshContexts: false };
  let baselineOnly = false, replay = false, json = false;
  for (const arg of args) {
    if (arg === "--help" || arg === "-h") { console.log(help); return; }
    if (arg === "--reuse-normal-forms") selected.normalForms = true;
    else if (arg === "--memoize-instructions") selected.instructions = true;
    else if (arg === "--index-fresh-contexts") selected.freshContexts = true;
    else if (arg === "--baseline-only") baselineOnly = true;
    else if (arg === "--replay") replay = true;
    else if (arg === "--json") json = true;
    else if (arg.startsWith("-")) throw new Error(`Unknown option: ${arg}`);
    else proofs.push(resolve(root, /^[A-Za-z_][A-Za-z0-9_]*$/.test(arg) ? `web/proofs/${arg}.proof` : arg));
  }
  if (!proofs.length) throw new Error(help);
  if (baselineOnly && Object.values(selected).some(Boolean)) throw new Error("--baseline-only cannot be combined with optimization flags");
  const baseline = { normalForms: false, instructions: false, freshContexts: false };
  const modes = baselineOnly ? [baseline] : Object.values(selected).some(Boolean) ? [baseline, selected] : [
    baseline, { ...baseline, normalForms: true },
    { ...baseline, instructions: true }, { ...baseline, freshContexts: true },
    { normalForms: true, instructions: true, freshContexts: true },
  ];
  const results = [];
  for (const path of [...new Set(proofs)]) {
    const runs = [];
    for (const optimizations of modes) {
      const child = promisify(execFile)(process.execPath,
        [script, "--worker", JSON.stringify([path, optimizations, replay])],
        { cwd: root, maxBuffer: 8 * 1024 * 1024 });
      child.child.stderr.pipe(process.stderr);
      const { stdout } = await child;
      const result = JSON.parse(stdout);
      runs.push(result);
      if (!json) console.log(`${result.proof} · ${modeName(optimizations)}: ${result.instructions.toLocaleString()} instructions, ${(result.compileMs / 1000).toFixed(2)}s${replay ? `; replay ${(result.replayMs / 1000).toFixed(2)}s` : ""}`);
    }
    const entry = { proof: runs[0].proof, runs };
    entry.comparisons = [];
    for (const optimized of runs.slice(1)) {
      const baseline = runs[0];
      assert.deepEqual(optimized.statements, baseline.statements, "Optimization changed output statements or axiom dependencies");
      const savedInstructions = baseline.instructions - optimized.instructions;
      const reductionPercent = 100 * savedInstructions / baseline.instructions;
      entry.comparisons.push({ optimizations: optimized.optimizations, savedInstructions, reductionPercent });
      if (!json) {
        console.log(`  ${modeName(optimized.optimizations)}: saved ${savedInstructions.toLocaleString()} instructions (${reductionPercent.toFixed(1)}%); statements and dependencies agree.`);
        const operations = new Set([...Object.keys(baseline.operations), ...Object.keys(optimized.operations)]);
        const deltas = [...operations].map(op => [op, (baseline.operations[op] ?? 0) - (optimized.operations[op] ?? 0)])
          .filter(([, count]) => count !== 0).sort((a, b) => b[1] - a[1]).slice(0, 8);
        for (const [op, count] of deltas) console.log(`  ${op}: ${count >= 0 ? "−" : "+"}${Math.abs(count).toLocaleString()}`);
      }
    }
    results.push(entry);
  }
  if (json) console.log(JSON.stringify(results, null, 2));
}

main(process.argv.slice(2)).catch(error => {
  console.error(error.message);
  process.exitCode = 1;
});
