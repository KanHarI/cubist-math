// Fixed-budget full normalization of the constant-transport reproduction.
import { readFileSync } from "node:fs";
import { createHash } from "node:crypto";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "./module-sources.mjs";
import { assertFreshBuild, sourceHash } from "./build-stamp.mjs";

assertFreshBuild();
const source = readFileSync(new URL("../tests/fixtures/constant-setness-transport.cubist", import.meta.url), "utf8");
const fixtureHash = createHash("sha256").update(source).digest("hex");
const kernelHash = sourceHash("kernel");
const cases = ["moved_value", "moved_function", "moved_neutral", "moved_setness", "moved_path"];
const steps = 10000000n;
for (const name of cases) {
  const module = await createCubical();
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  try {
    const checked = await program.check(source, "transport_probe");
    if (!checked.complete) throw new Error(JSON.stringify(checked.gaps));
    const dependencies = Object.entries(program.sources).filter(([name]) => name !== "transport_probe")
      .sort(([a], [b]) => a.localeCompare(b));
    const dependencyHash = createHash("sha256").update(JSON.stringify(dependencies)).digest("hex");
    const expression = program.checker.checkSyntax({ tag: "DefRef", name: `transport_probe__${name}` },
      null, new Map(), new Map()).expression;
    const kernel = program.kernel;
    kernel.stepBudget = steps;
    kernel.maxQuerySteps = steps;
    kernel.setStepBudget(steps);
    kernel.setDeadline(30000);
    const before = { work: kernel.work().querySteps, arena: kernel.arena() };
    let outcome, result;
    const started = performance.now();
    try {
      result = kernel.normalize(expression);
      outcome = { status: "normalized" };
    } catch (error) {
      if (!["budget", "resource", "deadline"].includes(error.kind)) throw error;
      outcome = { status: "limited", kind: error.kind, message: error.message };
    }
    const ms = performance.now() - started;
    const after = { work: kernel.work().querySteps, arena: kernel.arena() };
    let normal = null;
    if (result) {
      // Count reachable handles including annotations, preserving sharing.
      const pending = [[result, false]], depth = new Map(), deadline = performance.now() + 30000;
      let visits = 0;
      while (pending.length) {
        if (++visits > 10000000 || (visits % 1024 === 0 && performance.now() >= deadline))
          throw new Error("Normal-form graph inspection exceeded its independent bound.");
        const [id, done] = pending.pop();
        if (!id || depth.has(id)) continue;
        const node = kernel.node(id);
        if (done) depth.set(id, 1 + Math.max(0, ...node.children.map(c => depth.get(c) ?? 0)));
        else {
          pending.push([id, true]);
          for (const child of node.children) if (child && !depth.has(child)) pending.push([child, false]);
        }
      }
      normal = { nodes: depth.size, depth: depth.get(result) };
    }
    console.log(JSON.stringify({ case: name, budget: String(steps), ...outcome,
      querySteps: after.work - before.work, allocatedNodes: after.arena.nodes - before.arena.nodes,
      arena: after.arena, normal, ms, fixtureHash, kernelHash, dependencyHash }));
  } finally {
    program.dispose();
  }
}
