// Versioned EVAL4 inputs, measured with the ordinary kernel and its guards.
// Each case uses a fresh process and requests the complete function normal form.
import { execFileSync } from "node:child_process";
import { readFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "./module-sources.mjs";
import { assertFreshBuild, sourceHash } from "./build-stamp.mjs";

const cases = [32, 64, 128].flatMap(bits => [
  { name: `add_left_${bits}`, bits, fixture: "open-bnat-addition.cubist" },
  { name: `add_right_${bits}`, bits, fixture: "open-bnat-addition.cubist" },
  { name: `add_comm_${bits}`, bits, fixture: "open-bnat-bitwise-proof.cubist" },
]);
assertFreshBuild();
if (process.argv.length === 2) {
  for (const { name } of cases)
    execFileSync(process.execPath, [fileURLToPath(import.meta.url), name], { stdio: "inherit" });
} else {
  const selected = cases.find(c => c.name === process.argv[2]);
  if (process.argv.length !== 3 || !selected)
    throw new Error(`Choose one of: ${cases.map(c => c.name).join(", ")}. Omit it to run all cases.`);
  const source = await readFile(new URL(`../tests/fixtures/${selected.fixture}`, import.meta.url), "utf8");
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  try {
    const checked = await program.check(source, "depth_probe");
    if (!checked.complete) throw new Error(JSON.stringify(checked.gaps));
    const derived = program.checker.checkSyntax({ tag: "DefRef", name: `depth_probe__${selected.name}` },
      null, new Map(), new Map());
    const kernel = program.kernel, steps = 10000000n;
    kernel.stepBudget = steps; kernel.maxQuerySteps = steps; kernel.setStepBudget(steps);
    kernel.setDeadline(30000);
    const before = { work: kernel.work().querySteps, arena: kernel.arena() }, started = performance.now();
    let result, outcome;
    try { result = kernel.normalize(derived.expression); outcome = { status: "normalized" }; }
    catch (error) {
      if (!["budget", "deadline", "resource"].includes(error.kind)) throw error;
      outcome = { status: "limited", kind: error.kind, message: error.message };
    }
    const normalizeMs = performance.now() - started;
    const after = { work: kernel.work().querySteps, arena: kernel.arena() };
    // Output inspection is separate from the normalization counters. A failed
    // query has no output graph; allocated nodes must not masquerade as a NF.
    const normalForm = result ? graphSize(kernel, result) : null;
    const root = fileURLToPath(new URL("..", import.meta.url));
    const workingTreeStatus = execFileSync("git", ["status", "--porcelain", "--untracked-files=normal"],
      { cwd: root, encoding: "utf8" }).trimEnd();
    console.log(JSON.stringify({ ...selected, ...outcome, queryBudget: String(steps), deadlineMs: 30000,
      querySteps: after.work - before.work, allocatedNodes: after.arena.nodes - before.arena.nodes,
      normalForm, arenaBefore: before.arena, arenaAfter: after.arena, normalizeMs,
      memoryAfterInspection: process.memoryUsage(), processMaxRssKiB: process.resourceUsage().maxRSS,
      revision: execFileSync("git", ["rev-parse", "HEAD"], { cwd: root, encoding: "utf8" }).trim(),
      modified: workingTreeStatus !== "", workingTreeStatus,
      fixtureSha256: createHash("sha256").update(source).digest("hex"), kernelSourceHash: sourceHash("kernel"),
      node: process.version, platform: `${process.platform}/${process.arch}` }));
  } finally { program.dispose(); }
}

function graphSize(kernel, root) {
  const depths = new Map(), pending = [[root, false]], deadline = performance.now() + 30000;
  let visits = 0;
  while (pending.length) {
    if (++visits > 10000000 || (visits % 1024 === 0 && performance.now() >= deadline))
      throw new Error("Normal-form graph inspection exceeded its independent bound.");
    const [id, done] = pending.pop();
    if (!id || depths.has(id)) continue;
    const children = kernel.node(id).children;
    if (done) depths.set(id, 1 + Math.max(0, ...children.map(c => depths.get(c) ?? 0)));
    else {
      pending.push([id, true]);
      for (const child of children) if (child && !depths.has(child)) pending.push([child, false]);
    }
  }
  return { reachableNodes: depths.size, depth: depths.get(root) };
}
