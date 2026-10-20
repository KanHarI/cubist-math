// Retained diagnostic for the report beside this directory. It performs one
// full-normalization query with a fixed budget, without BQ or source overlays.
import { readFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import createCubical from "../../../web/dist/cubical.mjs";
import { CubicalProgram } from "../../../web/cubical-program.mjs";
import { sourceReader } from "../../../tools/module-sources.mjs";
import { assertFreshBuild, sourceHash } from "../../../tools/build-stamp.mjs";

assertFreshBuild();
const root = fileURLToPath(new URL("../../../", import.meta.url));
const source = `import fractions;
import binary_integers;

def relation := SameRatio{{U0}}(binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one);
`;
const sha256 = text => createHash("sha256").update(text).digest("hex");
const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
try {
  const checked = await program.check(source, "same_ratio_probe");
  if (!checked.complete) throw new Error(JSON.stringify(checked.gaps));
  const derived = program.checker.checkSyntax({ tag: "DefRef", name: "same_ratio_probe__relation" },
    null, new Map(), new Map());
  const kernel = program.kernel, steps = 100000n;
  kernel.stepBudget = steps;
  kernel.maxQuerySteps = steps;
  kernel.setStepBudget(steps);
  kernel.setDeadline(30000);
  const before = { ticks: kernel.work().querySteps, arena: kernel.arena() };
  const started = performance.now();
  let outcome;
  try {
    kernel.normalize(derived.expression);
    outcome = { status: "normalized" };
  } catch (error) {
    if (!["budget", "deadline", "resource"].includes(error.kind)) throw error;
    outcome = { status: "limited", kind: error.kind, message: error.message };
  }
  const elapsedMs = performance.now() - started;
  const after = { ticks: kernel.work().querySteps, arena: kernel.arena() };
  console.log(JSON.stringify({ case: "SameRatio over binary_integers", ...outcome,
    queryBudget: String(steps), deadlineMs: 30000, querySteps: after.ticks - before.ticks,
    allocatedNodes: after.arena.nodes - before.arena.nodes,
    arenaBefore: before.arena, arenaAfter: after.arena, elapsedMs,
    revision: execFileSync("git", ["rev-parse", "HEAD"], { cwd: root, encoding: "utf8" }).trim(),
    kernelSourceHash: sourceHash("kernel"), fixtureSha256: sha256(source),
    probeSha256: sha256(await readFile(fileURLToPath(import.meta.url))),
    checkedSourceHashes: Object.fromEntries(Object.entries(program.sources).sort(([a], [b]) => a.localeCompare(b))
      .map(([name, text]) => [name, sha256(text)])),
    node: process.version, platform: `${process.platform}/${process.arch}` }, null, 2));
} finally {
  program.dispose();
}
