// Ordinary-data runtime observations of the unchanged archive workload.
// Each sample uses a fresh process; no result is kernel evidence or a full NF.
import { execFileSync } from "node:child_process";
import { readFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { RuntimeQuery, RuntimeError } from "../web/cubical-runtime.mjs";
import { sourceReader } from "./module-sources.mjs";
import { assertFreshBuild, sourceHash } from "./build-stamp.mjs";

assertFreshBuild();
const input = Number(process.argv[2]);
if (process.argv.length === 2) {
  for (const n of [4, 5, 6]) execFileSync(process.execPath, [fileURLToPath(import.meta.url), String(n)], { stdio: "inherit" });
} else {
  if (process.argv.length !== 3 || ![4, 5, 6].includes(input)) throw new Error("Usage: node tools/shared-evaluation-probe.mjs [4|5|6]");
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  let query;
  try {
    const started = performance.now();
    const checked = await program.check(`import euclid; use unat; def probe := euclid(${input});`, "probe");
    if (!checked.complete) throw new Error(JSON.stringify(checked.gaps));
    const kernel = program.kernel, graph = new InstructionGraph(kernel);
    const typing = graph.lookup(kernel.definitions.get("probe__probe"));
    const checkMs = performance.now() - started, before = kernel.arena().nodes;
    const limits = { maxSteps: input === 6 ? 2000000 : 100000000, maxCells: 20000000, milliseconds: 30000 };
    const snapshotStart = performance.now();
    query = new RuntimeQuery(kernel, typing, limits);
    const snapshotMs = performance.now() - snapshotStart, observeStart = performance.now();
    let outcome;
    try {
      const pair = await query.observe();
      if (pair.kind !== "Pair") throw new Error("Expected the checked Euclid result pair.");
      let next = pair.first, result = 0;
      for (;;) {
        const value = await query.observe(next);
        if (value.kind !== "Con" || value.signature !== kernel.signatures.get("unat__UNat").index)
          throw new Error("Expected a unary natural observation.");
        if (value.index === 0 && value.args.length === 0) break;
        if (value.index !== 1 || value.args.length !== 1 || ++result > 1000)
          throw new Error("Unexpected unary observation.");
        next = value.args[0];
      }
      if (result !== ({ 4: 5, 5: 11, 6: 7 })[input]) throw new Error(`Unexpected prime ${result}.`);
      outcome = { status: "observed", result };
    } catch (error) {
      if (!(error instanceof RuntimeError) || !["budget", "resource", "deadline"].includes(error.kind)) throw error;
      outcome = { status: "limited", kind: error.kind, message: error.message };
    }
    const observeMs = performance.now() - observeStart, stats = query.stats;
    // Measure after recording execution stats; this walk consumes work and
    // temporary memory of its own. Skip the walk after a resource stop;
    // the sample's work budget may already be exhausted.
    const retained = outcome.status === "observed" ? query.retainedObjects() : null;
    const root = fileURLToPath(new URL("..", import.meta.url));
    console.log(JSON.stringify({ input, contract: "prime observation", ...outcome, limits, stats, retained,
      nativeNodes: kernel.arena().nodes - before, milliseconds: { check: checkMs, snapshot: snapshotMs, observe: observeMs },
      memoryAfterMeasurement: process.memoryUsage(), processMaxRssKiB: process.resourceUsage().maxRSS,
      revision: execFileSync("git", ["rev-parse", "HEAD"], { cwd: root, encoding: "utf8" }).trim(),
      modified: execFileSync("git", ["status", "--porcelain", "--untracked-files=normal"], { cwd: root, encoding: "utf8" }).trim() !== "",
      runtimeSha256: createHash("sha256").update(await readFile(new URL("../web/cubical-runtime.mjs", import.meta.url))).digest("hex"),
      kernelSourceHash: sourceHash("kernel"), node: process.version, platform: `${process.platform}/${process.arch}` }));
  } finally { query?.dispose(); program.dispose(); }
}
