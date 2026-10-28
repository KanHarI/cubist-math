// One workload in a fresh process: its kernel work, time, outcome and the
// process's peak memory (docs/reports/driver-derivation-sharing.md). ROOT
// is a checkout whose web/dist is built.
//   node probe.mjs ROOT SETUP ENTRY   one REPL entry after a setup, as
//     node docs/reports/driver-derivation-sharing/probe.mjs . \
//       "import binary_rationals; use binary_rationals;" "evaluate 1/2 expecting 1/2;"
//   node probe.mjs ROOT --file PATH   a file checked as a program, in test
//     mode, with a digest of its outcomes
//   node probe.mjs ROOT --audit       the archive, as tools/audit-cubical.mjs --all
import { readFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import { resolve } from "node:path";
import { pathToFileURL } from "node:url";
const [root, mode, argument] = process.argv.slice(2);
const at = path => pathToFileURL(resolve(root, path)).href;
const { default: createCubical } = await import(at("web/dist/cubical.mjs"));
const { CubicalProgram } = await import(at("web/cubical-program.mjs"));
const { ReplSession } = await import(at("web/repl-session.mjs"));
const { sourceReader, archiveReader } = await import(at("tools/module-sources.mjs"));
const { archiveModules } = await import(at("web/cubist/modules.mjs"));
const program = mode === "--audit" ? new CubicalProgram(await createCubical(), archiveReader("audit"))
  : new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false, testMode: mode === "--file" });
const measured = async (label, run) => {
  const before = program.kernel.work(), started = performance.now();
  const outcome = await run();
  const after = program.kernel.work();
  console.log(JSON.stringify({ ...label, ...outcome, ms: Math.round(performance.now() - started),
    instructions: after.instructions - before.instructions, instructionSteps: Number(after.instructionSteps - before.instructionSteps),
    queries: after.queries - before.queries, querySteps: Number(after.querySteps - before.querySteps),
    maxRssMiB: Math.round(process.resourceUsage().maxRSS / 1024) }));
};
try {
  if (mode === "--audit") {
    await measured({ workload: "audit --all" }, async () => {
      await program.checkModules(archiveModules, "audit", () => {});
      const entries = Object.values(program.symbols);
      return { checked: entries.filter(d => d.verified).length,
        failures: entries.filter(d => !d.verified).length + program.gaps.filter(g => g.directive || g.duplicate).length };
    });
  } else if (mode === "--file") {
    const source = await readFile(argument, "utf8");
    await measured({ file: argument.split("/").pop() }, async () => {
      const result = await program.check(source, argument.split("/").pop().replace(/\.cubist$/, ""));
      const outputs = result.outputs.map(o => `${o.name}:${o.verified ? "ok" : o.reason}`);
      const evaluations = result.evaluations.map(e => e.value ?? ""), gaps = result.gaps.map(g => g.message ?? g.text ?? JSON.stringify(g));
      const prints = result.prints.map(p => p.text ?? p.value ?? "");
      return { outputs: outputs.length, failed: outputs.filter(o => !o.endsWith(":ok")).length, evaluations: evaluations.length,
        gaps: gaps.length, prints: prints.length,
        outcomeDigest: createHash("sha256").update(JSON.stringify([outputs, evaluations, gaps, prints])).digest("hex").slice(0, 16) };
    });
  } else {
    const session = new ReplSession(program);
    const prepared = await session.run(mode);
    const failed = prepared.find(answer => answer.kind === "error");
    if (failed) throw new Error(failed.text);
    await measured({ entry: argument }, async () => ({ outcome: (await session.run(argument))[0].text.slice(0, 200) }));
  }
} finally { program.dispose(); }
