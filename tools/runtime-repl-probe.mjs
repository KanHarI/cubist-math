// The REPL's value form computed by the runtime and by the kernel's head
// queries alone, for fixed workloads (docs/reports/runtime-repl-evaluation.md).
// Each sample, one workload by one path, is a fresh process, named or not:
// the setup is checked as a REPL session, then one `evaluate` entry is
// measured, so that the process's peak memory is that sample's alone.
// Neither path's answer is evidence.
// Before the runtime query is disposed of, its retained runtime objects are
// counted and the heap is measured after a collection (each sample's
// process runs with --expose-gc), so that retained memory is the query's
// live graph, not its garbage. That collection and count happen inside the
// entry, and their time is taken out of the entry's.
//   node tools/runtime-repl-probe.mjs                 every workload, both paths
//   node tools/runtime-repl-probe.mjs NAME[,NAME] [runtime|kernel]
import { execFileSync } from "node:child_process";
import { readFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { RuntimeQuery } from "../web/cubical-runtime.mjs";
import { sourceReader } from "./module-sources.mjs";
import { assertFreshBuild, sourceHash } from "./build-stamp.mjs";

export const workloads = {
  "euclid-3": ["import euclid; use unat;", "evaluate euclid(3);"],
  "euclid-4-prime": ["import euclid; use unat;", "evaluate euclid(4).1;"],
  "euclid-4": ["import euclid; use unat;", "evaluate euclid(4);"],
  "euclid-5-prime": ["import euclid; use unat;", "evaluate euclid(5).1;"],
  "euclid-6-prime": ["import euclid; use unat;", "evaluate euclid(6).1;"],
  // An exact expected value is compared by the kernel's queries on either path.
  "euclid-3-expecting": ["import euclid; use unat;", "evaluate euclid(3).1 expecting 7;"],
  "euclid-5-expecting": ["import euclid; use unat;", "evaluate euclid(5).1 expecting 11;"],
  // The library's binary Euclid (library/binary_euclid.cubist), a separate
  // source-algorithm series (docs/reports/binary-euclid.md).
  "binary-euclid-3": ["import binary_euclid; use nat;", "evaluate euclid(3);"],
  "binary-euclid-4-prime": ["import binary_euclid; use nat;", "evaluate euclid(4).1;"],
  "binary-euclid-4": ["import binary_euclid; use nat;", "evaluate euclid(4);"],
  "binary-euclid-5-prime": ["import binary_euclid; use nat;", "evaluate euclid(5).1;"],
  "binary-euclid-6-prime": ["import binary_euclid; use nat;", "evaluate euclid(6).1;"],
  "binary-euclid-10-prime": ["import binary_euclid; use nat;", "evaluate euclid(10).1;"],
  // 7! + 1 = 71 * 71: the search's 70 candidates pass the kernel's depth guard.
  "binary-euclid-7-prime": ["import binary_euclid; use nat;", "evaluate euclid(7).1;"],
  "binary-euclid-3-expecting": ["import binary_euclid; use nat;", "evaluate euclid(3).1 expecting 7;"],
  "binary-euclid-5-expecting": ["import binary_euclid; use nat;", "evaluate euclid(5).1 expecting 11;"],
  "binary-euclid-5-folded": ["import binary_euclid; use nat;", "evaluate !!euclid(5);"],
  "unary-510": ["import unat; use unat;", "evaluate typed(UNat and UNat, (2 * 255, 2 * 255));"],
  // An accumulator the kernel substitutes into each call, past its syntax
  // depth (web/reference/checking.html#print).
  "count-into-510": ["import unat; use unat; def count_into(n, total : UNat) : UNat := match n { zero => total; succ(k) => count_into(k, succ(total)); };",
    "evaluate count_into(2 * 255, 0);"],
  // A list the definition retains while its parity forces every cell: the
  // runtime's allocation cap with its cells retained.
  "list-parity-200000": ["import lists; use unat; inductive Lamp { dark; lit; } "
    + "def toggle(f : Lamp) : Lamp := match f { dark => lit; lit => dark; }; "
    + "def rep(n : UNat) : List(U0, Unit) := match n { zero => nil; succ(m) => cons(tt, rep(m)); }; "
    + "def parity(xs : List(U0, Unit)) : Lamp := induction xs return Lamp { nil => dark; cons(x, rest) with below => toggle(below); }; "
    + "def big : List(U0, Unit) := rep(100 * 100 * 20);", "evaluate parity(big);"],
  // The same recursive call twice: structural recursion shares it as one
  // hypothesis.
  "unary-doubling-8": ["import unat; use unat; def doubling(n : UNat) : UNat := match n { zero => 1; succ(m) => doubling(m) + doubling(m); };",
    "evaluate doubling(8);"],
  // The same non-recursive call twice, through 24 definitions: the kernel
  // caches weak heads by shared syntax, so each g_i(tt) is computed once;
  // the runtime shares a thunk by occurrence, so g_24(tt) costs 2^24 calls.
  "duplicated-calls-24": [["def both(a, b : Unit) : Unit := unit_induction(fun (x : Unit) => Unit, b, a);",
    "def g0(u : Unit) : Unit := u;",
    ...Array.from({ length: 24 }, (_, i) => `def g${i + 1}(u : Unit) : Unit := both(g${i}(u), g${i}(u));`)].join(" "),
    "evaluate g24(tt);"],
  "binary-factorial-40": ["import nat; use nat;", "evaluate factorial(40);"],
  "binary-product": ["import nat; use nat;", "evaluate 12345678901234567890 * 98765432109876543210;"],
  "binary-rational": ["import binary_rationals; use binary_rationals;", "evaluate 2/3 + 1/6;"],
  // Binary integers and rationals are set quotients: their point
  // constructors execute in the runtime, and a path constructor falls back.
  "binary-rational-wide-inverse": ["import binary_rationals; use binary_rationals;",
    "evaluate bq_inv(-340282366920938463463374607431768211455/18446744073709551615);"],
  "binary-rational-distinct": ["import binary_rationals; use binary_rationals;", "evaluate bq_decide(1/2, 2/3);"],
  "binary-rational-equal": ["import binary_rationals; use binary_rationals;", "evaluate bq_decide(1/2 + 1/3, 5/6);"],
  "binary-integer-wide-product": ["import binary_integers; use binary_integers;",
    "evaluate 340282366920938463463374607431768211455 * 340282366920938463463374607431768211455;"],
  "binary-integer-distinct": ["import binary_integers; use binary_integers;",
    "evaluate bint_decide(340282366920938463463374607431768211455, -1);"],
};

assertFreshBuild();
const args = process.argv.slice(2), child = args[0] === "--child";
const [names, only] = child ? args.slice(1) : args;
const root = fileURLToPath(new URL("..", import.meta.url));
const selected = (names ? names.split(",") : Object.keys(workloads)).flatMap(name => (only ? [only] : ["runtime", "kernel"]).map(path => {
  if (!workloads[name] || !["runtime", "kernel"].includes(path)) throw new Error(`Unknown workload or path: ${name} ${path}`);
  return [name, path];
}));
if (!child) {
  for (const [name, path] of selected)
    execFileSync(process.execPath, ["--expose-gc", fileURLToPath(import.meta.url), "--child", name, path], { stdio: "inherit" });
} else {
  if (selected.length !== 1) throw new Error("A child process measures one workload by one path.");
  for (const [name, path] of selected) {
    const [setup, entry] = workloads[name];
    const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false, runtimeEvaluation: path === "runtime" });
    try {
      const session = new ReplSession(program);
      const prepared = await session.run(setup);
      const failed = prepared.find(result => result.kind === "error");
      if (failed) throw new Error(failed.text);
      globalThis.gc?.();
      const before = { work: program.kernel.work(), arena: program.kernel.arena().nodes, heap: process.memoryUsage().heapUsed };
      let captured = null, retained = null, measuring = 0;
      const dispose = RuntimeQuery.prototype.dispose;
      RuntimeQuery.prototype.dispose = function () {
        const measured = performance.now();
        globalThis.gc?.();
        retained = { heapMiB: +((process.memoryUsage().heapUsed - before.heap) / 1048576).toFixed(1) };
        try { Object.assign(retained, this.retainedObjects()); } catch (error) { retained.walk = error.kind; }
        measuring += performance.now() - measured;
        return dispose.call(this);
      };
      const check = program.checkEntry.bind(program);
      program.checkEntry = async (...args) => (captured = await check(...args));
      const started = performance.now(), [answer] = await session.run(entry), elapsed = performance.now() - started - measuring;
      const after = program.kernel.work();
      globalThis.gc?.();
      console.log(JSON.stringify({ workload: name, path, entry, result: answer.text.slice(0, 120), kind: answer.kind,
        computedBy: captured?.prints?.at(-1)?.valueForm ?? null, retained, milliseconds: Math.round(elapsed),
        kernelQuerySteps: Number(after.querySteps - before.work.querySteps), kernelQueries: Number(after.queries - before.work.queries),
        arenaNodes: program.kernel.arena().nodes - before.arena,
        heapAfterGcMiB: +((process.memoryUsage().heapUsed - before.heap) / 1048576).toFixed(1),
        processMaxRssMiB: Math.round(process.resourceUsage().maxRSS / 1024),
        revision: execFileSync("git", ["rev-parse", "--short", "HEAD"], { cwd: root, encoding: "utf8" }).trim(),
        modified: execFileSync("git", ["status", "--porcelain", "--untracked-files=normal"], { cwd: root, encoding: "utf8" }).trim() !== "",
        runtimeSha256: createHash("sha256").update(await readFile(new URL("../web/cubical-runtime.mjs", import.meta.url))).digest("hex").slice(0, 16),
        kernelSourceHash: sourceHash("kernel").slice(0, 16), node: process.version, platform: `${process.platform}/${process.arch}` }));
    } finally { program.dispose(); }
  }
}
