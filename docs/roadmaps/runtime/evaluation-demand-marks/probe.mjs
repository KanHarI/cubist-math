// Demand probes for the evaluation demand marks note beside this directory.
// Each query runs in a fresh checked program with a fixed budget, on main's
// library and archive only. For each named definition it records:
//   whnf:      cc_kernel_whnf of the definition, the proposed `!`
//   walk:      the proposed value form, by head queries: weak heads through
//              pairs, injections and constructor arguments, stopping at
//              lambdas, path lambdas, types, compositions and neutral heads
//   partGuard: whether the driver's normalize query accepts the handle of the
//              first part the walk reached (`!!` on a part)
//   normal:    cc_kernel_normalize of the definition, the proposed `!!` and
//              today's evaluation
// Usage: node probe.mjs [name,...] [budget]; names are `group/definition`.
import { createHash } from "node:crypto";
import createCubical from "../../../../web/dist/cubical.mjs";
import { CubicalProgram } from "../../../../web/cubical-program.mjs";
import { sourceReader } from "../../../../tools/module-sources.mjs";
import { assertFreshBuild, sourceHash } from "../../../../tools/build-stamp.mjs";

assertFreshBuild();
const sources = {
  // #302's main-only reproduction of the small inverse, without #283.
  rational: `import fractions;
import binary_integers;
use bnat;

def binary_rationals : Field(U0) := fraction_field(binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one);

def BQ : U0 := binary_rationals.R;

computable def two_thirds : BQ := match bint_decide_zero(bint_of_nat(3)) return BQ {
    left same => binary_rationals.zero;
    right nonzero => class((bint_of_nat(2), bint_of_nat(3), nonzero));
  };

computable def minus_two_thirds : BQ := binary_rationals.neg(two_thirds);

computable def small_inverse : BQ := q_inv{{U0}}(
  binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one, two_thirds
);

computable def small_inverse_neg : BQ := q_inv{{U0}}(
  binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one, minus_two_thirds
);
`,
  // The evaluation baseline's Euclid workloads, and lambdas the weak head
  // contracts by eta or keeps.
  euclid: `import euclid;
use unat;

def euclid_3 := euclid(3);

def euclid_4 := euclid(4);

def euclid_4_prime := euclid(4).1;

def eta_successor := fun (n : UNat) => succ(n);

def identity := fun (n : UNat) => n;
`,
};
const defaults = ["rational/two_thirds", "rational/small_inverse", "rational/small_inverse_neg",
  "euclid/euclid_3", "euclid/euclid_4", "euclid/euclid_4_prime", "euclid/eta_successor", "euclid/identity"];
const [namesText, budgetText = "100000000"] = process.argv.slice(2);
const names = namesText ? namesText.split(",") : defaults;
const budget = BigInt(budgetText);
const sha256 = text => createHash("sha256").update(text).digest("hex");
const identity = { kernelSourceHash: sourceHash("kernel"),
  fixtureSha256: Object.fromEntries(Object.entries(sources).map(([key, text]) => [key, sha256(text)])) };
const module = await createCubical();

async function fresh(group, name) {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  const checked = await program.check(sources[group], "probe");
  if (checked.gaps.length) throw new Error(JSON.stringify(checked.gaps.map(g => [g.name, g.code, g.reason])));
  const { expression } = program.checker.checkSyntax({ tag: "DefRef", name: `probe__${name}` }, null, new Map(), new Map());
  const kernel = program.kernel;
  kernel.stepBudget = budget;
  kernel.maxQuerySteps = budget;
  kernel.setStepBudget(budget);
  kernel.setDeadline(600000);
  return { program, kernel, expression };
}

const ticks = kernel => Number(kernel.work().querySteps);
function query(kernel, run) {
  const before = ticks(kernel);
  try { return { status: "done", handle: run(), ticks: ticks(kernel) - before }; }
  catch (error) {
    if (!["budget", "deadline", "resource", "other"].includes(error.kind)) throw error;
    return { status: "failed", kind: error.kind, message: error.message, ticks: ticks(kernel) - before };
  }
}

// A weak head's application spine: its root node and its arguments.
function spine(kernel, handle) {
  const args = [];
  let node = kernel.node(handle);
  while (node.kind === "App") { args.unshift(node.children[1]); node = kernel.node(node.children[0]); }
  return { root: node, args };
}

const types = new Set(["U", "Pi", "Sigma", "Path", "Sum", "Unit", "Void", "Glue", "Sort", "LPi"]);
function walk(kernel, root) {
  const stops = {}, before = ticks(kernel), pending = [root];
  let heads = 0, firstHead = null, firstPart = null, failure = null;
  const stop = key => { stops[key] = (stops[key] ?? 0) + 1; };
  while (pending.length) {
    const result = query(kernel, () => kernel.head(pending.pop()));
    if (result.status !== "done") { failure = `${result.kind}: ${result.message}`; break; }
    heads++;
    firstHead ??= result.ticks;
    const { root: node, args } = spine(kernel, result.handle);
    const parts = node.kind === "Pair" && !args.length ? [node.children[1], node.children[2]]
      : (node.kind === "Inl" || node.kind === "Inr") && !args.length ? [node.children[1]]
      : node.kind === "Con" ? args : null;
    if (parts) { pending.push(...[...parts].reverse()); firstPart ??= parts[0] ?? null; stop(node.kind); }
    else if (node.kind === "Point") stop("Point");
    else if (["Lam", "PLam", "LLam"].includes(node.kind) && !args.length) stop(`suspended ${node.kind}`);
    else if (types.has(node.kind)) stop(`type ${node.kind}`);
    else if (["Comp", "HComp", "Trans", "GlueTerm"].includes(node.kind)) stop(`formal ${node.kind}`);
    else stop(`neutral ${node.kind}`);
  }
  return { heads, firstHeadTicks: firstHead, ticks: ticks(kernel) - before, stops, failure, firstPart };
}

for (const name of names) {
  const [group, definition] = name.split("/");
  const record = { case: name, queryBudget: String(budget), ...identity };
  let run = await fresh(group, definition);
  try {
    const head = query(run.kernel, () => run.kernel.head(run.expression));
    record.whnf = head.status === "done"
      ? { kind: spine(run.kernel, head.handle).root.kind, arguments: spine(run.kernel, head.handle).args.length, ticks: head.ticks }
      : head;
  } finally { run.program.dispose(); }
  run = await fresh(group, definition);
  try {
    const { firstPart, ...walked } = walk(run.kernel, run.expression);
    record.walk = walked;
    if (firstPart) {
      try { run.kernel.normalize(firstPart); record.partGuard = "accepted"; }
      catch (error) { record.partGuard = `refused: ${error.message}`; }
    }
  } finally { run.program.dispose(); }
  run = await fresh(group, definition);
  try {
    const normal = query(run.kernel, () => run.kernel.normalize(run.expression));
    record.normal = normal.status === "done" ? { ticks: normal.ticks } : normal;
  } finally { run.program.dispose(); }
  console.log(JSON.stringify(record));
}
