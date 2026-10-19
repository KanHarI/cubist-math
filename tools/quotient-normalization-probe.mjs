// A bounded, arithmetic-free reproduction of the open rational-normalization
// problem. This measures full normalization of independently checked functions,
// not a projection, lazy observation, or a proof-of-inhabitation query.
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { MAX_QUERY_STEPS } from "../web/cubical-kernel.mjs";
import { sourceReader } from "./module-sources.mjs";
import { assertFreshBuild } from "./build-stamp.mjs";

assertFreshBuild();
const steps = BigInt(process.argv[2] ?? 10000000);
if (steps < 1n || steps > MAX_QUERY_STEPS)
  throw new Error(`Choose a positive step budget at most ${MAX_QUERY_STEPS}.`);
const source = await readFile(new URL("../tests/fixtures/generic-prop-normalization.cubist", import.meta.url), "utf8");
for (const name of ["to_unit", "to_prop"]) {
  // A fresh kernel prevents one case's failed query from warming the other's
  // reduction caches. The fixture's two functions are both checked each time.
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  try {
    const checked = await program.check(source, "normalization_probe");
    if (!checked.complete) throw new Error(JSON.stringify(checked.gaps));
    const derived = program.checker.checkSyntax({ tag: "DefRef", name: `normalization_probe__${name}` },
      null, new Map(), new Map());
    const kernel = program.kernel;
    kernel.stepBudget = steps;
    kernel.maxQuerySteps = steps; // No automatic retry with a larger budget.
    kernel.setStepBudget(steps);
    kernel.setDeadline(30000);
    const before = { steps: kernel.work().querySteps, nodes: kernel.arena().nodes };
    let outcome;
    try {
      kernel.normalize(derived.expression);
      outcome = { status: "normalized" };
    } catch (error) {
      if (!["budget", "deadline", "resource"].includes(error.kind)) throw error;
      outcome = { status: "limited", kind: error.kind, message: error.message };
    }
    console.log(JSON.stringify({ case: name, budget: String(steps), ...outcome,
      querySteps: kernel.work().querySteps - before.steps,
      allocatedNodes: kernel.arena().nodes - before.nodes }));
  } finally {
    program.dispose();
  }
}
