import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { testResults, mutationOutcome } from "../tools/frontend-test-results.mjs";

// Inject the same faults through the actual harnesses, including their
// controls. Check the structured mutation outcome, not just a helper's
// return value: a missing local declaration must never block classification.
test("all semantic harnesses classify local output loss and dependency failure consistently", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-observation-faults-"));
  t.after(() => rm(directory, {recursive:true,force:true}));
  const hook = join(directory,"fault.mjs");
  await writeFile(hook, `import {CubicalProgram} from ${JSON.stringify(new URL("../web/cubical-program.mjs",import.meta.url).href)};
const check = CubicalProgram.prototype.check;
CubicalProgram.prototype.check = async function (...args) {
  const result = await check.apply(this,args);
  if (process.env.CUBIST_OBSERVATION_FAULT === "dependency")
    result.gaps.push({module:"broken_fixture",name:"dependency",code:"E340",reason:"injected dependency failure"});
  if (process.env.CUBIST_OBSERVATION_FAULT === "output") {
    const target = ["identity","intended","initial_computation","checked","P"].find(name => result.outputs.some(output => output.name === name));
    if (!target) throw Error("fault needs a local output");
    result.outputs = result.outputs.filter(output => output.name !== target);
  }
  return result;
};\n`);
  const names = [
    "CB0: [ordered-header] later helpers cannot replace an earlier header parameter",
    "CB0 preservation: uncolliding parameter, seed 2",
    "control: [control-recursion] inherited recursive operations and initial-model clients compute",
    "CB0 migration control: helper-pattern-argument, intended reading",
    "CB0 migration control: helper-pattern-argument, captured reading",
    "CB0 migration control: imported-pattern-rename, captured reading",
    "CB0: simp_rule ignores opened labels (local registration)",
    "CB0: simp_rule ignores opened labels (imported registration)",
  ];
  const pattern = `^(?:${names.map(name => name.replace(/[.*+?^${}()|[\]\\]/g,"\\$&")).join("|")})$`;
  const env = {...process.env,CUBIST_GENERATION_CASES:"3"};
  delete env.NODE_TEST_CONTEXT;
  delete env.CUBIST_GENERATION_STRICT;
  const files = ["capture-bindings","frontend-invariants","frontend-generation","capture-refusals"]
    .map(name => fileURLToPath(new URL(`./${name}.test.mjs`,import.meta.url)));
  const run = fault => {
    const child = spawnSync(process.execPath,["--import",hook,"--test",
      `--test-reporter=${fileURLToPath(new URL("../tools/frontend-test-reporter.mjs",import.meta.url))}`,
      `--test-name-pattern=${pattern}`,...files],
    {env:{...env,CUBIST_OBSERVATION_FAULT:fault},encoding:"utf8",timeout:60000,maxBuffer:4*1024*1024});
    return {status:child.status,signal:child.signal,error:child.error?.message,log:child.stdout};
  };
  const baseline = testResults(run("none"));
  assert.ok(!baseline.invalid, baseline.invalid);
  assert.deepEqual(baseline.failed, []);
  assert.deepEqual(baseline.passed.sort(), [...names].sort());
  for (const [fault,outcome] of [["output","killed"],["dependency","precondition"]]) {
    const result = mutationOutcome(run(fault),baseline.passed);
    assert.equal(result.outcome,outcome,JSON.stringify(result));
    assert.deepEqual(result.failedTests.sort(),[...names].sort());
  }
});
