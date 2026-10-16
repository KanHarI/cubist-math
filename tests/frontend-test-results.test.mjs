import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { spawnSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { testResults, mutationOutcome } from "../tools/frontend-test-results.mjs";

const reporter = fileURLToPath(new URL("../tools/frontend-test-reporter.mjs", import.meta.url));
test("mutation evidence distinguishes active assertions from TODOs and process failures", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-test-events-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const file = join(directory, "case.test.mjs"), env = { ...process.env };
  delete env.NODE_TEST_CONTEXT;
  const todo = 'test("known", {todo:true}, () => assert.equal(1,2));';
  const pass = 'test("contract", () => assert.equal(1,1));';
  const fail = 'test("contract", () => assert.equal(1,2));';
  const crash = 'test("crash", () => { throw new TypeError("broken"); });';
  const blocked = 'test("contract", () => { throw Object.assign(new Error("fixture failed", {cause:new assert.AssertionError({message:"precondition"})}), {code:"ERR_TEST_PRECONDITION"}); });';
  async function run(source) {
    await writeFile(file, `import test from "node:test"; import assert from "node:assert/strict"; ${source}`);
    const child = spawnSync(process.execPath, ["--test", `--test-reporter=${reporter}`, file],
      { env, encoding:"utf8", timeout:10000 });
    return { status:child.status, signal:child.signal, error:child.error?.message, log:child.stdout };
  }
  const baseline = testResults(await run(todo + pass));
  assert.ok(!baseline.invalid);
  assert.deepEqual(baseline.passed, ["contract"]);
  for (const [source, outcome] of [
    [todo + pass, "survived"], [todo + fail, "killed"],
    [todo + crash, "invalid"], [todo + fail + crash, "invalid"],
    [todo, "invalid"], ['test("unrelated", () => assert.equal(1,2));', "invalid"],
    [todo + blocked, "precondition"], [blocked + crash, "invalid"],
  ]) {
    const observed = mutationOutcome(await run(source), baseline.passed);
    assert.equal(observed.outcome, outcome, source);
    if (outcome === "killed") assert.deepEqual(observed.failedTests, ["contract"]);
  }
  const killed = await run(fail);
  const truncated = killed.log.trim().split("\n").slice(0, -1).join("\n");
  assert.equal(mutationOutcome({ ...killed, log:truncated }, baseline.passed).outcome, "invalid");
  assert.equal(mutationOutcome({ ...killed, signal:"SIGTERM" }, baseline.passed).outcome, "invalid");
});
