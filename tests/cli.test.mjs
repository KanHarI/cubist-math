import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
const cli = fileURLToPath(new URL("../cli/repl.mjs", import.meta.url));
const run = (args, options = {}) => spawnSync(process.execPath, [cli, ...args], { encoding: "utf8", timeout: 30000, ...options });
test("CLI checks custom sibling imports, rejects false proofs, and explores actual native terms", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-cli-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "helper.cubist"), "def identity(n : Nat) := n;");
  await writeFile(join(directory, "example.cubist"), "import helper; def self_equal(n : Nat) : n =[Nat] n { exact refl(identity(n)); }");
  await writeFile(join(directory, "bad.cubist"), "def false_claim : 0 = 1 { exact refl(0); }");
  const good = run(["check", "example.cubist"], { cwd: directory });
  assert.equal(good.status, 0, good.stderr); assert.match(good.stdout, /Checked 1 declarations/);
  const bad = run(["check", "bad.cubist"], { cwd: directory }); assert.notEqual(bad.status, 0);
  const shell = run([], { cwd: directory, input: "check example.cubist\ninspect self_equal\nassembly self_equal\ninspect identity\nbeta expression\ndelta type\nquit\n" });
  assert.equal(shell.status, 0, shell.stderr); assert.equal(shell.stderr, "");
  assert.match(shell.stdout, /Expression:/); assert.match(shell.stdout, /CC_(LAM|PATH)/);
  assert.match(run(["--help"]).stdout, /FILE.cubist/);
});
test("CLI reports assumptions and evaluates closed terms", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-cli-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "sample.cubist"), `import primes;
import classical;
def double(n : Nat) := n + n;
def recover(P : U0, prop : Proposition(P), nn : (P -> Void) -> Void) : P {
  exact double_negation(P, prop, nn);
}
evaluate double(2) expecting 4;
`);
  const shell = run([], { cwd: directory, input: "check sample.cubist\ninspect double\ninspect recover\n" +
    "evaluate double(3)\nevaluate recover\nevaluate missing_name\nquit\n" });
  assert.equal(shell.status, 0, shell.stderr);
  assert.match(shell.stdout, /evaluate at line 7: 4\n/);
  assert.match(shell.stdout, /Type: .*\nAssumptions: none\n/);
  assert.match(shell.stdout, /Assumptions: LEM\(U0\), Truncate\(U0\), TruncateElim\(U0\)\n/);
  assert.match(shell.stdout, /\n6\n/);
  assert.match(shell.stderr, /The evaluated term depends on non-computing assumptions: LEM\(U0\).*Path to LEM\(U0\): recover \(sample\) → double_negation \(classical\) → LEM\(U0\)\./);
  assert.match(shell.stderr, /missing_name/);
});
