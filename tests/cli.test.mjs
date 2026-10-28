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
  await writeFile(join(directory, "helper.cubist"), "import unat; def identity(n : UNat) := n;");
  await writeFile(join(directory, "example.cubist"), "import unat; import helper; def self_equal(n : UNat) : n =[UNat] n { exact refl(identity(n)); }");
  await writeFile(join(directory, "bad.cubist"), "import unat; def false_claim : 0 = 1 { exact refl(0); }");
  const good = run(["check", "example.cubist"], { cwd: directory });
  assert.equal(good.status, 0, good.stderr); assert.match(good.stdout, /Checked 1 declarations/);
  const bad = run(["check", "bad.cubist"], { cwd: directory }); assert.notEqual(bad.status, 0);
  const shell = run([], { cwd: directory, input: "check example.cubist\ninspect self_equal\nassembly self_equal\ninspect identity\nbeta expression\ndelta type\nquit\n" });
  assert.equal(shell.status, 0, shell.stderr); assert.equal(shell.stderr, "");
  assert.match(shell.stdout, /Expression:/); assert.match(shell.stdout, /CC_(LAM|PATH)/);
  assert.match(run(["--help"]).stdout, /FILE.cubist/);
});
// A file whose name is no identifier is checked as the module its name
// gives (moduleOfFile), whose declarations module::name spells, and whose
// imports are its siblings.
test("CLI checks my-proof.cubist as the module my_proof", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-cli-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "helper.cubist"), "def h : Unit := tt;\n");
  await writeFile(join(directory, "my-proof.cubist"), "import helper;\ndef q : Unit := helper::h;\ndef g : Unit := my_proof::q;\n");
  const checked = run(["check", "my-proof.cubist"], { cwd: directory });
  assert.equal(checked.status, 0, checked.stderr); assert.match(checked.stdout, /Checked 2 declarations/);
  // The test runner checks a selected file as the CLI does.
  const env = { ...process.env };
  delete env.NODE_TEST_CONTEXT;
  const runner = spawnSync(process.execPath, [fileURLToPath(new URL("../tools/test.mjs", import.meta.url)), "--test-reporter=tap",
    join(directory, "my-proof.cubist")], { cwd: fileURLToPath(new URL("..", import.meta.url)), encoding: "utf8", timeout: 60000, env });
  assert.equal(runner.status, 0, runner.stdout + runner.stderr);
  assert.match(runner.stdout, /^ok 1 - cubical proof: my-proof\.cubist$/m);
});
test("CLI reports assumptions and evaluates closed terms", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-cli-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "sample.cubist"), `import primes;
import classical; use unat;
def double(n : UNat) := n + n;
def recover(P : U0, prop_ : Proposition(P), nn : (P -> Void) -> Void) : P {
  exact double_negation(P, prop_, nn);
}
evaluate double(2) expecting 4;
`);
  const shell = run([], { cwd: directory, input: "check sample.cubist\ninspect double\ninspect recover\n" +
    "evaluate double(3)\nevaluate recover\nevaluate missing_name\nquit\n" });
  assert.equal(shell.status, 0, shell.stderr);
  assert.match(shell.stdout, /evaluate at line 7: 4\n/);
  assert.match(shell.stdout, /Type: .*\nAssumptions: none\n/);
  assert.match(shell.stdout, /Assumptions: LEM\[Truncate\], Truncate, TruncateElim\n/);
  assert.match(shell.stdout, /\n6\n/);
  assert.match(shell.stderr, /The evaluated term depends on non-computing assumptions: LEM\[Truncate\].*Path to LEM\[Truncate\]: recover \(sample\) → double_negation \(classical\) → LEM\[Truncate\]\./);
  assert.match(shell.stderr, /missing_name/);
  // check reports each result that relies on an assumption, with all of them.
  assert.match(shell.stdout, /kernel steps\nrecover assumes LEM\[Truncate\], Truncate, TruncateElim\nevaluate at line 7/);
});
// A user's axiom, a library axiom and one reached through an import are
// reported with every result that relies on them; a result that relies on
// none is not reported.
// check checks the file and everything it imports: an import's failing
// declaration fails the check, though nothing the file uses fails (#317's
// review round 5, finding 2).
test("CLI check fails when an import fails a declaration", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-cli-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "dep.cubist"), "def bad : Void := tt;\ndef kept := tt;\n");
  await writeFile(join(directory, "main.cubist"), "import dep;\ndef use_ := kept;\n");
  const checked = run(["check", "main.cubist"], { cwd: directory });
  assert.notEqual(checked.status, 0, checked.stdout);
  assert.match(checked.stderr, /^error E606 at line 1:\d+ \(dep\.bad\): Type mismatch/m);
});

test("CLI check reports every assumption a result relies on, a user's axiom among them", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-cli-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "assumed.cubist"), "def Pointed := axiom Unit;\n");
  await writeFile(join(directory, "uses.cubist"), "import classical_axioms;\nimport assumed;\n"
    + "def both : ExcludedMiddle(U0) and Unit := (LEM(U0), Pointed);\ndef plain := tt;\ndef again := both;\n");
  const checked = run(["check", "uses.cubist"], { cwd: directory });
  assert.equal(checked.status, 0, checked.stderr);
  assert.match(checked.stdout, /kernel steps\nboth assumes LEM, assumed::Pointed\nagain assumes LEM, assumed::Pointed\n$/);
  // A print is a result too: it is followed by the assumptions its term
  // relies on, if any (#317's review round 2, finding 4).
  await writeFile(join(directory, "prints.cubist"), "import classical_axioms;\nimport assumed;\n"
    + "def plain := tt;\nprint(typeof(LEM(U0, Unit)));\nprint(inspect(Pointed));\nprint(typeof(plain));\n");
  const printed = run(["check", "prints.cubist"], { cwd: directory });
  assert.equal(printed.status, 0, printed.stderr);
  assert.match(printed.stdout, /^print typeof at line 4: .*\nprint typeof at line 4 assumes LEM\n/m);
  assert.match(printed.stdout, /^print inspect at line 5: .*\nprint inspect at line 5 assumes assumed::Pointed\n/m);
  assert.match(printed.stdout, /^print typeof at line 6: Unit\n?$/m);
  assert.doesNotMatch(printed.stdout, /line 6 assumes|plain assumes/);
});
// The H1 specification's 6.5: inspecting a declared type prints its signature
// in normal form and its eliminator's clause types, and no kernel extension
// since H1's release.
test("CLI inspects a declared type: its constructors and its eliminator", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-cli-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "circle.cubist"), "inductive S1 { base; loop : base = base; }\n");
  const shell = run([], { cwd: directory, input: "check circle.cubist\ninspect S1\nquit\n" });
  assert.equal(shell.status, 0, shell.stderr); assert.equal(shell.stderr, "");
  for (const line of ["inductive S1 : U0 (type)", "  base : S1  [0 data, 0 positions, 0 dimensions]",
    "  loop : base = base  [0 data, 0 positions, 1 dimension]", "Eliminator, for a motive P : S1 -> U:", "  base_case : P(base)",
    "  loop_case : PathP(fun (i : Interval) => P(loop @ i), base_case, base_case)", "Kernel extensions: none"])
    assert.ok(shell.stdout.split("\n").includes(line), `missing: ${line}\n${shell.stdout}`);
});

test("CLI refuses the removed --experimental option", () => {
  const shell = run(["--experimental=h1"], { input: "quit\n" });
  assert.equal(shell.status, 2);
  assert.match(shell.stderr, /--experimental was removed: declared types \(H1\) are on by default\./);
});
