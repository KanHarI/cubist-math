import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { selectTests, loadProof, changedProofs, projectRoot, defaultTests } from "../tools/test-selection.mjs";

const runner = resolve(projectRoot, "tools/test.mjs");

test("target selection keeps the full suite opt-in by omission and forwards Node filters", () => {
  assert.deepEqual(selectTests([]).tests, defaultTests.map(p => resolve(projectRoot, p)));
  const filtered = selectTests(["--test-name-pattern", "complex inverses", "tests/mathscript.test.mjs"]);
  assert.deepEqual(filtered.flags, ["--test-name-pattern", "complex inverses"]);
  assert.deepEqual(filtered.tests, [resolve(projectRoot, "tests/mathscript.test.mjs")]);
  assert.deepEqual(filtered.proofs, []);
  assert.deepEqual(selectTests(["--test-name-pattern=loader", "tests/workbench.test.mjs"]).flags, ["--test-name-pattern=loader"]);
});

test("proof selection deduplicates module names and paths without enabling full regressions", () => {
  const selected = selectTests(["field_products", "--module=field_products", "web/proofs/field_products.proof"]);
  assert.deepEqual(selected.proofs, [resolve(projectRoot, "web/proofs/field_products.proof")]);
  assert.deepEqual(selected.tests, [resolve(projectRoot, "tests/proof-modules.test.mjs")]);
  assert.throws(() => selectTests(["--module"]), /needs/);
  assert.throws(() => selectTests(["--test-name-pattern"]), /needs/);
  assert.throws(() => selectTests(["field_products", "--test-name-pattern=nothing"]), /silently skipped/);
  assert.throws(() => selectTests(["not-a-proof.txt"]), /Expected a proof/);
  assert.deepEqual(selectTests(["--changed"], { changed: () => [] }).tests, []);
  assert.deepEqual(selectTests(["--help"]), { help: true });
});

test("compiler optimizations default on with independent ordered CLI overrides", () => {
  assert.deepEqual(selectTests(["basics"]).optimizations, { normalForms: true, instructions: true });
  assert.deepEqual(selectTests(["--no-reuse-normal-forms", "basics"]).optimizations, { normalForms: false, instructions: true });
  assert.deepEqual(selectTests(["--no-memoize-instructions", "basics"]).optimizations, { normalForms: true, instructions: false });
  const neither = selectTests(["--no-reuse-normal-forms", "--no-memoize-instructions", "basics"]);
  assert.deepEqual(neither.optimizations, { normalForms: false, instructions: false });
  assert.deepEqual(neither.flags, []);
  assert.deepEqual(selectTests(["--no-reuse-normal-forms", "--reuse-normal-forms", "basics"]).optimizations,
    { normalForms: true, instructions: true });
  assert.deepEqual(selectTests(["--memoize-instructions", "--no-memoize-instructions", "basics"]).optimizations,
    { normalForms: true, instructions: false });
  assert.throws(() => selectTests(["--reuse-normal-forms"]), /require selected proof modules/);
  assert.throws(() => selectTests(["--no-reuse-normal-forms"]), /require selected proof modules/);
});

test("selected proofs load only transitive imports and tolerate cycles for compiler diagnostics", async t => {
  const root = await mkdtemp(join(tmpdir(), "mathscript-imports-"));
  t.after(() => rm(root, { recursive: true, force: true }));
  await mkdir(join(root, "web/proofs"), { recursive: true });
  await writeFile(join(root, "web/proofs/a.proof"), "import b; import prelude; def a = tt;");
  await writeFile(join(root, "web/proofs/b.proof"), "// import missing;\nimport a; def b = tt;");
  const path = join(root, "root.proof");
  await writeFile(path, "import a; theorem root : Unit { exact tt; }");
  const loaded = await loadProof(path, root);
  assert.deepEqual(Object.keys(loaded.sources).sort(), ["a", "b"]);
  assert.match(loaded.source, /theorem root/);
  assert.equal(loaded.label, "root.proof");
});

test("changed-proof selection includes staged, unstaged and untracked files only", async t => {
  const root = await mkdtemp(join(tmpdir(), "mathscript-changed-"));
  t.after(() => rm(root, { recursive: true, force: true }));
  const git = (...args) => {
    const result = spawnSync("git", args, { cwd: root, encoding: "utf8" });
    assert.equal(result.status, 0, result.stderr);
  };
  git("init", "-q");
  await writeFile(join(root, "tracked.proof"), "def initial = tt;\n");
  git("add", "tracked.proof");
  git("-c", "user.name=Test", "-c", "user.email=test@example.invalid", "commit", "-qm", "fixture");
  await writeFile(join(root, "tracked.proof"), "def modified = tt;\n");
  await writeFile(join(root, "staged.proof"), "def staged = tt;\n");
  git("add", "staged.proof");
  await writeFile(join(root, "untracked space.proof"), "def untracked = tt;\n");
  await writeFile(join(root, "unrelated.mjs"), "// not a proof\n");
  assert.deepEqual(changedProofs(root).sort(), ["staged.proof", "tracked.proof", "untracked space.proof"]);
  assert.equal(selectTests(["--changed"], { root }).proofs.length, 3);
});

test("targeted CLI checks a small proof and propagates failures without running the library", async t => {
  const root = await mkdtemp(join(tmpdir(), "mathscript-runner-"));
  t.after(() => rm(root, { recursive: true, force: true }));
  const good = join(root, "good.proof"), bad = join(root, "bad.proof");
  await writeFile(good, "theorem good : Unit { exact tt; }");
  await writeFile(bad, "theorem bad : Void { exact tt; }");
  for (const [path, success] of [[good, true], [bad, false]]) {
    const result = spawnSync(process.execPath, [runner, path], { cwd: root, encoding: "utf8", timeout: 15000 });
    assert.equal(result.error, undefined);
    assert.equal(result.status === 0, success, result.stdout + result.stderr);
    assert.match(result.stdout, /tests 1|# tests 1/);
    assert.doesNotMatch(result.stdout, /prime development|audit translations|puncture graph/);
    if (success) assert.match(result.stdout, /0 source imports/);
  }
  const missing = spawnSync(process.execPath, [runner, "missing_module_for_test"], { encoding: "utf8", timeout: 5000 });
  assert.notEqual(missing.status, 0);
  assert.match(missing.stderr, /ENOENT/);
});
