// The build stamp (tools/build-stamp.mjs): web/dist fails loudly when it no
// longer matches its sources, its compiler or its outputs, instead of
// testing code it does not contain. The negative cases run on a small tree of
// the files each build reads and writes, in a temporary directory, with a copy
// of tools/build-stamp.mjs, which checks and locks the tree it lies in.
import test from "node:test";
import assert from "node:assert/strict";
import { spawn, spawnSync } from "node:child_process";
import { appendFileSync, copyFileSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync,
  truncateSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { buildStamp, hashOf, runtimeModules, sources, staleBuilds } from "../tools/build-stamp.mjs";

const repository = fileURLToPath(new URL("../", import.meta.url));
const configuration = "emcc 1.0\nemcc -O3";

function fakeTree(t) {
  const root = mkdtempSync(join(tmpdir(), "build-stamp-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const path = relative => join(root, relative);
  for (const file of ["kernel/src/a.c", "kernel/src/a.h", "kernel/include/k.h", "wasm/cubical_bridge.c", "Makefile",
    "tools/build-cubical-runtime.mjs", "web/dist/cubical.mjs", "web/dist/cubical.wasm",
    ...runtimeModules.flatMap(name => [`lib/cubical/${name}.mjs`, `web/dist/cubical-runtime/${name}.mjs`])]) {
    mkdirSync(dirname(path(file)), { recursive: true });
    writeFileSync(path(file), file);
  }
  copyFileSync(join(repository, "tools/build-stamp.mjs"), path("tools/build-stamp.mjs"));
  const stamp = buildStamp(pathToFileURL(`${root}/`));
  stamp.write("kernel", stamp.sourceHash("kernel"), configuration);
  stamp.write("runtime", stamp.sourceHash("runtime"));
  return { root, stamp, path };
}

// A command run as a child of no build and no test run.
const environment = (extra = {}) => {
  const env = { ...process.env };
  delete env.CUBIST_BUILD_LOCK;
  delete env.NODE_TEST_CONTEXT;
  return { ...env, ...extra };
};
const run = (args, extra) => spawnSync(process.execPath, args,
  { cwd: repository, env: environment(extra), encoding: "utf8", timeout: 120_000 });
const exitedProcess = () => spawnSync(process.execPath, ["-e", "0"]).pid;

test("the hash covers each source by path and content", () => {
  const files = new Map([["a.c", "int a;"], ["b.h", "int b;"]]);
  const read = path => files.get(path);
  const before = hashOf([...files.keys()], read);
  assert.equal(hashOf([...files.keys()], read), before, "deterministic");
  files.set("b.h", "int b2;");
  assert.notEqual(hashOf([...files.keys()], read), before, "a changed file");
  files.set("b.h", "int b;");
  assert.notEqual(hashOf(["a.c", "b.h", "c.c"], path => files.get(path) ?? ""), before, "an added file");
  assert.notEqual(hashOf(["b.h", "a.c"], read), before, "the order of paths is part of the hash");
});

test("each build's inputs include what changes its output", () => {
  const kernel = sources.kernel();
  for (const file of ["kernel/src/term_normalize.c", "kernel/src/term_internal.h", "kernel/include/cubical_kernel.h",
    "wasm/cubical_bridge.c", "Makefile"]) assert.ok(kernel.includes(file), file);
  const runtime = sources.runtime();
  assert.ok(runtimeModules.every(name => runtime.includes(`lib/cubical/${name}.mjs`)));
  assert.ok(runtime.includes("tools/build-cubical-runtime.mjs") && runtime.includes("tools/build-stamp.mjs"));
});

test("a stamped build is fresh, and every change to its inputs or outputs makes it stale", async t => {
  const changes = [
    ["a kernel source edited", ({ path }) => appendFileSync(path("kernel/src/a.c"), "\n"), /kernel sources changed/],
    ["a kernel source added", ({ path }) => writeFileSync(path("kernel/src/b.c"), ""), /kernel sources changed/],
    ["a translator module edited", ({ path }) => appendFileSync(path("lib/cubical/match.mjs"), "\n"), /runtime sources changed/],
    ["the copying generator edited", ({ path }) => appendFileSync(path("tools/build-cubical-runtime.mjs"), "\n"), /runtime sources changed/],
    ["the WASM missing", ({ path }) => rmSync(path("web/dist/cubical.wasm")), /cubical\.wasm is missing/],
    ["a copied module truncated", ({ path }) => truncateSync(path("web/dist/cubical-runtime/core.mjs")), /runtime outputs changed/],
    ["the stamp missing", ({ path }) => rmSync(path("web/dist/build-stamp.json")), /no kernel build is recorded/],
    ["a build under way", ({ stamp }) => stamp.invalidate("runtime"), /no runtime build is recorded/],
  ];
  for (const [what, change, reason] of changes) {
    const tree = fakeTree(t);
    assert.deepEqual(tree.stamp.staleBuilds(), [], `fresh before ${what}`);
    change(tree);
    assert.match(tree.stamp.staleBuilds().join("; "), reason, what);
    assert.throws(() => tree.stamp.assertFreshBuild(), /web\/dist is stale: .*Run make wasm\./, what);
  }
});

test("a source edited while its build ran, and another compiler, are caught", t => {
  const { stamp, path } = fakeTree(t);
  const hash = stamp.sourceHash("kernel");
  appendFileSync(path("kernel/src/a.c"), "/* edited during the build */\n");
  stamp.write("kernel", hash, configuration);
  assert.match(stamp.staleness("kernel"), /kernel sources changed/);
  stamp.write("kernel", stamp.sourceHash("kernel"), configuration);
  assert.equal(stamp.staleness("kernel", configuration), null);
  assert.match(stamp.staleness("kernel", "emcc 1.0\nemcc -O0 -g"), /another compiler or other flags/);
});

test("the check command checks the tree it lies in, by any path", t => {
  const { root, path } = fakeTree(t);
  const link = `${root}-link`;
  symlinkSync(root, link);
  t.after(() => rmSync(link, { force: true }));
  const checks = () => [path("tools/build-stamp.mjs"), join(link, "tools/build-stamp.mjs")].map(script => run([script, "check"]));
  for (const result of checks()) assert.equal(result.status, 0, "fresh");
  appendFileSync(path("kernel/src/a.c"), "\n");
  for (const result of checks()) {
    assert.equal(result.status, 1, "a check that ran");
    assert.match(result.stderr, /web\/dist is stale: the kernel sources changed/);
  }
});

// Every command that loads web/dist, run with a stand-in stamp that always
// finds it stale (tests/fixtures/stale-build.mjs): each must refuse.
test("every command that loads web/dist refuses a stale build", () => {
  const stale = args => run(["--import", "./tests/fixtures/stale-build.mjs", ...args]);
  const refusal = /web\/dist is stale: the test's stand-in says so/;
  const probe = stale(["--input-type=module", "-e", "import { assertFreshBuild } from './tools/build-stamp.mjs'; assertFreshBuild();"]);
  assert.match(probe.stderr, refusal, "the stand-in replaces the stamp");
  for (const args of [["cli/repl.mjs", "check", "nothing"], ["tools/test.mjs", "tests/source-tokens.test.mjs"],
    ["tools/instruction-coverage.mjs", "--select=nothing"], ["tools/audit-cubical.mjs"],
    ["tools/verify-proof-migration.mjs", "--no-dependents", "nothing"], ["tools/elaboration-fingerprint.mjs"],
    ["tools/search-fuel-baseline.mjs"], ["tools/benchmark-cubical.mjs", "nothing"], ["tools/build-site.mjs"],
    ["tools/differential-driver.mjs", "--seeds=1"], ["tests/cubical-inspector.browser.mjs"], ["tests/cubical.browser.mjs"], ["tests/statement.browser.mjs"],
    ["tests/proof-navigation.browser.mjs"], ["tests/landing.browser.mjs"]]) {
    const result = stale(args);
    assert.notEqual(result.status, 0, args.join(" "));
    assert.match(result.stderr, refusal, args.join(" "));
  }
});

test("one build at a time: a live owner's lock is waited for, an exited owner's taken over", t => {
  const { path } = fakeTree(t);
  const owner = path("web/dist/.build-lock/owner");
  const locked = (script, extra) => run([path("tools/build-stamp.mjs"), "locked", "--", process.execPath, "-e", script], extra);
  mkdirSync(dirname(owner), { recursive: true });
  writeFileSync(owner, String(process.pid));
  const waited = locked("0", { CUBIST_BUILD_LOCK_TIMEOUT_MS: "300" });
  assert.equal(waited.status, 1);
  assert.match(waited.stderr, /Timed out waiting for another build/);
  assert.equal(readFileSync(owner, "utf8"), String(process.pid), "a live owner's lock is left");
  writeFileSync(owner, String(exitedProcess()));
  const taken = locked("process.exit(3)");
  assert.equal(taken.status, 3, taken.stderr);
  assert.equal(existsSync(owner), false, "the lock is released");
  // A process claiming a lock it was not started under takes it like any other.
  const claimed = run([path("tools/build-stamp.mjs"), "locked", "--", process.execPath, "-e",
    `require("node:fs").writeFileSync(${JSON.stringify(path("held"))}, require("node:fs").readFileSync(${JSON.stringify(owner)}, "utf8"))`],
    { CUBIST_BUILD_LOCK: "1" });
  assert.equal(claimed.status, 0, claimed.stderr);
  assert.match(readFileSync(path("held"), "utf8"), /^[1-9]\d*$/);
  assert.notEqual(readFileSync(path("held"), "utf8"), "1");
});

test("a recoverer that saw an exited owner leaves a lock taken since, one at a time", t => {
  const { root, path } = fakeTree(t);
  const { recoverLock } = buildStamp(pathToFileURL(`${root}/`));
  const owner = path("web/dist/.build-lock/owner"), recoverer = path("web/dist/.build-lock-recovery/owner");
  const exited = exitedProcess();
  mkdirSync(dirname(owner), { recursive: true });
  writeFileSync(owner, String(process.pid));
  assert.equal(recoverLock(exited), true);
  assert.equal(readFileSync(owner, "utf8"), String(process.pid), "the lock another took since is left");
  writeFileSync(owner, String(exited));
  assert.equal(recoverLock(exited), true);
  assert.equal(existsSync(owner), false, "the exited owner's lock is removed");
  assert.equal(existsSync(dirname(recoverer)), false, "and the recovery's own lock");
  mkdirSync(dirname(recoverer));
  writeFileSync(recoverer, String(process.pid));
  assert.equal(recoverLock(exited), false, "a recovery under way is waited for");
  writeFileSync(recoverer, String(exited));
  assert.throws(() => recoverLock(exited), /exited while taking over an abandoned lock\. If no build is running, remove/);
});

test("builders racing for an exited owner's lock hold it one at a time", async t => {
  const { path } = fakeTree(t);
  const owner = path("web/dist/.build-lock/owner"), log = JSON.stringify(path("holders.log"));
  mkdirSync(dirname(owner), { recursive: true });
  writeFileSync(owner, String(exitedProcess()));
  const holder = `const { appendFileSync } = require("node:fs"); appendFileSync(${log}, "enter\\n");`
    + ` Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 200); appendFileSync(${log}, "leave\\n");`;
  const statuses = await Promise.all(Array.from({ length: 4 }, () => new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [path("tools/build-stamp.mjs"), "locked", "--", process.execPath, "-e", holder],
      { cwd: repository, env: environment(), stdio: "ignore" });
    child.on("error", reject);
    child.on("exit", resolve);
  })));
  assert.deepEqual(statuses, [0, 0, 0, 0]);
  assert.equal(readFileSync(path("holders.log"), "utf8"), "enter\nleave\n".repeat(4), "never two holders at once");
  assert.equal(existsSync(path("web/dist/.build-lock")), false);
  assert.equal(existsSync(path("web/dist/.build-lock-recovery")), false);
});

test("the build under test matches its sources", () => {
  assert.deepEqual(staleBuilds(), []);
});
