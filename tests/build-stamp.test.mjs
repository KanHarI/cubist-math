// The build stamp (tools/build-stamp.mjs): web/dist fails loudly when it no
// longer matches its sources, its compiler or its outputs, instead of
// testing code it does not contain. The negative cases run on a small tree of
// the files each build reads and writes, in a temporary directory.
import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { appendFileSync, existsSync, mkdirSync, mkdtempSync, rmSync, truncateSync, writeFileSync } from "node:fs";
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
    "tools/build-cubical-runtime.mjs", "tools/build-stamp.mjs", "web/dist/cubical.mjs", "web/dist/cubical.wasm",
    ...runtimeModules.flatMap(name => [`lib/cubical/${name}.mjs`, `web/dist/cubical-runtime/${name}.mjs`])]) {
    mkdirSync(dirname(path(file)), { recursive: true });
    writeFileSync(path(file), file);
  }
  const stamp = buildStamp(pathToFileURL(`${root}/`));
  stamp.write("kernel", stamp.sourceHash("kernel"), configuration);
  stamp.write("runtime", stamp.sourceHash("runtime"));
  return { root, stamp, path };
}

// A command run with the fake tree as the one it checks.
const run = (root, args, extra = {}) => {
  const env = { ...process.env, CUBIST_BUILD_ROOT: root, ...extra };
  delete env.CUBIST_BUILD_LOCK;
  delete env.NODE_TEST_CONTEXT;
  return spawnSync(process.execPath, args, { cwd: repository, env, encoding: "utf8" });
};

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

test("the commands refuse a stale build", t => {
  const { root, path } = fakeTree(t);
  appendFileSync(path("kernel/src/a.c"), "\n");
  for (const args of [["tools/build-stamp.mjs", "check"], ["tools/test.mjs", "tests/build-stamp.test.mjs"],
    ["cli/repl.mjs", "check", "nothing"], ["tools/instruction-coverage.mjs", "--select=nothing"]]) {
    const result = run(root, args);
    assert.notEqual(result.status, 0, args.join(" "));
    assert.match(result.stderr, /web\/dist is stale: the kernel sources changed/, args.join(" "));
  }
});

test("one build at a time: a live owner's lock is waited for, an exited owner's taken over", t => {
  const { root, path } = fakeTree(t);
  const owner = path("web/dist/.build-lock/owner");
  mkdirSync(dirname(owner), { recursive: true });
  writeFileSync(owner, String(process.pid));
  const waited = run(root, ["tools/build-stamp.mjs", "locked", "--", process.execPath, "-e", "0"], { CUBIST_BUILD_LOCK_TIMEOUT_MS: "300" });
  assert.equal(waited.status, 1);
  assert.match(waited.stderr, /Timed out waiting for another build/);
  const exited = spawnSync(process.execPath, ["-e", "0"]).pid;
  writeFileSync(owner, String(exited));
  const taken = run(root, ["tools/build-stamp.mjs", "locked", "--", process.execPath, "-e", "process.exit(3)"]);
  assert.equal(taken.status, 3, taken.stderr);
  assert.equal(existsSync(owner), false, "the lock is released");
});

test("the build under test matches its sources", () => {
  assert.deepEqual(staleBuilds(), []);
});
