import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { moduleReader, listedReader, searchOrder, placeOfPath } from "../web/module-resolution.mjs";
import { sourceReader, placeOfFile, projectRoot } from "../tools/module-sources.mjs";
import { selectTests, loadProof } from "../tools/test-selection.mjs";
import { budget } from "./timing.mjs";

// The resolution contract of web/module-resolution.mjs, which the CLI, the test
// runner, the library and reference tests and the browser worker share.

test("a module resolves its imports by where it lives", async () => {
  assert.deepEqual(searchOrder("archive"), ["archive"]);
  assert.deepEqual(searchOrder("library"), ["library", "archive"]);
  assert.deepEqual(searchOrder("local"), ["local", "library", "archive"]);
  assert.deepEqual(searchOrder(), ["library", "archive"], "a source that is not a file");
  assert.throws(() => searchOrder("elsewhere"), /Unknown module place/);
  assert.equal(placeOfPath("archive/first-library/euclid.cubist"), "archive");
  assert.equal(placeOfPath("library/naturals.cubist"), "library");
  assert.equal(placeOfPath("scratch/mine.cubist"), "local");
  assert.equal(placeOfFile(join(projectRoot, "archive/first-library/euclid.cubist")), "archive");

  const files = { "library/x": "library x", "archive/x": "archive x", "library/only": "library only",
    "local/helper": "local helper" };
  const reader = () => moduleReader((place, name) => files[`${place}/${name}`] ?? null);
  const source = reader();
  assert.equal(await source("x"), "library x", "the library shadows the archive");
  assert.equal(source.placeOf("x"), "library");
  const archive = reader();
  archive.place("main", "archive");
  assert.equal(await archive("x", "main"), "archive x", "an archive module never sees the library");
  await assert.rejects(archive("only", "main"),
    { message: "No module named only in archive/first-library/: an archive module imports only from the archive." });
  const local = reader();
  local.place("main", "local");
  assert.equal(await local("helper", "main"), "local helper");
  assert.equal(await local("x", "main"), "library x");
  await assert.rejects(local("missing", "main"),
    { message: "No module named missing in the checked file's directory, library/ or archive/first-library/." });
  // A REPL entry imports the checked file it runs on top of.
  assert.equal(await local.checkImports("repl_1", ["main", "x"]), null);
  // An archive module never sees a module this check loaded from the library.
  assert.equal(await source("only"), "library only");
  source.place("old", "archive");
  assert.equal(await source.checkImports("old", ["only"]), "old imports only, but archive/first-library/ has "
    + "no only; this check loaded only from library/, which old does not see.");
  await assert.rejects(source("missing"), { message: "No module named missing in library/ or archive/first-library/." });

  // The browser knows modules by name: a listed module is fetched from its root.
  const fetched = [];
  const listed = listedReader({ library: ["x"], archive: ["x", "a"] },
    async path => { fetched.push(path); return path; }, "a");
  assert.equal(listed.placeOf("a"), "archive");
  assert.equal(await listed("x", "a"), "archive/first-library/x.cubist");
  assert.equal(await listedReader({ library: ["x"], archive: ["x"] }, async path => path)("x"), "library/x.cubist");
  assert.deepEqual(fetched, ["archive/first-library/x.cubist"], "an unlisted place is never fetched");
});

// A repository-shaped directory with a module x in both roots, an archive
// module a that imports x, and a local directory with its own x.
async function fixture(t) {
  const root = await mkdtemp(join(tmpdir(), "cubist-resolution-"));
  t.after(() => rm(root, { recursive: true, force: true }));
  const file = async (path, text) => {
    await mkdir(join(root, path, ".."), { recursive: true });
    await writeFile(join(root, path), text);
  };
  await file("library/x.cubist", "def x_value : Nat := 1;\n");
  await file("archive/first-library/x.cubist", "def x_value : Nat := 2;\n");
  await file("archive/first-library/a.cubist", "import x;\ndef a_value : Nat := x_value;\n");
  await file("work/x.cubist", "def x_value : Nat := 4;\n");
  await file("work/helper.cubist", "def helper_value : Nat := 3;\n");
  await file("work/main.cubist", "import x;\nimport helper;\ndef main_value : Nat := x_value;\n");
  const text = path => readFile(join(root, path), "utf8");
  return { root, text };
}

async function checked(t, root, source, { path = null, main = "current" } = {}) {
  const program = new CubicalProgram(await createCubical(), sourceReader({ path, root }), { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(source, main);
  return { program, result };
}

test("same-name modules: each importer loads the module its place sees, one per name", async t => {
  const { root, text } = await fixture(t);
  // An archive module imported into a library-first check keeps the archive's x.
  let { program, result } = await checked(t, root, "import a;\ndef mine : Nat := a_value;\n");
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.equal(program.sources.x, await text("archive/first-library/x.cubist"));
  ({ program, result } = await checked(t, root, "import x;\ndef mine : Nat := x_value;\n"));
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.equal(program.sources.x, await text("library/x.cubist"));
  // Checking the archive file is archive-isolated.
  const archived = join(root, "archive/first-library/a.cubist");
  ({ program, result } = await checked(t, root, await text("archive/first-library/a.cubist"), { path: archived, main: "a" }));
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.equal(program.sources.x, await text("archive/first-library/x.cubist"));
  // Both would be needed under one name: the later importer fails, naming both places.
  await assert.rejects(checked(t, root, "import a;\nimport x;\n"), { message: "current imports x from library/, "
    + "but this check already loaded x from archive/first-library/; a check holds one module per name." });
  ({ program, result } = await checked(t, root, "import x;\nimport a;\ndef mine : Nat := a_value;\n"));
  assert.equal(result.complete, false);
  assert.deepEqual(program.gaps.filter(gap => gap.module === "a").map(gap => gap.reason), ["a imports x from "
    + "archive/first-library/, but this check already loaded x from library/; a check holds one module per name."]);
});

test("a checked file outside both roots imports from its own directory first", async t => {
  const { root, text } = await fixture(t);
  const path = join(root, "work/main.cubist");
  const { program, result } = await checked(t, root, await text("work/main.cubist"), { path, main: "main" });
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.equal(program.sources.x, await text("work/x.cubist"));
  assert.equal(program.sources.helper, await text("work/helper.cubist"));
});

test("test selection finds a module as the CLI does and loads the same imports", async t => {
  const { root, text } = await fixture(t);
  assert.deepEqual(selectTests(["naturals"]).proofs, [resolve(projectRoot, "library/naturals.cubist")]);
  assert.deepEqual(selectTests(["euclid"]).proofs, [resolve(projectRoot, "archive/first-library/euclid.cubist")]);
  assert.deepEqual(selectTests(["x", "a"], { root }).proofs,
    [resolve(root, "library/x.cubist"), resolve(root, "archive/first-library/a.cubist")]);
  assert.equal((await loadProof(join(root, "archive/first-library/a.cubist"), root)).sources.x,
    await text("archive/first-library/x.cubist"));
  const local = await loadProof(join(root, "work/main.cubist"), root);
  assert.deepEqual(local.sources, { x: await text("work/x.cubist"), helper: await text("work/helper.cubist") });
  // A library module's imports: the library's own module, and archive modules.
  const library = await loadProof(join(projectRoot, "library/universe_automorphisms.cubist"));
  assert.equal(library.sources.classical_axioms, await readFile(join(projectRoot, "library/classical_axioms.cubist"), "utf8"));
  assert.equal(library.sources.classical, await readFile(join(projectRoot, "archive/first-library/classical.cubist"), "utf8"));
});

test("the CLI and the test runner check a file with local and library imports alike", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-parity-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "helper.cubist"), "def helper_value : Nat := 3;\n");
  await writeFile(join(directory, "parity.cubist"),
    "import helper;\nimport classical_axioms;\ndef total : Nat := helper_value;\n");
  const cli = spawnSync(process.execPath, [fileURLToPath(new URL("../cli/repl.mjs", import.meta.url)), "check", "parity.cubist"],
    { cwd: directory, encoding: "utf8", timeout: budget(60000) });
  assert.equal(cli.status, 0, cli.stderr);
  assert.match(cli.stdout, /^Checked 1 declarations/m);
  const environment = { ...process.env };
  delete environment.NODE_TEST_CONTEXT;
  const runner = spawnSync(process.execPath, [fileURLToPath(new URL("../tools/test.mjs", import.meta.url)), join(directory, "parity.cubist")],
    { cwd: projectRoot, encoding: "utf8", timeout: budget(60000), env: environment });
  assert.equal(runner.status, 0, runner.stdout + runner.stderr);
  assert.match(runner.stdout, /# pass 1/);
});
