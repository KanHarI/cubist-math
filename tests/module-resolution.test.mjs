import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, mkdir, readFile, readdir, writeFile, rm, symlink } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { moduleReader, listedReader, searchOrder, placeOfPath, moduleRoots } from "../web/module-resolution.mjs";
import { moduleListing } from "../web/module-listing.mjs";
import { sourceReader, placeOfFile, projectRoot } from "../tools/module-sources.mjs";
import { selectTests, loadProof } from "../tools/test-selection.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { budget } from "./timing.mjs";

// The resolution contract of web/module-resolution.mjs, which the CLI, the test
// runner, the library and reference tests and the browser worker share.

test("a module resolves its imports by where it lives", async () => {
  assert.deepEqual(searchOrder("archive"), ["archive"]);
  assert.deepEqual(searchOrder("library"), ["library", "archive"]);
  assert.deepEqual(searchOrder("tests"), ["tests", "library", "archive"]);
  assert.deepEqual(searchOrder("local"), ["local", "library", "archive"]);
  assert.deepEqual(searchOrder(), ["library", "archive"], "a source that is not a file");
  assert.throws(() => searchOrder("elsewhere"), /Unknown module place/);
  assert.equal(placeOfPath("archive/first-library/euclid.cubist"), "archive");
  assert.equal(placeOfPath("library/naturals.cubist"), "library");
  assert.equal(placeOfPath("cubist-tests/glue.cubist"), "tests");
  assert.equal(placeOfPath("scratch/mine.cubist"), "local");
  assert.equal(placeOfFile(join(projectRoot, "archive/first-library/euclid.cubist")), "archive");

  const files = { "library/x": "library x", "archive/x": "archive x", "library/only": "library only",
    "local/helper": "local helper", "tests/case": "tests case" };
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
  // A test module imports another test module first, then the library; no
  // other module sees the tests.
  const tests = reader();
  tests.place("main", "tests");
  assert.equal(await tests("case", "main"), "tests case");
  assert.equal(await tests("x", "main"), "library x");
  await assert.rejects(reader()("case"), { message: "No module named case in library/ or archive/first-library/." });
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
  // A listed test module is placed in the tests' root.
  assert.equal(listedReader({ library: [], archive: [], tests: ["t"] }, async path => path, "t").placeOf("t"), "tests");
  // A page that loaded its source from the archive says so, listed or not.
  const told = listedReader({ library: ["only"], archive: [] }, async path => path, "entry", "archive");
  assert.equal(told.placeOf("entry"), "archive");
  await assert.rejects(told("only", "entry"), /an archive module imports only from the archive/);
});

test("the browser lists every module the CLI finds on disk", async () => {
  const names = async directory => (await readdir(join(projectRoot, directory)))
    .filter(file => file.endsWith(".cubist")).map(file => file.slice(0, -".cubist".length)).sort();
  assert.deepEqual([...moduleListing.archive].sort(), await names(moduleRoots.archive),
    "every archive module, entry points such as euclid and basics included");
  assert.deepEqual([...moduleListing.library].sort(), await names(moduleRoots.library));
  assert.deepEqual([...moduleListing.tests].sort(), await names(moduleRoots.tests));
  // So the page's default proof is placed in the archive and imports only from it.
  const reader = listedReader(moduleListing, async () => "", "euclid");
  assert.equal(reader.placeOf("euclid"), "archive");
  await assert.rejects(reader("classical_axioms", "euclid"),
    { message: "No module named classical_axioms in archive/first-library/: an archive module imports only from the archive." });
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
  const clash = "a imports x from archive/first-library/, but this check already loaded x from library/; "
    + "a check holds one module per name.";
  ({ program, result } = await checked(t, root, "import x;\nimport a;\ndef mine : Nat := a_value;\n"));
  assert.equal(result.complete, false);
  assert.deepEqual(program.gaps.filter(gap => gap.module === "a").map(gap => gap.reason), [clash]);
  // The clash fails the check even when no declaration uses the refused module.
  ({ program, result } = await checked(t, root, "import x;\nimport a;\ndef independent : Nat := 0;\n"));
  assert.equal(result.outputs.every(output => output.verified), true);
  assert.equal(result.complete, false, "a refused import leaves the check incomplete");
  assert.deepEqual(program.gaps.map(gap => gap.reason), [clash]);
});

test("a failed import fails the check, even when nothing uses it", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-unused-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  await writeFile(join(directory, "unused.cubist"), "import no_such_module;\ndef independent : Nat := 0;\n");
  const program = new CubicalProgram(await createCubical(), sourceReader({ path: join(directory, "unused.cubist") }),
    { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(await readFile(join(directory, "unused.cubist"), "utf8"), "unused");
  assert.equal(result.complete, false);
  // A later check of the same program that imports nothing new is complete again.
  assert.equal((await program.check("def later : Nat := 1;\n", "later")).complete, true);
  const cli = spawnSync(process.execPath, [fileURLToPath(new URL("../cli/repl.mjs", import.meta.url)), "check", "unused.cubist"],
    { cwd: directory, encoding: "utf8", timeout: budget(60000) });
  assert.notEqual(cli.status, 0, cli.stdout);
  assert.match(cli.stderr, /No module named no_such_module in the checked file's directory, library\/ or archive\/first-library\//);
  const environment = { ...process.env };
  delete environment.NODE_TEST_CONTEXT;
  const runner = spawnSync(process.execPath, [fileURLToPath(new URL("../tools/test.mjs", import.meta.url)),
    "--test-reporter=tap", join(directory, "unused.cubist")],
    { cwd: projectRoot, encoding: "utf8", timeout: budget(60000), env: environment });
  assert.notEqual(runner.status, 0, runner.stdout);
  assert.match(runner.stdout, /^not ok 1 - cubical proof: unused\.cubist$/m);
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

test("loading a selected proof refuses a clash in either order, as a check does", async t => {
  const { root } = await fixture(t);
  await writeFile(join(root, "library/both.cubist"), "import x;\nimport a;\n");
  await writeFile(join(root, "library/both_reversed.cubist"), "import a;\nimport x;\n");
  await assert.rejects(loadProof(join(root, "library/both.cubist"), root), { message: "a imports x from "
    + "archive/first-library/, but this check already loaded x from library/; a check holds one module per name." });
  await assert.rejects(loadProof(join(root, "library/both_reversed.cubist"), root), { message: "both_reversed imports x "
    + "from library/, but this check already loaded x from archive/first-library/; a check holds one module per name." });
  // A check of the same files refuses them too.
  for (const main of ["both", "both_reversed"]) {
    const path = join(root, `library/${main}.cubist`);
    const program = new CubicalProgram(await createCubical(), sourceReader({ path, root }), { collectReferences: false });
    t.after(() => program.dispose());
    const outcome = await program.check(`${await readFile(path, "utf8")}def mine : Nat := x_value;\n`, main)
      .then(result => result.complete, error => error.message);
    assert.notEqual(outcome, true, main);
  }
});

test("a failed read is retried in the next check, while placements persist", async t => {
  const files = { "library/flaky": "def flaky_value : Nat := 1;\n" };
  let down = true;
  const reader = moduleReader(async (place, name) => {
    if (name === "flaky" && down) { down = false; throw new Error("The network is down."); }
    return files[`${place}/${name}`] ?? null;
  });
  await assert.rejects(reader("flaky"), /The network is down/);
  await assert.rejects(reader("later"), /No module named later/);
  files["library/later"] = "def later_value : Nat := 2;\n";
  // Within one check, answers are kept; the next check reads again.
  await assert.rejects(reader("later"), /No module named later/);
  reader.beginCheck();
  assert.equal(await reader("flaky"), files["library/flaky"]);
  assert.equal(await reader("later"), files["library/later"]);
  assert.equal(reader.placeOf("flaky"), "library");

  // A REPL session keeps one reader: a failed import succeeds when retried,
  // and a module created after a failed import can then be imported.
  const { root } = await fixture(t);
  let fetches = 0;
  const session = moduleReader(async (place, name) => {
    if (name === "x" && fetches++ === 0) throw new Error("The network is down.");
    return place === "local" ? null : readFile(join(root, moduleRoots[place], `${name}.cubist`), "utf8")
      .catch(error => { if (error.code === "ENOENT") return null; throw error; });
  });
  const program = new CubicalProgram(await createCubical(), session, { collectReferences: false });
  t.after(() => program.dispose());
  const repl = new ReplSession(program);
  const texts = results => results.map(result => `${result.kind}: ${result.text}`);
  assert.deepEqual(texts(await repl.run("import x;")), ["error: The network is down."]);
  assert.deepEqual(texts(await repl.run("import x;")), ["info: Imported x."]);
  assert.match(texts(await repl.run("import created_later;")).join(), /No module named created_later in library\//);
  await writeFile(join(root, "library/created_later.cubist"), "def created_value : Nat := 5;\n");
  assert.deepEqual(texts(await repl.run("import created_later;")), ["info: Imported created_later."]);
});

test("a checked file is placed where it really is, through symbolic links", async t => {
  const { root, text } = await fixture(t);
  const elsewhere = await mkdtemp(join(tmpdir(), "cubist-links-"));
  t.after(() => rm(elsewhere, { recursive: true, force: true }));
  // A link to an archive module is an archive module: it imports the archive's x.
  const archived = join(elsewhere, "linked_a.cubist");
  await symlink(join(root, "archive/first-library/a.cubist"), archived);
  assert.equal(placeOfFile(archived, root), "archive");
  const { program, result } = await checked(t, root, await readFile(archived, "utf8"), { path: archived, main: "linked_a" });
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.equal(program.sources.x, await text("archive/first-library/x.cubist"));
  assert.equal((await loadProof(archived, root)).sources.x, await text("archive/first-library/x.cubist"));
  // A link to a local file imports from the real file's directory.
  const local = join(elsewhere, "linked_main.cubist");
  await symlink(join(root, "work/main.cubist"), local);
  assert.equal(placeOfFile(local, root), "local");
  assert.deepEqual((await loadProof(local, root)).sources,
    { x: await text("work/x.cubist"), helper: await text("work/helper.cubist") });
  // A root reached through a link places its files as the real root does.
  const linkedRoot = join(elsewhere, "repository");
  await symlink(root, linkedRoot);
  assert.equal(placeOfFile(join(linkedRoot, "archive/first-library/a.cubist"), root), "archive");
  assert.equal(placeOfFile(join(root, "archive/first-library/a.cubist"), linkedRoot), "archive");
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
  // A fixed reporter: Node's default differs between versions when piped.
  const runner = spawnSync(process.execPath, [fileURLToPath(new URL("../tools/test.mjs", import.meta.url)),
    "--test-reporter=tap", join(directory, "parity.cubist")],
    { cwd: projectRoot, encoding: "utf8", timeout: budget(60000), env: environment });
  assert.equal(runner.status, 0, runner.stdout + runner.stderr);
  assert.match(runner.stdout, /^ok 1 - cubical proof: parity\.cubist$/m);
  assert.match(runner.stdout, /^# pass 1$/m);
});
