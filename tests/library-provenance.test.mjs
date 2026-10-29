// The library's provenance (web/module-resolution.mjs, fromLibrary and
// libraryProvenance): a library module's axioms take their bare names only
// when its text is the library's file of its name, the file the module
// reader really read it from, by its real path. Its name, the place it is
// read under, and what a transfer says vouch for nothing more.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import fs, { existsSync, renameSync, symlinkSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, symlink, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { WorkbenchSession } from "../web/cubical-workbench-session.mjs";
import { moduleListing } from "../web/module-listing.mjs";
import { libraryProvenance, moduleReader } from "../web/module-resolution.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

const module = await createCubical();
const root = fileURLToPath(new URL("../", import.meta.url));
const cli = fileURLToPath(new URL("../cli/repl.mjs", import.meta.url));
const fromLibrary = libraryProvenance(moduleListing, path => readFile(join(root, path), "utf8"));
// A program, disposed of when the test ends, and the labels of the
// assumptions its check made.
const program = (t, reader) => {
  const made = new CubicalProgram(module, reader, { collectReferences: false });
  t.after(() => made.dispose());
  return made;
};
const labels = checked => [...checked.checker.assumptionLabels.values()].sort();
// The labels of a transfer's assumptions, as the workbench replays it.
async function replayed(t, payload) {
  const session = new WorkbenchSession(module, { fromLibrary });
  t.after(() => session.dispose());
  const loaded = await session.load(payload);
  return loaded.view.axioms.map(name => loaded.view.symbols[name].name);
}

// On a case-insensitive file system a path may spell the library's file in
// another case: it is the library's file all the same, recorded as the root
// lists it, so the check and its transfer keep the bare labels (#332's
// review round 3). The module keeps the name its path gives, and one that
// is not the file's own name is not the library's.
const caseInsensitive = existsSync(join(root, "LIBRARY/CLASSICAL_AXIOMS.cubist"));
test("a path that spells the library's file in another case is the library's file", {
  skip: !caseInsensitive && "this file system is case-sensitive: a path in another case names no library file",
}, async t => {
  for (const [path, label] of [["LIBRARY/classical_axioms.cubist", "LEM"], ["library/CLASSICAL_AXIOMS.cubist", "CLASSICAL_AXIOMS::LEM"]]) {
    const run = spawnSync(process.execPath, [cli, "check", path], { cwd: root, encoding: "utf8", timeout: 60000 });
    assert.equal(run.status, 0, `${path}: ${run.stdout}${run.stderr}`);
    assert.match(run.stdout, new RegExp(`^LEM assumes ${label}$`, "m"), path);
  }
  const path = join(root, "LIBRARY/classical_axioms.cubist"), checked = program(t, sourceReader({ path }));
  assert.equal((await checked.check(await readFile(path, "utf8"), "classical_axioms")).complete, true);
  const exported = checked.export("classical_axioms__LEM");
  assert.equal(exported.files.classical_axioms, "library/classical_axioms.cubist");
  assert.deepEqual(await replayed(t, exported), ["LEM"]);
});

// A link followed by .. leaves the link's target, as reading the file does:
// a path that spells the library's file through a link into another tree
// reads that tree's file, and is vouched for as that file, outside the
// library (#332's review round 4). Reading and provenance take one path.
test("a path through a link and .. is vouched for as the file it reads", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-link-dotdot-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const project = join(directory, "project"), elsewhere = join(directory, "elsewhere");
  for (const tree of [project, elsewhere]) await mkdir(join(tree, "library"), { recursive: true });
  await mkdir(join(elsewhere, "inner"));
  await writeFile(join(project, "library/assumed.cubist"), "def Genuine := axiom Unit;\n");
  await writeFile(join(elsewhere, "library/assumed.cubist"), "def Forged := axiom Unit;\n");
  try { await symlink(join(elsewhere, "inner"), join(project, "link")); }
  catch (error) { t.skip(`symbolic links cannot be made here (${error.code})`); return; }
  // Spelled as text, project/link/../library/… is the project's library;
  // read, it is elsewhere's file.
  const through = `${project}/link/../library/assumed.cubist`;
  assert.equal(await readFile(through, "utf8"), "def Forged := axiom Unit;\n");
  const imported = async file => {
    const checked = program(t, sourceReader({ root: project, files: new Map([["library/assumed", file]]) }));
    await checked.check("import assumed;\n", "main");
    return labels(checked);
  };
  assert.deepEqual(await imported(through), ["assumed::Forged"]);
  assert.deepEqual(await imported(join(project, "library/assumed.cubist")), ["Genuine"]);
  // A checked file named so is placed and read as the same file.
  const checked = program(t, sourceReader({ path: through, root: project }));
  assert.equal((await checked.check(await readFile(through, "utf8"), "assumed")).complete, true);
  assert.deepEqual(labels(checked), ["assumed::Forged"]);
});

// A file replaced by a link into the library while it is read: its real
// path is resolved once, the text read from it, and the root taken from
// that path as text, so a link swapped in after the read never vouches for
// the text read before it (#332's review round 5, finding 1). The swap is
// made at the next resolution of the path after the first, as the
// reviewer's mocks did.
test("a file swapped for a link into the library while it is read is not the library's", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-swap-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const external = join(fs.realpathSync.native(directory), "external.cubist");
  await writeFile(external, "def LEM := axiom Unit;\n");
  const libraryFile = join(root, "library/classical_axioms.cubist");
  try { symlinkSync(libraryFile, join(directory, "probe.cubist")); }
  catch (error) { t.skip(`symbolic links cannot be made here (${error.code})`); return; }
  const native = fs.realpathSync.native;
  let resolutions = 0;
  t.mock.method(fs.realpathSync, "native", function (path, ...rest) {
    if (path === external && ++resolutions === 2) {
      renameSync(external, `${external}.read`);
      symlinkSync(libraryFile, external);
    }
    return native.call(this, path, ...rest);
  });
  const checked = program(t, sourceReader({ files: new Map([["library/classical_axioms", external]]) }));
  await checked.check("import classical_axioms;\n", "main");
  t.mock.restoreAll();
  assert.ok(resolutions >= 2, "the path was resolved again after it was read");
  assert.deepEqual(labels(checked), ["classical_axioms::LEM"]);
});

// A program checked again reuses a module only from the same text and the
// same provenance: text that is no longer what the library holds is checked
// again, and loses its axioms' bare labels (#332's review, finding 3).
test("a module checked again is checked afresh when its provenance changes, though its text does not", async t => {
  const assumed = "def P := axiom Unit;\ndef used := P;\n", files = new Map([["library/assumed", assumed]]);
  const reader = moduleReader((place, name) => files.get(`${place}/${name}`) ?? null), checked = program(t, reader);
  reader.place("assumed", "library");
  // Each check gives the module's original text, whatever the library holds.
  const label = async () => (await checked.check(assumed, "assumed")).outputs.at(-1).axioms
    .map(id => checked.checker.assumptionLabels.get(id));
  assert.deepEqual(await label(), ["P"]);
  files.set("library/assumed", `${assumed}// Edited in the library.\n`);
  assert.deepEqual(await label(), ["assumed::P"]);
});

// A program checked again from another file of the same text records the
// new file, so that an export names the file it was read from (#332's
// review round 5, finding 2).
test("a module read again from another file of the same text is exported with that file", async t => {
  let file = "archive/first-library/old.cubist";
  const reader = moduleReader((place, name) => place === "archive" && name === "borrowed"
    ? { text: "def P := axiom Unit;\n", root: "archive", file } : null);
  const checked = program(t, reader), source = "import borrowed;\ndef again := P;";
  await checked.check(source, "workbench");
  assert.equal(checked.export("workbench__again").files.borrowed, "archive/first-library/old.cubist");
  file = "archive/first-library/new.cubist";
  await checked.check(source, "workbench");
  assert.equal(checked.export("workbench__again").files.borrowed, "archive/first-library/new.cubist");
});

// A transfer carries the file each source was read from, and the workbench
// authenticates that file (#332's review round 2, finding 1): the library's
// own file of the module's name, holding its text, and no other.
test("a workbench transfer authenticates each source by the file it was read from", async t => {
  const checked = program(t, sourceReader());
  await checked.check("import classical_axioms;\ndef excluded : ExcludedMiddle(U0) := LEM(U0);", "workbench");
  const exported = checked.export("workbench__excluded");
  assert.equal(exported.files.classical_axioms, "library/classical_axioms.cubist");
  assert.deepEqual(await replayed(t, exported), ["LEM"]);
  for (const file of ["archive/first-library/classical.cubist", "library/h1_classical.cubist", "library/../library/classical_axioms.cubist"])
    assert.deepEqual(await replayed(t, { ...exported, files: { ...exported.files, classical_axioms: file } }), ["classical_axioms::LEM"], file);
});
