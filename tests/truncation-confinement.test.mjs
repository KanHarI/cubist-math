// K2.5 step 4 (docs/roadmaps/hott/h1-truncation-migration.md): the archive's
// legacy builtins, Truncate, TruncateIntro, TruncateProp, TruncateElim and
// the builtin LEM and Choice over them, are accepted only in an archive
// module, one the module reader read unedited from archive/first-library/.
// Anywhere else each is refused, called or named, with E491, which names
// Trunc and the library's axioms: a library module, a file of the user's,
// the workspace, a REPL or console entry and a test fixture, and so is a
// module that only spells an archive module's name or edits its text.
// No module of the repository's archive uses them since K2.5 step 5 moved
// it to the library's truncation and axioms; an archive module that does is
// legacyClassical, read from a temporary project's archive (legacyProject)
// or answered as the archive's own file (legacyArchiveReader).
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
import { ReplSession } from "../web/repl-session.mjs";
import { ContextualSession } from "../web/contextual-session.mjs";
import { WorkbenchSession } from "../web/cubical-workbench-session.mjs";
import { moduleListing } from "../web/module-listing.mjs";
import { archiveProvenance, libraryProvenance, listedReader, moduleReader } from "../web/module-resolution.mjs";
import { moduleOfFile, sourceReader } from "../tools/module-sources.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { migrationSourceReader } from "../tools/migration-sources.mjs";
import { checkProgram, checkTestModule, legacyArchiveReader, legacyClassical } from "./check-program.mjs";

const module = await createCubical();
const root = fileURLToPath(new URL("../", import.meta.url));
const cli = fileURLToPath(new URL("../cli/repl.mjs", import.meta.url));
const archived = name => readFile(join(root, "archive/first-library", `${name}.cubist`), "utf8");
const fetchText = path => readFile(join(root, path), "utf8");
const confined = name => new RegExp(`^E491: ${name} is the archive's legacy builtin, accepted only in archive modules: `
  + "elsewhere use the library's Trunc, from h1_truncation, and its axioms LEM and Choice, from classical_axioms\\.");
const legacy = "def truncated(A : U0) := Truncate(U0, A);\n";
// Each declaration's verdict: true, or its refusal with its code.
const verdicts = result => Object.fromEntries(result.outputs.map(output => [output.name,
  output.verified ? true : `${output.code}: ${output.reason}`]));
const labels = (result, name) => result.outputs.find(output => output.name === name).axioms
  .map(id => result.assumptionLabels[id] ?? id).sort();
const legacyLabels = ["LEM[Truncate]", "Truncate", "TruncateElim"];
// A project whose archive holds legacyClassical as its classical module, with
// the listing and the reader of its files that a transfer's provenance takes.
async function legacyProject(t) {
  const directory = fs.realpathSync.native(await mkdtemp(join(tmpdir(), "cubist-legacy-")));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const project = join(directory, "project"), classical = join(project, "archive/first-library/classical.cubist");
  await mkdir(join(project, "archive/first-library"), { recursive: true });
  await writeFile(classical, legacyClassical);
  return { directory, project, classical, listing: { archive: ["classical"] }, fetchText: path => readFile(join(project, path), "utf8") };
}

test("an archive module may still use the legacy builtins; the archive's own call sites use the library's axioms", async t => {
  // The archive's three call sites of LEM and Choice are the library's.
  for (const [name, declaration, label] of [["classical", "double_negation", "LEM"],
    ["zorn_chain_complete", "zorn_chain_complete", "Choice"], ["surjections", "every_surjection_has_right_inverse", "Choice"]]) {
    const path = join(root, "archive/first-library", `${name}.cubist`);
    const { result } = await checkProgram(t, await archived(name), { module, name, reader: sourceReader({ path }) });
    assert.equal(result.complete, true, `${name}: ${JSON.stringify(result.gaps[0])}`);
    assert.ok(labels(result, declaration).includes(label), `${name}.${declaration}: ${labels(result, declaration)}`);
    assert.ok(!labels(result, declaration).some(label => legacyLabels.includes(label) || label === "Choice[Truncate]"), name);
  }
  // From the command line, by its path and by its name.
  for (const target of ["archive/first-library/classical.cubist", "classical"]) {
    const run = spawnSync(process.execPath, [cli, "check", target], { cwd: root, encoding: "utf8", timeout: 60000 });
    assert.equal(run.status, 0, run.stdout + run.stderr);
    assert.match(run.stdout, /double_negation assumes LEM\n/);
  }
  // An archive module over the builtins, as its file holds it.
  const { classical, project } = await legacyProject(t);
  const { result } = await checkProgram(t, legacyClassical, { module, name: "classical", reader: sourceReader({ path: classical, root: project }) });
  assert.equal(result.complete, true, JSON.stringify(result.gaps[0]));
  assert.deepEqual(labels(result, "double_negation"), legacyLabels);
});

test("a test fixture refuses each legacy builtin, called or named", async t => {
  const { result } = await checkTestModule(t, "truncation_legacy_confined", { module });
  const refused = verdicts(result);
  for (const [name, builtin] of [["truncated", "Truncate"], ["introduced", "TruncateIntro"], ["proposition", "TruncateProp"],
    ["eliminated", "TruncateElim"], ["excluded", "LEM"], ["choice_at_zero", "Choice"], ["named", "Truncate"]])
    assert.match(refused[name], confined(builtin), name);
});

// universe_generic_builtins once took the legacy builtin LEM at UU0 (E407);
// since step 2 it imports classical_axioms, so no use of it is refused here.
test("universe_generic_builtins uses the library's LEM, no legacy builtin", async t => {
  const { result } = await checkTestModule(t, "universe_generic_builtins", { module });
  assert.ok(!result.outputs.some(output => output.code === "E491"), JSON.stringify(verdicts(result)));
  assert.deepEqual(labels(result, "D4_small"), ["LEM"]);
});

test("a library module may not use them, though read unedited from library/", async t => {
  const files = { "library/legacy_library": legacy };
  const reader = moduleReader((place, name) => files[`${place}/${name}`] ?? null);
  reader.place("legacy_library", "library");
  const { result } = await checkProgram(t, legacy, { module, name: "legacy_library", reader });
  assert.equal(await reader.fromLibrary("legacy_library", legacy), true);
  assert.match(verdicts(result).truncated, confined("Truncate"));
});

test("a file of the user's may not, nor a copy of an archive module outside the archive; a link into it may", async t => {
  const { directory, project, classical } = await legacyProject(t);
  const check = file => spawnSync(process.execPath, [cli, "check", file], { cwd: directory, encoding: "utf8", timeout: 60000 });
  await writeFile(join(directory, "mine.cubist"), "def excluded(A : U0, nn : (A -> Void) -> Void) := LEM(U0, A, nn);\n");
  const mine = check("mine.cubist");
  assert.notEqual(mine.status, 0);
  assert.match(mine.stdout + mine.stderr, /error E491 at line 1:51 \(excluded\): LEM is the archive's legacy builtin/);
  // A file read as the command line reads it, in the project, whose archive
  // module uses the builtins.
  const verdict = async path => {
    const { result } = await checkProgram(t, await readFile(path, "utf8"), { module, name: moduleOfFile(path),
      reader: sourceReader({ path, root: project }) });
    return verdicts(result).double_negation;
  };
  assert.equal(await verdict(classical), true);
  // The archive's own text under its own name, outside the archive: a
  // module's name and text do not make it the archive's, its root does.
  await writeFile(join(directory, "classical.cubist"), legacyClassical);
  assert.match(await verdict(join(directory, "classical.cubist")), /^E491: /);
  // A link resolves to the archive's own file, as an import of it does,
  // under its own name or another (#332's review, finding 1: a renamed link
  // was refused, its name's archive file looked for).
  const linked = join(directory, "linked");
  await symlink(join(project, "archive/first-library"), linked);
  assert.equal(await verdict(join(linked, "classical.cubist")), true);
  await symlink(classical, join(directory, "renamed.cubist"));
  assert.equal(await verdict(join(directory, "renamed.cubist")), true);
  // So the command line checks the repository's archive through a renamed
  // link, over the library's LEM.
  await symlink(join(root, "archive/first-library/classical.cubist"), join(directory, "archived.cubist"));
  const archivedLink = check("archived.cubist");
  assert.equal(archivedLink.status, 0, archivedLink.stdout + archivedLink.stderr);
  assert.match(archivedLink.stdout, /double_negation assumes LEM\n/);
});

// On a case-insensitive file system a path may spell the archive's file in
// another case: it is the archive's file all the same, recorded as the root
// lists it, so the check keeps the builtins and its transfer replays
// (#332's review round 3). The module keeps the name its path gives.
const caseInsensitive = existsSync(join(root, "ARCHIVE/FIRST-LIBRARY/CLASSICAL.cubist"));
test("a path that spells the archive's file in another case is the archive's file", {
  skip: !caseInsensitive && "this file system is case-sensitive: a path in another case names no archive file",
}, async t => {
  for (const path of ["archive/first-library/CLASSICAL.cubist", "ARCHIVE/FIRST-LIBRARY/classical.cubist"]) {
    const run = spawnSync(process.execPath, [cli, "check", path], { cwd: root, encoding: "utf8", timeout: 60000 });
    assert.equal(run.status, 0, `${path}: ${run.stdout}${run.stderr}`);
    assert.match(run.stdout, /double_negation assumes LEM\n/, path);
  }
  const { project, listing, fetchText: fetchProject } = await legacyProject(t);
  const program = new CubicalProgram(module, sourceReader({ path: join(project, "archive/first-library/CLASSICAL.cubist"), root: project }),
    { collectReferences: false });
  t.after(() => program.dispose());
  assert.equal((await program.check(legacyClassical, "CLASSICAL")).complete, true);
  const exported = program.export("CLASSICAL__double_negation");
  assert.equal(exported.files.CLASSICAL, "archive/first-library/classical.cubist");
  const session = new WorkbenchSession(module, { fromLibrary: libraryProvenance(moduleListing, fetchText),
    fromArchive: archiveProvenance(listing, fetchProject) });
  t.after(() => session.dispose());
  const loaded = await session.load(exported);
  assert.ok(loaded.view.axioms.map(name => loaded.view.symbols[name].name).includes("LEM[Truncate]"));
});

// A link followed by .. leaves the link's target, as reading the file does:
// a path that spells the archive's file through a link into another tree
// reads that tree's file, and is vouched for as that file, outside the
// archive (#332's review round 4). Reading and provenance take one path.
test("a path through a link and .. is vouched for as the file it reads", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-link-dotdot-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const project = join(directory, "project"), elsewhere = join(directory, "elsewhere");
  for (const tree of [project, elsewhere]) await mkdir(join(tree, "archive/first-library"), { recursive: true });
  await mkdir(join(elsewhere, "inner"));
  const forged = "def forged(A : U0) := Truncate(U0, A);\n";
  await writeFile(join(project, "archive/first-library/classical.cubist"), "def genuine(A : U0) := Truncate(U0, A);\n");
  await writeFile(join(elsewhere, "archive/first-library/classical.cubist"), forged);
  try { await symlink(join(elsewhere, "inner"), join(project, "link")); }
  catch (error) { t.skip(`symbolic links cannot be made here (${error.code})`); return; }
  // Spelled as text, project/link/../archive/… is the project's archive;
  // read, it is elsewhere's file.
  const through = `${project}/link/../archive/first-library/classical.cubist`;
  assert.equal(await readFile(through, "utf8"), forged);
  const verdict = async reader => {
    const program = new CubicalProgram(module, reader, { collectReferences: false });
    t.after(() => program.dispose());
    await program.checkModules(["borrowed"], "fingerprint");
    const output = program.symbols.borrowed__forged ?? program.symbols.borrowed__genuine;
    return [output.name, output.verified ? true : output.code];
  };
  const aliased = (file, place = "archive") => {
    const reader = sourceReader({ root: project, files: new Map([[`${place}/borrowed`, file]]) });
    reader.place("fingerprint", "archive");
    return reader;
  };
  assert.deepEqual(await verdict(aliased(through)), ["forged", "E491"]);
  assert.deepEqual(await verdict(aliased(join(project, "archive/first-library/classical.cubist"))), ["genuine", true]);
  // A checked file named so is placed and read as the same file.
  const { result } = await checkProgram(t, await readFile(through, "utf8"), { module, name: "classical",
    reader: sourceReader({ path: through, root: project }) });
  assert.match(verdicts(result).forged, /^E491: /);
});

// A file replaced by a link into the archive while it is read: its real path
// is resolved once, the text read from it, and the root taken from that path
// as text, so a link swapped in after the read never vouches for the text
// read before it (#332's review round 5, finding 1). The swap is made at the
// next resolution of the path after the first, as the reviewer's mocks did.
test("a file swapped for a link into the archive while it is read is not the archive's", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-swap-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const external = join(fs.realpathSync.native(directory), "external.cubist");
  await writeFile(external, (await readFile(join(root, "cubist-tests/truncation_legacy_confined.cubist"), "utf8")));
  const archiveFile = join(root, "archive/first-library/truncation.cubist");
  try { symlinkSync(archiveFile, join(directory, "probe.cubist")); }
  catch (error) { t.skip(`symbolic links cannot be made here (${error.code})`); return; }
  const native = fs.realpathSync.native;
  let resolutions = 0;
  t.mock.method(fs.realpathSync, "native", function (path, ...rest) {
    if (path === external && ++resolutions === 2) {
      renameSync(external, `${external}.read`);
      symlinkSync(archiveFile, external);
    }
    return native.call(this, path, ...rest);
  });
  const reader = sourceReader({ files: new Map([["archive/swapped", external]]) });
  reader.place("fingerprint", "archive");
  const program = new CubicalProgram(module, reader, { collectReferences: false });
  t.after(() => program.dispose());
  await program.checkModules(["swapped"], "fingerprint");
  t.mock.restoreAll();
  assert.ok(resolutions >= 2, "the path was resolved again after it was read");
  for (const name of ["truncated", "introduced", "proposition", "eliminated", "excluded", "choice_at_zero", "named"])
    assert.equal(program.symbols[`swapped__${name}`].code, "E491", name);
});

// A file aliased into the archive's place, as the fingerprint tool's
// --examples maps documentation examples, is not the archive's: its file is
// (#332's review, finding 1).
test("a file aliased into the archive's place is not the archive's", async t => {
  const fixture = join(root, "cubist-tests/truncation_legacy_confined.cubist");
  const reader = sourceReader({ files: new Map([["archive/external_example", fixture]]) });
  reader.place("fingerprint", "archive");
  const program = new CubicalProgram(module, reader, { collectReferences: false });
  t.after(() => program.dispose());
  await program.checkModules(["external_example"], "fingerprint");
  for (const name of ["truncated", "introduced", "proposition", "eliminated", "excluded", "choice_at_zero", "named"])
    assert.equal(program.symbols[`external_example__${name}`].code, "E491", name);
  // The archive's own file under an alias of another name is.
  const { project, classical } = await legacyProject(t);
  const own = sourceReader({ root: project, files: new Map([["archive/borrowed", classical]]) });
  own.place("fingerprint", "archive");
  const archive = new CubicalProgram(module, own, { collectReferences: false });
  t.after(() => archive.dispose());
  await archive.checkModules(["borrowed"], "fingerprint");
  assert.equal(archive.symbols.borrowed__double_negation.verified, true, archive.symbols.borrowed__double_negation.reason);
});

// Text is the archive's where it was written: syntax a module outside the
// archive writes and an archive module expands is not, and is refused where
// it is expanded (#332's review, finding 2). Each mechanism that expands
// syntax written in one module while another is checked: a named
// notation's operator, numeral, literal and unary minus rules, selected by
// use or applied qualified, and a model's attached notation. A theory's
// fields, and its parents', are elaborated where the theory is written,
// which refuses them there; so is a theory's derived definition, which an
// initial model of it in another module uses where it was checked, and the
// initial model itself is not affected (#332's review round 2, finding 3).
test("a builtin in syntax written outside the archive is refused where an archive module expands it", async t => {
  const T = "Truncate(U0, Unit)";
  const named = rules => `import unat;\ndef plus(x, y : UNat) : UNat := add(x, y);\nnotation lib { ${rules} numeral(n : UNat) := n; }\n`;
  const check = async (author, authorPlace, user) => {
    const files = { [`${authorPlace}/author`]: author,
      "archive/user": `import author;\nimport unat;\nimport hlevels;\nimport lexemes;\n${user}\n` };
    const reader = moduleReader((place, name) => files[`${place}/${name}`]
      ?? (place === "library" ? readFile(join(root, "library", `${name}.cubist`), "utf8").catch(() => null) : null));
    const program = new CubicalProgram(module, reader, { collectReferences: false });
    try {
      const result = await program.check("import user;\n", "main");
      return Object.fromEntries(result.imports.filter(output => ["author", "user"].includes(output.sourceModule))
        .map(output => [`${output.sourceModule}.${output.name}`, output.verified ? labels({ ...result, outputs: result.imports }, output.name) : output.code]));
    } finally { program.dispose(); }
  };
  const users = verdict => Object.entries(verdict).filter(([name]) => name.startsWith("user."));
  const notations = [
    ["an operator rule selected by use", named(`x + y := (fun (T : U0) => plus(x, y))(${T});`), "use lib;\ndef z : UNat := 1 + 2;"],
    ["an operator rule applied qualified", named(`x + y := (fun (T : U0) => plus(x, y))(${T});`), "def z : UNat := lib.(1 + 2);"],
    ["a numeral rule", `import unat;\nnotation lib { numeral(n : UNat) := (fun (T : U0) => n)(${T}); }\n`, "use lib;\ndef z : UNat := 3;"],
    ["a literal rule", `import unat;\nimport lexemes;\ncomputable def glyph_count(s : Lexeme) : Parsed(U0, UNat) := ok(length(s));\n`
      + `notation lib { literal(s : Lexeme) := (fun (T : U0) => glyph_count(s))(${T}); }\n`, "def z : UNat := lib.(007);"],
    ["a unary minus rule", `import unat;\nnotation lib { -x := (fun (T : U0) => x)(${T}); numeral(n : UNat) := n; }\n`, "use lib;\ndef z : UNat := -3;"],
    ["a model's attached notation", `import unat;\ntheory Mag(U < UU0) { M : U; op(x, y : M) : M notation x * y; }\n`
      + `def m : Mag(U0) := Mag.make(M := UNat, op := fun (x, y : UNat) => x);\nnotation m { numeral(n : UNat) := (fun (T : U0) => n)(${T}); }\n`,
      "def z : UNat := m.(3);"],
  ];
  for (const [label, author, user] of notations) {
    assert.deepEqual(users(await check(author, "library", user)), [["user.z", "E491"]], label);
    assert.deepEqual(users(await check(author, "archive", user)), [["user.z", ["Truncate"]]], label);
  }
  // A theory's parent: refused where it is written, and so unavailable to an
  // archive module that extends it; in the archive, the child and its
  // generated members carry it.
  const parent = [`theory P(U < UU0) { M : U; w : ${T} -> M; }\n`, "theory C(U < UU0) extends P {}"];
  const outside = await check(parent[0], "library", parent[1]), inside = await check(parent[0], "archive", parent[1]);
  assert.equal(outside["author.P"], "E491");
  assert.ok(users(outside).every(([, verdict]) => verdict === "E340"), JSON.stringify(outside));
  assert.deepEqual(users(inside).map(([name]) => name), ["user.C", "user.C.make", "user.C.M", "user.C.w", "user.C.p"]);
  assert.ok(users(inside).every(([, verdict]) => JSON.stringify(verdict) === '["Truncate"]'), JSON.stringify(inside));
  // An initial model of a theory whose derived definition writes it: the
  // derived definition is refused where it is written, the initial model and
  // its generated members verify either way, and only a use of the derived
  // definition carries the builtin, in the archive.
  const initial = [`import hlevels;\ntheory P(U < UU0) { M : set U; c : M; def dropped(w : ${T}) : M := c; }\n`,
    `initial N : P(U0);\ndef used(w : ${T}) : N := P.dropped(N.model, w);`];
  const generated = ["user.N", "user.N.model", "user.N.fold_map", "user.N.fold"].map(name => [name, []]);
  const library = await check(initial[0], "library", initial[1]), archive = await check(initial[0], "archive", initial[1]);
  assert.equal(library["author.P.dropped"], "E491");
  assert.deepEqual(users(library), [...generated, ["user.used", "E340"]]);
  assert.deepEqual(archive["author.P.dropped"], ["Truncate"]);
  assert.deepEqual(users(archive), [...generated, ["user.used", ["Truncate"]]]);
});

// A refusal is no failed attempt: where elaboration infers an argument's
// type speculatively, as for an implicit parameter, a hole, a constructor's
// parameters or a literal rule's parse, the legacy builtin's refusal is
// reported, not that nothing determines the argument (#332's review round
// 2, finding 2).
test("a legacy builtin's refusal is reported through speculative inference, not taken for a failed attempt", async t => {
  const T = "TruncateIntro(U0, Unit, tt)";
  const sources = {
    implicit: `def identity_{{A : U0}}(x : A) := x;\ndef z := identity_(${T});`,
    hole: `def identity_(A : U0, x : A) := x;\ndef z := identity_(_, ${T});`,
    named: `def identity_(A : U0, x : A) := x;\ndef z := identity_(x := ${T}, A := _);`,
    constructor: `inductive Box(A : U0) { box(a : A); }\ndef z := box(${T});`,
    literal: `import unat;\nimport lexemes;\ncomputable def glyph_count(s : Lexeme) : Parsed(U0, UNat) := ok(length(s));\n`
      + `notation count { literal(s : Lexeme) := (fun (w : Truncate(U0, Unit)) => glyph_count(s))(${T}); }\ndef z : UNat := count.(007);`,
  };
  for (const [name, source] of Object.entries(sources)) {
    const { result } = await checkProgram(t, source, { module, name: `refusal_${name}` });
    assert.match(verdicts(result).z, /^E491: /, name);
  }
});

// A program checked again reuses a module only from the same text and the
// same provenance: text that is no longer what its root holds is checked
// again, and loses the builtins, or its axioms' bare labels (#332's review,
// finding 3).
test("a module checked again is checked afresh when its provenance changes, though its text does not", async t => {
  const assumed = "def P := axiom Unit;\ndef used := P;\n", files = new Map([["archive/legacy", legacy], ["library/assumed", assumed]]);
  const reader = moduleReader((place, name) => files.get(`${place}/${name}`) ?? null);
  const program = new CubicalProgram(module, reader, { collectReferences: false });
  t.after(() => program.dispose());
  // Each check gives the module's original text, whatever its root holds.
  const check = async (name, place) => {
    reader.place(name, place);
    return (await program.check(name === "legacy" ? legacy : assumed, name)).outputs.at(-1);
  };
  assert.equal((await check("legacy", "archive")).verified, true);
  files.set("archive/legacy", `${legacy}// Edited in the archive.\n`);
  assert.equal((await check("legacy", "archive")).code, "E491");
  const label = output => output.axioms.map(id => program.checker.assumptionLabels.get(id));
  assert.deepEqual(label(await check("assumed", "library")), ["P"]);
  files.set("library/assumed", `${assumed}// Edited in the library.\n`);
  assert.deepEqual(label(await check("assumed", "library")), ["assumed::P"]);
});

// The browser's reader (web/cubical-worker.mjs): a page places the module it
// opened, and the module is the archive's only while its text is.
test("a workspace module is the archive's only as the archive holds it: an edit or a borrowed name is refused", async t => {
  const { listing, fetchText: fetchProject } = await legacyProject(t);
  const browser = (main, place) => listedReader(listing, fetchProject, main, place);
  const kept = await checkProgram(t, legacyClassical, { module, name: "classical", reader: browser("classical", "archive") });
  assert.equal(kept.result.complete, true, JSON.stringify(kept.result.gaps[0]));
  assert.deepEqual(labels(kept.result, "double_negation"), legacyLabels);
  const edited = await checkProgram(t, `${legacyClassical}\ndef extra := tt;\n`, { module, name: "classical", reader: browser("classical", "archive") });
  assert.match(verdicts(edited.result).double_negation, /^E491: /);
  assert.equal(verdicts(edited.result).extra, true);
  // Placed in the archive by its page, or by a listed name, a module whose
  // text the archive does not hold is the user's.
  for (const [main, place] of [["my_work", "archive"], ["classical", null]]) {
    const { result } = await checkProgram(t, legacy, { module, name: main, reader: browser(main, place) });
    assert.match(verdicts(result).truncated, confined("Truncate"), main);
  }
});

test("a REPL entry may not, over an archive module or not", async t => {
  const { project, classical } = await legacyProject(t);
  for (const base of [null, "classical"]) {
    const reader = base ? sourceReader({ path: classical, root: project }) : sourceReader();
    const program = new CubicalProgram(module, reader, { collectReferences: false });
    t.after(() => program.dispose());
    if (base) assert.equal((await program.check(legacyClassical, base)).complete, true);
    const repl = new ReplSession(program, base ? { base } : {});
    for (const entry of ["def truncated(A : U0) := Truncate(U0, A);", "typeof LEM(U0);", "typeof TruncateIntro;"]) {
      const [result] = await repl.run(entry);
      assert.equal(result.kind, "error", `${base}: ${entry}`);
      assert.match(result.text, /E491|is the archive's legacy builtin, accepted only in archive modules/, `${base}: ${entry}`);
    }
    // The archive's declarations over them remain usable.
    if (base) assert.equal((await repl.run("typeof double_negation;"))[0].kind, "type");
  }
});

// The console replays the check up to its scope, which keeps each module's
// recorded provenance (cubical-replay-inputs.mjs): the archive module
// replays with its builtins, and an entry in its scope is still refused.
test("a console entry in an archive module's scope may not", async t => {
  const { project, classical } = await legacyProject(t);
  const source = legacyClassical, marker = "LEM(U0, P, nn)";
  const { program } = await checkProgram(t, source, { module, name: "classical",
    reader: sourceReader({ path: classical, root: project }), options: { collectScopes: true } });
  const point = [...program.scopePoints.values()].find(point => point.origin.module === "classical"
    && point.origin.start === source.indexOf(marker) && point.phase === "expression");
  assert.ok(point);
  const session = new ContextualSession(program, point.id);
  t.after(() => session.dispose());
  const [typed] = await session.run("typeof nn;");
  assert.equal(typed.kind, "type", JSON.stringify(typed));
  const [refused] = await session.run("typeof LEM(U0, P, nn);");
  assert.equal(refused.kind, "error", JSON.stringify(refused));
  assert.match(refused.text, /LEM is the archive's legacy builtin, accepted only in archive modules/);
});

// A transfer's sources are text: the workbench asks which are the
// archive's, as it asks which are the library's.
test("a workbench transfer replays an archive module only as the archive holds it", async t => {
  const { project, listing, fetchText: fetchProject } = await legacyProject(t);
  const program = new CubicalProgram(module, sourceReader({ root: project }), { collectReferences: false });
  t.after(() => program.dispose());
  await program.check("import classical;\ndef again := double_negation;", "workbench");
  const exported = program.export("workbench__again");
  const fromArchive = archiveProvenance(listing, fetchProject), fromLibrary = libraryProvenance(moduleListing, fetchText);
  const load = async (sources, options) => {
    const session = new WorkbenchSession(module, options);
    t.after(() => session.dispose());
    return session.load({ ...exported, sources });
  };
  const loaded = await load(exported.sources, { fromLibrary, fromArchive });
  assert.ok(loaded.view.axioms.map(name => loaded.view.symbols[name].name).includes("LEM[Truncate]"));
  await assert.rejects(load(exported.sources, { fromLibrary }), /did not replay completely/);
  const edited = { ...exported.sources, classical: `${exported.sources.classical}\ndef extra := tt;\n` };
  await assert.rejects(load(edited, { fromLibrary, fromArchive }), /did not replay completely/);
});

// A transfer carries the file each source was read from, and the workbench
// authenticates that file, so a module read under another name, through an
// alias or a link, replays as the archive's when its file is the archive's,
// and never by a file the archive does not hold (#332's review round 2,
// finding 1).
test("a workbench transfer authenticates each source by the file it was read from, under any name", async t => {
  const { directory, project, classical, listing, fetchText: fetchProject } = await legacyProject(t);
  const fromArchive = archiveProvenance(listing, fetchProject), fromLibrary = libraryProvenance(moduleListing, fetchText);
  const load = async payload => {
    const session = new WorkbenchSession(module, { fromLibrary, fromArchive });
    t.after(() => session.dispose());
    const loaded = await session.load(payload);
    return loaded.view.axioms.map(name => loaded.view.symbols[name].name);
  };
  // An alias of the archive's file, as the fingerprint tool reads one.
  const aliased = new CubicalProgram(module, sourceReader({ root: project, files: new Map([["archive/borrowed", classical]]) }),
    { collectReferences: false });
  t.after(() => aliased.dispose());
  await aliased.check("import borrowed;\ndef again := double_negation;", "workbench");
  const borrowed = aliased.export("workbench__again");
  assert.equal(borrowed.files.borrowed, "archive/first-library/classical.cubist");
  assert.ok((await load(borrowed)).includes("LEM[Truncate]"));
  // A renamed link to it, checked as a file.
  const link = join(directory, "renamed.cubist");
  await symlink(classical, link);
  const linked = new CubicalProgram(module, sourceReader({ path: link, root: project }), { collectReferences: false });
  t.after(() => linked.dispose());
  assert.equal((await linked.check(legacyClassical, "renamed")).complete, true);
  const renamed = linked.export("renamed__double_negation");
  assert.ok((await load(renamed)).includes("LEM[Truncate]"));
  // A file the archive does not hold, or other text, is not the archive's.
  for (const files of [{ borrowed: "cubist-tests/truncation_legacy_confined.cubist" }, { borrowed: "archive/first-library/../../library/unat.cubist" },
    { borrowed: "archive/first-library/truncation.cubist" }])
    await assert.rejects(load({ ...borrowed, files: { ...borrowed.files, ...files } }), /did not replay completely/, JSON.stringify(files));
});

// A program checked again from another file of the same text, as an alias
// moved from one archive file to another, records the new file, so that an
// export names the file it was read from and its transfer replays (#332's
// review round 5, finding 2).
test("a module read again from another file of the same text is exported with that file", async t => {
  const text = "def truncated(A : U0) := Truncate(U0, A);\n";
  let file = "archive/first-library/old.cubist";
  const reader = moduleReader((place, name) => place === "archive" && name === "borrowed" ? { text, root: "archive", file } : null);
  const program = new CubicalProgram(module, reader, { collectReferences: false });
  t.after(() => program.dispose());
  const source = "import borrowed;\ndef again := truncated;";
  await program.check(source, "workbench");
  assert.equal(program.export("workbench__again").files.borrowed, "archive/first-library/old.cubist");
  file = "archive/first-library/new.cubist";
  await program.check(source, "workbench");
  const exported = program.export("workbench__again");
  assert.equal(exported.files.borrowed, "archive/first-library/new.cubist");
  // The archive now holds new.cubist and no old.cubist.
  const listing = { archive: ["new"] }, fetched = async path => path === "archive/first-library/new.cubist" ? text : null;
  const session = new WorkbenchSession(module, { fromArchive: archiveProvenance(listing, fetched) });
  t.after(() => session.dispose());
  const loaded = await session.load(exported);
  assert.ok(loaded.view.axioms.map(name => loaded.view.symbols[name].name).includes("Truncate"));
});

// The migration verifier reads a baseline from the archive at its revision,
// and an edit of the archive in place from the archive's own files: both are
// the archive's. An edited module from anywhere else is not.
test("the migration verifier's archive baselines and in-place archive edits keep the builtins", async () => {
  const before = "def value(A : U0, a : A) := TruncateIntro(U0, A, a);\n";
  const after = "// Edited in place.\ndef value(A : U0, a : A) := TruncateIntro(U0, A, a);\n";
  const run = async place => {
    const readEdited = async () => after;
    readEdited.placeOf = () => place;
    return (await verifyMigration({ modules: ["legacy_edit"],
      readOriginal: migrationSourceReader(async (where, name) => where === "archive" && name === "legacy_edit" ? before : null, ["legacy_edit"]),
      readEdited }))[0];
  };
  assert.deepEqual((await run("archive")).failures, []);
  const elsewhere = await run("local");
  assert.match(elsewhere.failures.find(failure => failure.name === "value").reason, /TruncateIntro is the archive's legacy builtin/);
});
