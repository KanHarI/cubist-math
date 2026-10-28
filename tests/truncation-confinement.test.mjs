// K2.5 step 4 (docs/roadmaps/hott/h1-truncation-migration.md): the archive's
// legacy builtins, Truncate, TruncateIntro, TruncateProp, TruncateElim and
// the builtin LEM and Choice over them, are accepted only in an archive
// module, one the module reader read unedited from archive/first-library/.
// Anywhere else each is refused, called or named, with E491, which names
// Trunc and the library's axioms: a library module, a file of the user's,
// the workspace, a REPL or console entry and a test fixture, and so is a
// module that only spells an archive module's name or edits its text.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, readFile, rm, symlink, writeFile } from "node:fs/promises";
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
import { sourceReader } from "../tools/module-sources.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { migrationSourceReader } from "../tools/migration-sources.mjs";
import { checkProgram, checkTestModule } from "./check-program.mjs";

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

test("an archive module, read from the archive as it holds it, still uses the legacy builtins", async t => {
  // The archive's three call sites of LEM and Choice keep them.
  for (const [name, declaration, label] of [["classical", "double_negation", "LEM[Truncate]"],
    ["zorn_chain_complete", "zorn_chain_complete", "Choice[Truncate]"], ["surjections", "every_surjection_has_right_inverse", "Choice[Truncate]"]]) {
    const path = join(root, "archive/first-library", `${name}.cubist`);
    const { result } = await checkProgram(t, await archived(name), { module, name, reader: sourceReader({ path }) });
    assert.equal(result.complete, true, `${name}: ${JSON.stringify(result.gaps[0])}`);
    assert.ok(labels(result, declaration).includes(label), `${name}.${declaration}: ${labels(result, declaration)}`);
  }
  // From the command line, by its path and by its name.
  for (const target of ["archive/first-library/classical.cubist", "classical"]) {
    const run = spawnSync(process.execPath, [cli, "check", target], { cwd: root, encoding: "utf8", timeout: 60000 });
    assert.equal(run.status, 0, run.stdout + run.stderr);
    assert.match(run.stdout, /double_negation assumes LEM\[Truncate\], Truncate, TruncateElim/);
  }
});

test("a test fixture refuses each legacy builtin, called or named, and keeps the archive's declarations over them", async t => {
  const { result } = await checkTestModule(t, "truncation_legacy_confined", { module });
  const refused = verdicts(result);
  for (const [name, builtin] of [["truncated", "Truncate"], ["introduced", "TruncateIntro"], ["proposition", "TruncateProp"],
    ["eliminated", "TruncateElim"], ["excluded", "LEM"], ["choice_at_zero", "Choice"], ["named", "Truncate"]])
    assert.match(refused[name], confined(builtin), name);
  assert.equal(refused.archived, true);
  assert.deepEqual(labels(result, "archived"), ["Truncate"]);
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
  const directory = await mkdtemp(join(tmpdir(), "cubist-confinement-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const check = file => spawnSync(process.execPath, [cli, "check", file], { cwd: directory, encoding: "utf8", timeout: 60000 });
  await writeFile(join(directory, "mine.cubist"), "def excluded(A : U0, nn : (A -> Void) -> Void) := LEM(U0, A, nn);\n");
  const mine = check("mine.cubist");
  assert.notEqual(mine.status, 0);
  assert.match(mine.stdout + mine.stderr, /error E491 at line 1:51 \(excluded\): LEM is the archive's legacy builtin/);
  // The archive's own text under its own name, outside the archive: a
  // module's name and text do not make it the archive's, its root does.
  await writeFile(join(directory, "classical.cubist"), await archived("classical"));
  const copy = check("classical.cubist");
  assert.notEqual(copy.status, 0);
  assert.match(copy.stdout + copy.stderr, /error E491 at line \d+:\d+ \(double_negation\): LEM is the archive's legacy builtin/);
  // A link resolves to the archive's own file, as an import of it does.
  const linked = join(directory, "linked");
  await symlink(join(root, "archive/first-library"), linked);
  const link = check(join(linked, "classical.cubist"));
  assert.equal(link.status, 0, link.stdout + link.stderr);
});

// The browser's reader (web/cubical-worker.mjs): a page places the module it
// opened, and the module is the archive's only while its text is.
test("a workspace module is the archive's only as the archive holds it: an edit or a borrowed name is refused", async t => {
  const browser = (main, place) => listedReader(moduleListing, fetchText, main, place);
  const original = await archived("classical");
  const kept = await checkProgram(t, original, { module, name: "classical", reader: browser("classical", "archive") });
  assert.equal(kept.result.complete, true, JSON.stringify(kept.result.gaps[0]));
  assert.ok(labels(kept.result, "double_negation").includes("LEM[Truncate]"));
  const edited = await checkProgram(t, `${original}\ndef extra := tt;\n`, { module, name: "classical", reader: browser("classical", "archive") });
  assert.match(verdicts(edited.result).double_negation, confined("LEM"));
  assert.equal(verdicts(edited.result).extra, true);
  // Placed in the archive by its page, or by a listed name, a module whose
  // text the archive does not hold is the user's.
  for (const [main, place] of [["my_work", "archive"], ["classical", null]]) {
    const { result } = await checkProgram(t, legacy, { module, name: main, reader: browser(main, place) });
    assert.match(verdicts(result).truncated, confined("Truncate"), main);
  }
});

test("a REPL entry may not, over an archive module or not", async t => {
  for (const base of [null, "classical"]) {
    const reader = base ? sourceReader({ path: join(root, "archive/first-library", `${base}.cubist`) }) : sourceReader();
    const program = new CubicalProgram(module, reader, { collectReferences: false });
    t.after(() => program.dispose());
    if (base) assert.equal((await program.check(await archived(base), base)).complete, true);
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
  const source = await archived("classical"), marker = "LEM(U0, P, nn)";
  const { program } = await checkProgram(t, source, { module, name: "classical",
    reader: sourceReader({ path: join(root, "archive/first-library/classical.cubist") }), options: { collectScopes: true } });
  const point = [...program.scopePoints.values()].find(point => point.origin.module === "classical"
    && point.origin.start === source.indexOf(marker) && point.phase === "expression");
  assert.ok(point);
  const session = new ContextualSession(program, point.id);
  t.after(() => session.dispose());
  const [typed] = await session.run("typeof mere_eliminate(P, P, prop_, (fun (p : P) => p));");
  assert.equal(typed.kind, "type", JSON.stringify(typed));
  const [refused] = await session.run("typeof LEM(U0, P, nn);");
  assert.equal(refused.kind, "error", JSON.stringify(refused));
  assert.match(refused.text, /LEM is the archive's legacy builtin, accepted only in archive modules/);
});

// A transfer's sources are text: the workbench asks which are the
// archive's, as it asks which are the library's.
test("a workbench transfer replays an archive module only as the archive holds it", async t => {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  await program.check("import classical;\ndef again := double_negation;", "workbench");
  const exported = program.export("workbench__again");
  const fromArchive = archiveProvenance(moduleListing, fetchText), fromLibrary = libraryProvenance(moduleListing, fetchText);
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
