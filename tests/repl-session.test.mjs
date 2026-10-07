import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession, replStatements } from "../web/repl-session.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// A session is a source that is not a file: it imports library-first.
async function session(t, source = null) {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  if (source === null) return new ReplSession(program);
  await program.check(source, "proof");
  return new ReplSession(program, { base: "proof" });
}
const texts = results => results.map(result => `${result.kind}: ${result.text}`);

test("statements end at ; outside brackets, and a block declaration at its brace", () => {
  assert.deepEqual(replStatements("let x := 7; typeof x;").statements, ["let x := 7;", "typeof x;"]);
  assert.deepEqual(replStatements("def a : Nat {\n  exact 1;\n}\nevaluate a").statements, ["def a : Nat {\n  exact 1;\n}"]);
  assert.equal(replStatements("def a : Nat {\n  exact 1;\n}\nevaluate a").rest, "evaluate a");
  assert.deepEqual(replStatements("def f := match x { left a => 1; right b => 2; };").statements,
    ["def f := match x { left a => 1; right b => 2; };"]);
  assert.equal(replStatements("def a : Nat {\n  exact").depth, 1);
  assert.deepEqual(replStatements("// a comment; with a semicolon\ntypeof 1;").statements, ["// a comment; with a semicolon\ntypeof 1;"]);
  // A brace within a term ends nothing: what follows a box, a match or
  // implicit arguments stays in its statement.
  for (const statement of ["compose i in (Unit and Unit) from (tt, tt) {}.1;", "evaluate compose i in Unit from tt {} expecting tt;",
    "fill j in Unit from tt at 1 {}(x);", "evaluate match b { yes => tt; no => tt; } expecting tt;", "evaluate id{{Unit}}(tt);",
    "def f{{A : U0}}(x : A) : A := x;", "def g : rematch(x) {\n  exact tt;\n}", "def h : compose(x) {\n  exact tt;\n}"])
    assert.deepEqual(replStatements(`${statement} typeof x;`).statements, [statement, "typeof x;"]);
  // A header's words may be apart by comments, as in a file; a word in a
  // comment is no header's.
  for (const statement of ["compose // direction\n  i in (Unit and Unit) from (tt, tt) {}.1;",
    "evaluate compose i // direction\n in Unit from tt {} expecting tt;", "fill\n// direction\nj in Unit from tt at 1 {}(x);",
    "def h : compose // i in\n(x) {\n  exact tt;\n}"])
    assert.deepEqual(replStatements(`${statement} typeof x;`).statements, [statement, "typeof x;"]);
  // A block still ends its declaration where its type holds a box.
  assert.deepEqual(replStatements("def t : compose j in U0 from Unit {} {\n  exact tt;\n}\nt").statements,
    ["def t : compose j in U0 from Unit {} {\n  exact tt;\n}"]);
});

test("let binds, typeof shows the type, and evaluate the value", async t => {
  const repl = await session(t);
  assert.deepEqual(texts(await repl.run("import nat;")), ["info: Imported nat."]);
  // A use selects for every entry after it, as at a file's top level.
  assert.deepEqual(texts(await repl.run("use nat;")), ["info: Selected nat."]);
  assert.deepEqual(texts(await repl.run("let x := 7;")), ["defined: x : Nat"]);
  assert.deepEqual(texts(await repl.run("typeof x;")), ["type: Nat"]);
  assert.deepEqual(texts(await repl.run("evaluate x;")), ["value: 7"]);
  // A term alone is evaluated, and a last statement may omit its `;`.
  assert.deepEqual(texts(await repl.run("x")), ["value: 7"]);
  assert.deepEqual(texts(await repl.run("typeof fun (n : Nat) => succ(n)")), ["type: Nat -> Nat"]);
  // A print directive is an entry too.
  assert.deepEqual(texts(await repl.run("print(evaluate(succ(x)));")), ["value: 8"]);
  assert.deepEqual(texts(await repl.run("print(typeof(x))")), ["value: Nat"]);
  assert.deepEqual(texts(await repl.run("print(inspect(succ(x)));")), ["value: succ(x)"]);
});

test("imports, declarations with blocks, and errors that leave the session unchanged", async t => {
  const repl = await session(t);
  assert.deepEqual(texts(await repl.run("import nat;")), ["info: Imported nat."]);
  // A use that selects nothing is refused, and changes nothing.
  assert.deepEqual(texts(await repl.run("use nowhere;")), ["error: E343: Untranslated name: nowhere"]);
  assert.deepEqual(texts(await repl.run("use nat;")), ["info: Selected nat."]);
  assert.deepEqual(texts(await repl.run("evaluate 2 + 3 * 4;")), ["value: 14"]);
  assert.deepEqual(texts(await repl.run("def four_is_four : 2 + 2 = 4 {\n  exact refl(4);\n}")), ["defined: four_is_four : 2 + 2 = 4"]);
  assert.deepEqual(texts(await repl.run("def wrong : 2 + 2 = 5 {\n  exact refl(4);\n}")),
    ["error: E606: Type mismatch: found 4 = 4, expected 2 + 2 = 5."]);
  assert.deepEqual(texts(await repl.run("typeof wrong;")), ["error: E343: Untranslated name: wrong"]);
  assert.deepEqual(texts(await repl.run("typeof nowhere")), ["error: E343: Untranslated name: nowhere"]);
  assert.deepEqual(texts(await repl.run("import nowhere;")).length, 1);
  // Later entries still see everything that checked.
  assert.deepEqual(texts(await repl.run("typeof four_is_four; evaluate double(3)")).slice(0, 1), ["type: 2 + 2 = 4"]);
});

test("witness reads a closed truncation's witness, with its type", async t => {
  const repl = await session(t);
  assert.deepEqual(texts(await repl.run("import h1_truncation; use nat;")), ["info: Imported h1_truncation.", "info: Selected nat."]);
  assert.deepEqual(texts(await repl.run("witness merely(U0, Nat, 2 + 1);")), ["value: 3 : Nat"]);
  assert.match(texts(await repl.run("witness 3;"))[0], /^error: E479: witness reads a closed truncation/);
});

test("a box is a term: its projection, application and expectation stay in the entry", async t => {
  const repl = await session(t);
  assert.deepEqual(texts(await repl.run("compose i in (Unit and Unit) from (tt, tt) {}.1;")), ["value: tt"]);
  assert.deepEqual(texts(await repl.run("compose i in (Unit -> Unit) from fun (x : Unit) => x {}(tt);")), ["value: tt"]);
  assert.deepEqual(texts(await repl.run("evaluate compose i in Unit from tt {} expecting tt;")), ["value: tt"]);
  assert.deepEqual(texts(await repl.run("compose // direction\n  i in (Unit and Unit) from (tt, tt) {}.1;")), ["value: tt"]);
  // A declaration that ends in a box, with its ; omitted, is complete.
  assert.deepEqual(texts(await repl.run("def moved := compose i in Unit from tt {}")), ["defined: moved : Unit"]);
});

test("a session over a proof sees its names, and rebases onto a rechecked proof", async t => {
  const repl = await session(t, "import nat; use nat;\ndef double(n : Nat) := n + n;\n");
  assert.deepEqual(texts(await repl.run("evaluate double(21);")), ["value: 42"]);
  assert.deepEqual(texts(await repl.run("let y := double(2);")), ["defined: y : Nat"]);
  assert.equal(repl.program.main, "proof", "the program still presents the proof");
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  await program.check("import nat; use nat;\ndef double(n : Nat) := n + n + n;\n", "proof");
  const rebased = await repl.rebase(program);
  assert.deepEqual(texts(await rebased.run("evaluate y")), ["value: 6"]);
});

test("slash commands: /modules lists what import can load, /help the commands", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const modules = async () => ({ library: ["lists"], archive: ["lists", "primes", "euclid", "cubical_paths"] });
  const repl = new ReplSession(program, { modules });
  // The library shadows the archive's module of the same name.
  assert.deepEqual(texts(await repl.run("/modules")),
    ["info: Library (1): lists\nArchive, the first library (3): cubical_paths, euclid, primes\nLoad one with import NAME;"]);
  assert.deepEqual(texts(await repl.run("/modules prime")), ["info: Archive, the first library (1): primes\nLoad one with import NAME;"]);
  assert.deepEqual(texts(await repl.run("/modules zeta")), ["info: No importable module's name contains zeta."]);
  assert.deepEqual(await repl.run("/help"), await repl.run("help"));
  assert.match(texts(await repl.run("/help"))[0], /\/modules \[TEXT\][\s\S]*\/clear[\s\S]*\/restart/);
  // The console clears and restarts itself; a session only says so.
  assert.deepEqual(texts(await repl.run("/clear")), ["error: E236: /clear is a command of the console, not of an entry."]);
  assert.deepEqual(texts(await repl.run("/frobnicate")), ["error: E237: Unknown command /frobnicate. /help lists the commands."]);
  // A rebased session keeps its module list.
  assert.equal((await repl.rebase(program)).modules, modules);
  assert.deepEqual(texts(await new ReplSession(program).run("/modules")), ["error: E238: This session cannot list its modules."]);
});
