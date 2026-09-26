import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession, replStatements } from "../web/repl-session.mjs";

const readLibrary = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8")
  .catch(() => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8"));
async function session(t, source = null) {
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
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
});

test("let binds, typeof shows the type, and evaluate the value", async t => {
  const repl = await session(t);
  assert.deepEqual(texts(await repl.run("let x := 7;")), ["defined: x : Nat"]);
  assert.deepEqual(texts(await repl.run("typeof x;")), ["type: Nat"]);
  assert.deepEqual(texts(await repl.run("evaluate x;")), ["value: 7"]);
  // A term alone is evaluated, and a last statement may omit its `;`.
  assert.deepEqual(texts(await repl.run("x")), ["value: 7"]);
  assert.deepEqual(texts(await repl.run("typeof fun (n : Nat) => succ(n)")), ["type: Nat -> Nat"]);
});

test("imports, declarations with blocks, and errors that leave the session unchanged", async t => {
  const repl = await session(t);
  assert.deepEqual(texts(await repl.run("import naturals;")), ["info: Imported naturals."]);
  assert.deepEqual(texts(await repl.run("evaluate 2 + 3 * 4;")), ["value: 14"]);
  assert.deepEqual(texts(await repl.run("def four_is_four : 2 + 2 = 4 {\n  exact refl(4);\n}")), ["defined: four_is_four : 2 + 2 = 4"]);
  assert.deepEqual(texts(await repl.run("def wrong : 2 + 2 = 5 {\n  exact refl(4);\n}")),
    ["error: Type mismatch: found 4 = 4, expected 2 + 2 = 5."]);
  assert.deepEqual(texts(await repl.run("typeof wrong;")), ["error: Untranslated name: wrong"]);
  assert.deepEqual(texts(await repl.run("typeof nowhere")), ["error: Untranslated name: nowhere"]);
  assert.deepEqual(texts(await repl.run("import nowhere;")).length, 1);
  // Later entries still see everything that checked.
  assert.deepEqual(texts(await repl.run("typeof four_is_four; evaluate double(3)")).slice(0, 1), ["type: 2 + 2 = 4"]);
});

test("a session over a proof sees its names, and rebases onto a rechecked proof", async t => {
  const repl = await session(t, "import naturals;\ndef double(n : Nat) := n + n;\n");
  assert.deepEqual(texts(await repl.run("evaluate double(21);")), ["value: 42"]);
  assert.deepEqual(texts(await repl.run("let y := double(2);")), ["defined: y : Nat"]);
  assert.equal(repl.program.main, "proof", "the program still presents the proof");
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
  t.after(() => program.dispose());
  await program.check("import naturals;\ndef double(n : Nat) := n + n + n;\n", "proof");
  const rebased = await repl.rebase(program);
  assert.deepEqual(texts(await rebased.run("evaluate y")), ["value: 6"]);
});
