import "./fresh-build.mjs";
import {naturalSort, numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { displayTerm } from "../web/cubical-elaborator.mjs";

// Mismatches in source syntax, and calc's two terms named together, are
// cubist-tests/mismatch_*.cubist (tests/cubist-tests.test.mjs).

test("the kernel reports the mismatched handles, and speculative checks stay undescribed", async t => {
  const program = new CubicalProgram(await createCubical(), async () => "", { collectReferences: false });
  t.after(() => program.dispose());
  await program.check("import nat;", "main");
  const checker = program.checker;
  const nat = naturalSort, unit = { tag: "Unit" }, zero = numeral(0);
  const answer = checker.attempt(zero, unit);
  assert.equal(answer.ok, false);
  assert.equal(answer.failure, "mismatch");
  assert.equal(answer.error.message, "Type mismatch.");
  assert.ok(answer.error.mismatch.found && answer.error.mismatch.expected);
  assert.throws(() => checker.check(zero, unit), /^Error: Type mismatch: found Nat, expected Unit\.$/);
  assert.equal(checker.check(zero, nat).tag, "Con");
});

test("display renaming never merges two different names", () => {
  const term = { tag: "Pi", name: "A1", domain: { tag: "U", level: 0 },
    body: { tag: "Pi", name: "A2", domain: { tag: "U", level: 0 }, body: { tag: "Var", name: "A1" } } };
  const shown = displayTerm(term);
  assert.notEqual(shown.name, shown.body.name);
  assert.equal(shown.body.body.name, shown.name);
  // A lone generated name gets its stem back.
  assert.equal(displayTerm({ tag: "Lam", name: "x7", domain: { tag: "Unit" }, body: { tag: "Var", name: "x7" } }).name, "x");
});

// The third review of #74: a mismatch's two sides are named together. The
// found side prints nat's add, so a variable named add1 cannot show its
// stem add there; named alone, the expected side would have shown it as add.
test("a variable reads alike on both sides of a mismatch", async t => {
  const { readFile } = await import("node:fs/promises");
  const { T } = await import("../web/translator/core.mjs");
  const program = new CubicalProgram(await createCubical(), name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8"));
  t.after(() => program.dispose());
  await program.check("import nat;\n", "main");
  const add = (a, b) => T.app(T.app({ tag: "DefRef", name: "nat__add" }, a), b);
  const add1 = T.variable("add1"), context = [["add1", naturalSort], ["p", T.path("i", naturalSort, add(add1, numeral(1)), add1)]];
  let message = null;
  try { program.checker.checkView(T.variable("p"), T.path("i", naturalSort, add1, add1), context); }
  catch (error) { message = error.message; }
  // Nothing is selected here, so nat's addition is qualified (L2.10j).
  assert.match(message ?? "", /^Type mismatch: found nat\.\(add1 \+ 1\) = add1, expected add1 = add1\.$/);
});
