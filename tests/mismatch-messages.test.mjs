import "./fresh-build.mjs";
import {naturalSort, numeral} from "../lib/cubical/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { displayTerm } from "../web/cubical-elaborator.mjs";

test("a type mismatch names the type found and the type expected, in source syntax", async t => {
  const program = new CubicalProgram(await createCubical(), async () => "", { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(`def Shape(value : Unit or Unit) := match value as z return U0 {
  left a => Nat;
  right b => Unit;
};
def wrong_index(P : Nat -> U0, f : forall n : Nat. P(n)) : P(1) {
  exact f(0);
}
def not_unit : Unit {
  exact 0;
}
def refined(value : Unit or Unit) : Shape(value) {
  cases value {
    left a => { exact 0; }
    right b => { exact tt; }
  }
}
`, "mismatches");
  const reason = name => result.outputs.find(output => output.name === name).reason;
  assert.equal(reason("wrong_index"), "Type mismatch: found P(0), expected P(1).");
  assert.equal(reason("not_unit"), "Type mismatch: found Nat, expected Unit.");
  // Module prefixes, generated suffixes and beta-redexes do not reach the message.
  assert.equal(reason("refined"), "Type mismatch: found Unit -> Nat, expected Unit -> Shape(value).");
});

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
  assert.equal(displayTerm({ tag: "Lam", name: "x7", domain: { tag: "Nat" }, body: { tag: "Var", name: "x7" } }).name, "x");
});

// The third review of #74: a mismatch's two sides are named together. The
// found side prints naturals' add, so a variable named add1 cannot show its
// stem add there; named alone, the expected side would have shown it as add.
test("a variable reads alike on both sides of a mismatch", async t => {
  const { readFile } = await import("node:fs/promises");
  const { T } = await import("../lib/cubical/core.mjs");
  const program = new CubicalProgram(await createCubical(), name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8"));
  t.after(() => program.dispose());
  await program.check("import naturals;\n", "main");
  const add = (a, b) => T.app(T.app({ tag: "DefRef", name: "naturals__add" }, a), b);
  const add1 = T.variable("add1"), context = [["add1", naturalSort], ["p", T.path("i", naturalSort, add(add1, numeral(1)), add1)]];
  let message = null;
  try { program.checker.checkView(T.variable("p"), T.path("i", naturalSort, add1, add1), context); }
  catch (error) { message = error.message; }
  assert.match(message ?? "", /^Type mismatch: found add1 \+ 1 = add1, expected add1 = add1\.$/);
});

// The fourth review of #74: every message that shows two terms of one scope
// names them together, as a mismatch does. `+` is naturals' add, captured as
// plus before a variable named add is introduced. That label prints on one
// side only, so the variable is named apart from it there; named alone, the
// other side would have shown it as add.
test("show and calc name the two terms they show together", async t => {
  const { readFile } = await import("node:fs/promises");
  const program = new CubicalProgram(await createCubical(), name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8"),
    { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(`import naturals;
def restated : forall add : Nat. add = add { let plus := add; intro add; show plus(add, 1) = add; }
def step_start : forall n : Nat. n = n { let plus := add; intro add; calc { add = add by refl(add); plus(add, 1) = add by refl(add); } }
def chain_end : forall n : Nat. n = n + 1 { intro add; calc { add = add by refl(add); } }
`, "main");
  const reason = name => result.outputs.find(output => output.name === name).reason;
  assert.match(reason("restated"), /^show requires a type equal to the goal by computation: found (\w+) \+ 1 = \1, expected \1 = \1\./);
  assert.match(reason("step_start"), /^calc step left endpoint does not match the preceding endpoint\. The step starts at (\w+) \+ 1; the chain so far ends at \1\./);
  assert.match(reason("chain_end"), /^calc final endpoint does not match the goal\. The chain ends at (\w+); the goal's right side is \1 \+ 1\./);
});
