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
  const checker = program.checker;
  const nat = { tag: "Nat" }, unit = { tag: "Unit" }, zero = { tag: "Zero" };
  const answer = checker.attempt(zero, unit);
  assert.equal(answer.ok, false);
  assert.equal(answer.failure, "mismatch");
  assert.equal(answer.error.message, "Type mismatch.");
  assert.ok(answer.error.mismatch.found && answer.error.mismatch.expected);
  assert.throws(() => checker.check(zero, unit), /^Error: Type mismatch: found Nat, expected Unit\.$/);
  assert.equal(checker.check(zero, nat).tag, "Zero");
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
