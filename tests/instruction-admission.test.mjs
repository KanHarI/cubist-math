// Stage 4: the instruction kernel admits every definition, and a tactic's
// committed check is derived by instructions as the tactic runs.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";

const readLibrary = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");
const source = `import naturals;

def two : Nat {
  exact 2;
}

def two_is_two : two = 2 {
  have same : 2 = 2 := refl(2);
  exact same;
}
`;

test("every definition is admitted by Define, and only admitted definitions can be looked up", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  const result = await program.check(source, "admitted");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const kernel = program.kernel, graph = new InstructionDriver(kernel).graph;
  for (const [name, reference] of kernel.definitions) {
    const view = program.checker.definitionViews.get(name);
    assert.ok(view.admission.judgements > 0, name);
    // Lookup succeeds only for a definition Define admitted.
    const lookup = graph.judgement(graph.lookup(reference));
    assert.equal(lookup.term, reference, name);
  }
  // The term checker's own definitions are refused.
  const zero = kernel.term("Point"), nat = kernel.term("Unit");
  const unadmitted = kernel.define("checked_only", zero, nat);
  assert.throws(() => graph.lookup(unadmitted), /admitted by Define/);
});

test("a tactic's check is derived as it runs, and fails at the tactic", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  const check = InstructionDriver.prototype.check;
  const issued = [];
  InstructionDriver.prototype.check = function (expression, type, context) {
    issued.push(this.kernel.node(expression).kind);
    return check.call(this, expression, type, context);
  };
  try { await program.check(source, "issued"); }
  finally { InstructionDriver.prototype.check = check; }
  // have's value, refl(2), is derived when have is elaborated; the
  // definitions are admitted after.
  assert.ok(issued.includes("PLam"), issued.join(", "));
  // An instruction failure in have's check is that tactic's error.
  InstructionDriver.prototype.check = function (expression, type, context) {
    if (this.kernel.node(expression).kind === "PLam") throw new Error("No rule for this yet.");
    return check.call(this, expression, type, context);
  };
  let result;
  try { result = await new CubicalProgram(await createCubical(), readLibrary).check(source, "failing"); }
  finally { InstructionDriver.prototype.check = check; }
  const failed = result.outputs.find(output => output.name === "two_is_two");
  assert.equal(failed.verified, false);
  // Reported at have, line 8, not at the declaration.
  assert.match(failed.reason, /^Instruction kernel: No rule for this yet\. at 8:3$/);
});

test("the driver steers by its own guide, and asks the term checker's conversion only when told to", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  assert.equal(program.kernel.conversionOracle, false);
  const result = await program.check(source, "unaided");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.equal(new InstructionDriver(program.kernel).oracle, false);
  assert.equal(new InstructionDriver(program.kernel, { oracle: true }).oracle, true);
  const graph = new InstructionDriver(program.kernel).graph;
  for (const [name, reference] of program.kernel.definitions) {
    const { value, type } = program.kernel.definition(reference);
    const driver = new InstructionDriver(program.kernel);
    driver.check(value, type);
    assert.equal(driver.equalities.size, 0, name);
    assert.equal(graph.judgement(graph.lookup(reference)).term, reference, name);
  }
});
