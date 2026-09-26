import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { instructions } from "../web/cubical-instructions.mjs";

const readLibrary = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");
const source = `import naturals;

def lt(n, m : Nat) : U0 {
  exact exists k : Nat. succ(k) + n = m;
}

def lt_succ(n : Nat) : lt(n, succ(n)) {
  exact (0, refl(succ(n)));
}

def exists_greater_number : forall n : Nat. exists m : Nat. lt(n, m) {
  intro n;
  exact (succ(n), lt_succ(n));
}
`;

async function checked(t) {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check(source, "first");
  return program.kernel;
}

test("the first proof and the naturals library derive in instruction mode, at their checked types", async t => {
  const kernel = await checked(t);
  const derived = [];
  for (const [name, reference] of kernel.definitions) {
    const { value, type } = kernel.definition(reference);
    const driver = new InstructionDriver(kernel);
    // trans needs compound interval formulas and composition (Stage 3).
    if (name === "naturals__nat_add_comm") {
      assert.throws(() => driver.check(value, type), /compound interval formula/);
      continue;
    }
    const judgement = driver.graph.judgement(driver.check(value, type));
    assert.equal(judgement.kind, "typing", name);
    assert.deepEqual(judgement.context, [], name);
    // The type is the checked one. The term may differ in an annotation the
    // driver reduced, such as a pair's type, so it is equal by computation.
    assert.ok(driver.alpha(judgement.type, type), name);
    derived.push(name);
  }
  assert.deepEqual(derived, ["naturals__add", "naturals__mul", "naturals__le", "naturals__isLt",
    "naturals__nat_add_zero", "naturals__nat_add_succ", "naturals__nat_add_assoc", "naturals__nat_le_refl",
    "first__lt", "first__lt_succ", "first__exists_greater_number"]);
});

test("the judgement graph records each derivation: rule, premises, highlighted steps and entries", async t => {
  const kernel = await checked(t);
  const { value, type } = kernel.definition(kernel.definitions.get("first__lt_succ"));
  const driver = new InstructionDriver(kernel), graph = driver.graph;
  const root = graph.judgement(driver.check(value, type));
  // Walk the derivation from its conclusion.
  const seen = new Map(), stack = [root.id];
  while (stack.length) {
    const id = stack.pop();
    if (seen.has(id)) continue;
    const judgement = graph.judgement(id);
    seen.set(id, judgement);
    assert.ok(instructions.includes(judgement.rule), judgement.rule);
    for (const premise of judgement.premises) { assert.ok(premise < id); stack.push(premise); }
  }
  const rules = new Set([...seen.values()].map(judgement => judgement.rule));
  for (const rule of ["lambda", "pair", "pathLambda", "apply", "lookup", "variable", "convert", "step"])
    assert.ok(rules.has(rule), rule);
  // The goal lt(n, succ(n)) is unfolded by steps highlighted at positions.
  const steps = [...seen.values()].filter(judgement => judgement.rule === "step");
  assert.ok(steps.some(step => step.stepRule === "delta"));
  assert.ok(steps.every(step => Array.isArray(step.position) && ["term", "other", "type"].includes(step.side)));
  // The lambda binds an entry n : Nat, justified by NatForm.
  const lambda = [...seen.values()].find(judgement => judgement.rule === "lambda");
  const entry = graph.entry(lambda.entry);
  assert.equal(entry.dimension, false);
  assert.equal(graph.judgement(entry.source).rule, "nat");
  // Repeating an instruction returns the same judgement.
  assert.equal(driver.check(value, type), root.id);
});
