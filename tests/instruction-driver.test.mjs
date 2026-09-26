import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { instructions } from "../web/cubical-instructions.mjs";
import { judgementGraph } from "../web/cubical-graph-view.mjs";

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

test("the workbench's kernel graph lists lt_succ's derivation in THTH style", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check(source, "first");
  const view = program.inspect("first__lt_succ");
  const checked = program.checker.syntax.check(view.expression, view.type, [], new Map());
  const listing = judgementGraph(program, view, checked);
  const root = listing.rows.at(-1);
  assert.equal(root.number, listing.root);
  assert.equal(root.label, "PiIntro");
  assert.match(root.statement, /^\{\} ⊢ λ \(n : Nat\)\. .* : Π \(n : Nat\), lt\(n, succ\(n\)\)$/);
  // Numbered in derivation order, premises first, each used where it is cited.
  for (const row of listing.rows) for (const premise of row.premises) {
    assert.ok(premise < row.number);
    assert.ok(listing.rows[premise - 1].usedBy.includes(row.number));
  }
  // The goal lt(n, succ(n)) is unfolded at its highlighted head, then computed.
  const unfold = listing.rows.find(row => row.highlight?.rule === "delta" && row.highlight.text === "lt");
  assert.deepEqual(unfold.highlight.position, [0, 0]);
  assert.match(unfold.statement, /^\{n : Nat\} ⊢ lt\(n, succ\(n\)\) ≡ /);
  assert.ok(listing.rows.some(row => row.highlight?.rule === "iota"));
  assert.ok(listing.rows.some(row => row.label === "SigmaIntro" && /^\{n : Nat\} ⊢ \(0 , refl\(succ\(n\)\)\) : Σ/.test(row.statement)));
  assert.deepEqual(listing.entries.map(entry => entry.shown), ["n", "ascription", "d0"]);
});

test("a definition's body is derived on request, as its lookup's premise", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check(source, "first");
  const view = program.inspect("first__lt_succ");
  const checked = program.checker.syntax.check(view.expression, view.type, [], new Map());
  const folded = judgementGraph(program, view, checked);
  const lookup = folded.rows.find(row => row.definition?.name === "lt");
  assert.equal(lookup.definition.expanded, false);
  assert.equal(lookup.definition.root, null);
  // lt's body uses add; both are derived and spliced in, each before its lookup.
  const add = program.kernel.definitions.get("naturals__add");
  const listing = judgementGraph(program, view, checked, { expanded: new Set([lookup.definition.reference, add]) });
  for (const name of ["lt", "add"]) {
    const row = listing.rows.find(item => item.definition?.name === name);
    const body = listing.rows[row.definition.root - 1];
    assert.ok(body.number < row.number, name);
    assert.ok(body.usedBy.includes(row.number), name);
    assert.match(body.statement, /^\{\} ⊢ λ /, name);
  }
  for (const row of listing.rows) for (const premise of row.premises) assert.ok(premise < row.number);
  assert.equal(listing.rows.at(-1).number, listing.root);
  assert.ok(listing.rows.length > folded.rows.length);
});
