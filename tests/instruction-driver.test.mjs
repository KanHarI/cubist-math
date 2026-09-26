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

test("the first proof and the naturals library, trans included, derive in instruction mode, at their checked types", async t => {
  const kernel = await checked(t);
  const derived = [];
  for (const [name, reference] of kernel.definitions) {
    const { value, type } = kernel.definition(reference);
    const driver = new InstructionDriver(kernel);
    const judgement = driver.graph.judgement(driver.check(value, type));
    assert.equal(judgement.kind, "typing", name);
    assert.deepEqual(judgement.context, [], name);
    // The term is the checked one, and so is its type.
    assert.ok(driver.alpha(judgement.term, value), name);
    assert.ok(driver.alpha(judgement.type, type), name);
    derived.push(name);
  }
  assert.deepEqual(derived, ["naturals__add", "naturals__mul", "naturals__le", "naturals__isLt",
    "naturals__nat_add_zero", "naturals__nat_add_succ", "naturals__nat_add_assoc", "naturals__nat_add_comm",
    "naturals__nat_le_refl",
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

test("every definition behind Euclid's theorem derives in instruction mode", async t => {
  const readArchive = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
  const program = new CubicalProgram(await createCubical(), readArchive);
  t.after(() => program.dispose());
  await program.check(await readArchive("euclid"), "euclid");
  const kernel = program.kernel, failures = [];
  for (const [name, reference] of kernel.definitions) {
    const { value, type } = kernel.definition(reference);
    const driver = new InstructionDriver(kernel);
    try {
      const judgement = driver.graph.judgement(driver.check(value, type));
      assert.deepEqual(judgement.context, [], name);
      assert.ok(driver.alpha(judgement.term, value), name);
      assert.ok(driver.alpha(judgement.type, type), name);
    } catch (error) { failures.push(`${name}: ${error.message}`); }
  }
  assert.deepEqual(failures, []);
  // sym and trans: a path at 1 - i, and composition with tubes on two faces.
  const rules = new Set();
  const { value, type } = kernel.definition(kernel.definitions.get("primes__nat_add_comm"));
  const driver = new InstructionDriver(kernel);
  for (const stack = [driver.check(value, type)], seen = new Set(); stack.length;) {
    const id = stack.pop();
    if (seen.has(id)) continue;
    seen.add(id);
    const judgement = driver.graph.judgement(id);
    rules.add(judgement.rule);
    stack.push(...judgement.premises);
  }
  for (const rule of ["pathAt", "system", "systemTube", "comp"]) assert.ok(rules.has(rule), rule);
});

test("a derived term is its source: a constructor at a type that reduces keeps that type", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check(`import naturals;

def NatSum : U0 {
  exact Nat or Nat;
}

def left_zero : NatSum {
  exact typed(NatSum, left(0));
}

def tag(c : NatSum) : Nat {
  exact 1;
}

def tag_left_zero : tag(typed(NatSum, left(0))) = 1 {
  exact refl(1);
}
`, "sums");
  const kernel = program.kernel;
  for (const name of ["sums__left_zero", "sums__tag_left_zero"]) {
    const { value, type } = kernel.definition(kernel.definitions.get(name));
    const driver = new InstructionDriver(kernel);
    const judgement = driver.graph.judgement(driver.check(value, type));
    // The injection is built at Nat + Nat, and both its annotation and its
    // type are rewritten back to NatSum.
    assert.ok(driver.alpha(judgement.term, value), name);
    assert.ok(driver.alpha(judgement.type, type), name);
  }
});

test("search: a composition whose face holds contracts by one step, and a failed congruence is not retried", async t => {
  const readArchive = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
  for (const [module, name, rule] of [
    // Unfolding the other side here would compute 10! in unary.
    ["binary_univalence_transfer", "binary_univalence_transfer__binary_factorial_ten_via_nat", "face"],
    // A group and its lift to U1 agree by projections, not by their pairs'
    // annotations; congruence on the pairs fails, and must not repeat.
    ["quotient_group_universal", "quotient_group_universal__killing_subgroup_respects_cosets_at", null]]) {
    const program = new CubicalProgram(await createCubical(), readArchive);
    t.after(() => program.dispose());
    await program.check(await readArchive(module), module);
    const kernel = program.kernel, { value, type } = kernel.definition(kernel.definitions.get(name));
    const driver = new InstructionDriver(kernel), rules = new Set();
    for (const stack = [driver.check(value, type)], seen = new Set(); stack.length;) {
      const id = stack.pop();
      if (seen.has(id)) continue;
      seen.add(id);
      const judgement = driver.graph.judgement(id);
      if (judgement.stepRule) rules.add(judgement.stepRule);
      stack.push(...judgement.premises);
    }
    if (rule) assert.ok(rules.has(rule), `${name} uses a ${rule} step`);
  }
});

test("composition with overlapping faces: each overlap has its equality, and a tube on the face 0 is vacuous", async t => {
  const readArchive = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
  const program = new CubicalProgram(await createCubical(), readArchive);
  t.after(() => program.dispose());
  await program.check(await readArchive("paths"), "paths");
  const kernel = program.kernel;
  // right_unit composes over [j = 0, j = 1, i = 1]: the last face meets both
  // others. transport_constant's type has a composition on the face 0.
  for (const [name, rule] of [["paths__right_unit", "systemOverlap"], ["paths__transport_constant", "systemTube"]]) {
    const { value, type } = kernel.definition(kernel.definitions.get(name));
    const driver = new InstructionDriver(kernel), counts = new Map();
    const root = driver.graph.judgement(driver.check(value, type));
    assert.ok(driver.alpha(root.term, value) && driver.alpha(root.type, type), name);
    for (const stack = [root.id], seen = new Set(); stack.length;) {
      const id = stack.pop();
      if (seen.has(id)) continue;
      seen.add(id);
      const judgement = driver.graph.judgement(id);
      counts.set(judgement.rule, (counts.get(judgement.rule) ?? 0) + 1);
      stack.push(...judgement.premises);
    }
    assert.ok(counts.get(rule) > 0, `${name} uses ${rule}`);
  }
  const { value } = kernel.definition(kernel.definitions.get("paths__right_unit"));
  const driver = new InstructionDriver(kernel), graph = driver.graph;
  const overlaps = [];
  for (const stack = [driver.check(value, kernel.definition(kernel.definitions.get("paths__right_unit")).type)], seen = new Set(); stack.length;) {
    const id = stack.pop();
    if (seen.has(id)) continue;
    seen.add(id);
    const judgement = graph.judgement(id);
    if (judgement.rule === "systemOverlap") overlaps.push(judgement.operands[0]);
    stack.push(...judgement.premises);
  }
  assert.deepEqual(overlaps.sort(), [0, 1]);
});

test("pushouts: the suspension, its points and meridian, and its induction principle derive", async t => {
  const readArchive = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
  const program = new CubicalProgram(await createCubical(), readArchive);
  t.after(() => program.dispose());
  await program.check(await readArchive("suspension_types"), "suspension_types");
  const kernel = program.kernel, rules = new Set(), failures = [];
  for (const [name, reference] of kernel.definitions) {
    if (!name.startsWith("suspension_types__")) continue;
    const { value, type } = kernel.definition(reference);
    const driver = new InstructionDriver(kernel);
    try {
      const root = driver.graph.judgement(driver.check(value, type));
      assert.ok(driver.alpha(root.term, value) && driver.alpha(root.type, type), name);
      for (const stack = [root.id], seen = new Set(); stack.length;) {
        const id = stack.pop();
        if (seen.has(id)) continue;
        seen.add(id);
        const judgement = driver.graph.judgement(id);
        rules.add(judgement.rule);
        stack.push(...judgement.premises);
      }
    } catch (error) { failures.push(`${name}: ${error.message}`); }
  }
  assert.deepEqual(failures, []);
  for (const rule of ["pushout", "pushPoint", "pushPath", "pushElim"]) assert.ok(rules.has(rule), rule);
});

test("W types: binary positive numbers, their constructors and their recursion derive", async t => {
  const readArchive = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
  const program = new CubicalProgram(await createCubical(), readArchive);
  t.after(() => program.dispose());
  await program.check(await readArchive("binary_naturals"), "binary_naturals");
  const kernel = program.kernel, rules = new Set(), failures = [];
  for (const [name, reference] of kernel.definitions) {
    if (!name.startsWith("binary_naturals__")) continue;
    const { value, type } = kernel.definition(reference);
    const driver = new InstructionDriver(kernel);
    try {
      const root = driver.graph.judgement(driver.check(value, type));
      assert.ok(driver.alpha(root.term, value) && driver.alpha(root.type, type), name);
      for (const stack = [root.id], seen = new Set(); stack.length;) {
        const id = stack.pop();
        if (seen.has(id)) continue;
        seen.add(id);
        const judgement = driver.graph.judgement(id);
        rules.add(judgement.rule);
        stack.push(...judgement.premises);
      }
    } catch (error) { failures.push(`${name}: ${error.message}`); }
  }
  assert.deepEqual(failures, []);
  for (const rule of ["w", "sup", "wElim"]) assert.ok(rules.has(rule), rule);
});

test("Glue: univalence derives, and so does a Glue term over its Glue type", async t => {
  const readArchive = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
  const program = new CubicalProgram(await createCubical(), readArchive);
  t.after(() => program.dispose());
  await program.check(await readArchive("binary_univalence_transfer"), "binary_univalence_transfer");
  const kernel = program.kernel, rules = new Set();
  const derive = (value, type) => {
    const driver = new InstructionDriver(kernel);
    const root = driver.graph.judgement(driver.check(value, type));
    assert.ok(driver.alpha(root.term, value) && driver.alpha(root.type, type));
    for (const stack = [root.id], seen = new Set(); stack.length;) {
      const id = stack.pop();
      if (seen.has(id)) continue;
      seen.add(id);
      const judgement = driver.graph.judgement(id);
      rules.add(judgement.rule);
      stack.push(...judgement.premises);
    }
  };
  for (const name of ["builtin__ua__U0", "builtin__UnivalenceBeta__U0"]) {
    const { value, type } = kernel.definition(kernel.definitions.get(name));
    derive(value, type);
  }
  for (const rule of ["glueBase", "gluePiece", "glueOverlap", "glue", "unglue"]) assert.ok(rules.has(rule), rule);
  // λA B e (a : A). <i> glue(e(a), [i = 0 ↦ a, i = 1 ↦ e(a)]) : ua's line,
  // built on the Glue type in ua's body; the term checker accepts it first.
  let body = kernel.definition(kernel.definitions.get("builtin__ua__U0")).value;
  const binders = [];
  while (kernel.node(body).kind === "Lam") { binders.push(kernel.node(body)); body = kernel.node(body).children[1]; }
  const line = kernel.node(body), glue = line.children[1];
  const [, first] = kernel.node(glue).children, second = kernel.node(first).children[2];
  const [source, equivalence] = kernel.node(first).children, a = kernel.symbol("glued'a");
  const image = kernel.term("App", 0, kernel.term("Fst", 0, equivalence), kernel.term("Var", a));
  const values = kernel.term("Tube", kernel.node(first).payload, kernel.term("Var", a),
    kernel.term("Tube", kernel.node(second).payload, image));
  const path = kernel.term("PLam", line.payload, glue, kernel.term("GlueTerm", 0, glue, image, values));
  const value = binders.reduceRight((inner, binder) => kernel.term("Lam", binder.payload, binder.children[0], inner),
    kernel.term("Lam", a, source, path));
  const checked = kernel.check(value);
  rules.clear();
  derive(checked.expression, checked.type);
  for (const rule of ["glueTermBase", "glueTermPiece", "glueTerm"]) assert.ok(rules.has(rule), rule);
});
