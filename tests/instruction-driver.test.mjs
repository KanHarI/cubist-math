import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { instructions } from "../web/cubical-instructions.mjs";
import { judgementGraph } from "../web/cubical-graph-view.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { cubicalText } from "../web/cubical-notation.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { levelNormal } from "../web/cubical-levels.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";

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
  for (const name of ["builtin__ua", "builtin__UnivalenceBeta"]) {
    const { value, type } = kernel.definition(kernel.definitions.get(name));
    derive(value, type);
  }
  for (const rule of ["glueBase", "gluePiece", "glueOverlap", "glue", "unglue"]) assert.ok(rules.has(rule), rule);
  // λA B e (a : A). <i> glue(e(a), [i = 0 ↦ a, i = 1 ↦ e(a)]) : ua's line,
  // built on the Glue type in the body of the generic ua instantiated at U0
  // (level β); the term checker, which knows closed levels only, accepts it
  // first.
  const generic = kernel.definition(kernel.definitions.get("builtin__ua")).value;
  let body = kernel.head(kernel.term("LApp", 0, generic, kernel.term("LConst", 0)));
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

test("G0: the driver derives universe-generic terms, and compares levels by normal form", async t => {
  const kernel = new CubicalKernel(await createCubical());
  t.after(() => kernel.dispose());
  const syntax = new CubicalSyntax(kernel);
  const v = name => ({ tag: "Var", name }), U = level => ({ tag: "U", level });
  const succ = level => ({ tag: "LSucc", count: 1, level }), max = (left, right) => ({ tag: "LMax", left, right });
  const derive = (term, type) => {
    const driver = new InstructionDriver(kernel);
    return driver.graph.judgement(driver.check(syntax.encode(term), syntax.encode(type)));
  };
  // id := λ (x < ω). λ (A : U(x)). λ (a : A). a, checked once at a statement
  // whose bound names differ.
  const id = { tag: "LLam", name: "x", body: { tag: "Lam", name: "A", domain: U(v("x")), body: { tag: "Lam", name: "a", domain: v("A"), body: v("a") } } };
  const idType = { tag: "LPi", name: "y", body: { tag: "Pi", name: "B", domain: U(v("y")), body: { tag: "Pi", name: "b", domain: v("B"), body: v("B") } } };
  const checked = derive(id, idType);
  assert.equal(checked.context.length, 0);
  assert.deepEqual(syntax.decode(checked.term), id);
  // The same definition at level 1: id {1} U0 Nat : U0.
  const atOne = { tag: "App", fn: { tag: "App", fn: { tag: "LApp", fn: id, level: 1 }, arg: U(0) }, arg: { tag: "Nat" } };
  assert.deepEqual(syntax.decode(derive(atOne, U(0)).type), U(0));
  // The expected type (λ (x < ω). U(x)) {1} is U(1) by a level Beta step.
  const family = { tag: "LApp", fn: { tag: "LLam", name: "x", body: U(v("x")) }, level: 1 };
  assert.equal(derive(U(0), family).rule, "convert");
  // Levels whose canonical nodes order their variables differently still
  // agree: z pairs with x and x with w.
  const nested = { tag: "LLam", name: "x", body: { tag: "LLam", name: "z", body: U(max(v("x"), v("z"))) } };
  const renamed = { tag: "LPi", name: "w", body: { tag: "LPi", name: "x", body: U(succ(max(v("w"), v("x")))) } };
  assert.equal(derive(nested, renamed).context.length, 0);
  // Cumulativity under a level binder (C11), and a universe not in itself (C3).
  derive({ tag: "LLam", name: "x", body: { tag: "Nat" } }, { tag: "LPi", name: "x", body: U(1) });
  assert.throws(() => derive({ tag: "LLam", name: "x", body: U(v("x")) }, { tag: "LPi", name: "x", body: U(v("x")) }),
    /Type mismatch|not included/);
  // Displays: kernel notation, and the source syntax L1.1 will parse.
  assert.equal(cubicalText(idType), "Π (y < ω), Π (B : y), (B → B)");
  assert.equal(cubicalText(atOne), "(λ (x < ω). λ (A : x). λ (a : A). a)(U1, U0, Nat)");
  assert.equal(sourceText(idType), "forall y < UU0. forall B : y. B -> B");
  assert.equal(sourceText(renamed), "forall w < UU0. forall x < UU0. next(max(w, x))");
});

test("G0: the driver's level normal forms agree with the kernel's on random levels", async t => {
  const kernel = new CubicalKernel(await createCubical());
  t.after(() => kernel.dispose());
  const syntax = new CubicalSyntax(kernel), g = new InstructionGraph(kernel);
  const names = ["x", "y", "z"];
  names.forEach(name => g.level(name));
  let seed = 7;
  const roll = bound => (seed = (seed * 1103515245 + 12345) % 2147483648) % bound;
  const random = depth => {
    switch (depth ? roll(5) : roll(2)) {
      case 0: return roll(4) ? roll(4) : { tag: "LConst", tier: 1 + roll(2), value: roll(4) };
      case 1: return { tag: "Var", name: names[roll(3)] };
      case 2: return { tag: "LSucc", count: 1 + roll(2), level: random(depth - 1) };
      default: return { tag: "LMax", left: random(depth - 1), right: random(depth - 1) };
    }
  };
  const read = id => kernel.node(id), same = (a, b) => a.tier === b.tier && a.constant === b.constant
    && a.offsets.size === b.offsets.size && [...a.offsets].every(([key, offset]) => b.offsets.get(key) === offset);
  let equal = 0;
  for (let i = 0; i < 400; i++) {
    const a = syntax.encodeLevel(random(3)), b = syntax.encodeLevel(i % 3 ? random(3) : random(1));
    // The kernel's universes at equal levels are one term.
    const kernelSays = g.judgement(g.universe(a)).term === g.judgement(g.universe(b)).term;
    assert.equal(same(levelNormal(read, a), levelNormal(read, b)), kernelSays);
    equal += kernelSays;
  }
  assert.ok(equal > 0);
});

test("the driver's guide compares weak heads: equal, different, or unknown", async t => {
  const kernel = new CubicalKernel(await createCubical());
  t.after(() => kernel.dispose());
  const syntax = new CubicalSyntax(kernel), driver = new InstructionDriver(kernel), e = term => syntax.encode(term);
  const guide = (x, y) => driver.guide(x, y, null, null, { left: 400 });
  const zero = { tag: "Zero" }, one = { tag: "Succ", value: zero }, two = { tag: "Succ", value: one }, nat = { tag: "Nat" };
  const successor = { tag: "Lam", name: "n", domain: nat, body: { tag: "Succ", value: { tag: "Var", name: "n" } } };
  // Equal after computing heads; different constructors or neutral terms.
  assert.equal(guide(e({ tag: "App", fn: successor, arg: one }), e(two)), true);
  assert.equal(guide(e(one), e(two)), false);
  assert.equal(guide(e(nat), e({ tag: "U", level: 0 })), false);
  assert.equal(guide(e({ tag: "Var", name: "x" }), e({ tag: "Var", name: "y" })), false);
  assert.equal(guide(e({ tag: "Var", name: "x" }), e(zero)), false);
  // A lambda against a neutral function may be equal by eta: unknown.
  assert.equal(guide(e({ tag: "Lam", name: "m", domain: nat, body: { tag: "Var", name: "m" } }), e({ tag: "Var", name: "f" })), null);
  // A path at an endpoint of its annotated type is that endpoint: nothing is
  // computed, and the path may be a variable.
  const annotation = e({ tag: "Path", dim: "i", family: nat, left: zero, right: one });
  const at = end => kernel.term("PApp", syntax.formula(end ? [[]] : [], "interval"), e({ tag: "Var", name: "p" }), annotation);
  assert.equal(guide(at(0), e(zero)), true);
  assert.equal(guide(at(1), e(one)), true);
  assert.equal(guide(at(0), e(one)), false);
});

test("a derivation in one context is not reused in another that types a variable differently", async t => {
  const kernel = new CubicalKernel(await createCubical());
  t.after(() => kernel.dispose());
  const syntax = new CubicalSyntax(kernel), driver = new InstructionDriver(kernel), graph = driver.graph;
  const x = { tag: "Var", name: "x" }, nat = { tag: "Nat" }, unit = { tag: "Unit" };
  const typeIn = type => syntax.decode(graph.judgement(driver.infer(syntax.encode(x), [[kernel.symbol("x"), syntax.encode(type)]])).type);
  assert.deepEqual(typeIn(nat), nat);
  // Each context's scope is its own memo key, including its assumptions.
  assert.deepEqual(typeIn(unit), unit);
  assert.throws(() => driver.check(syntax.encode(x), syntax.encode(nat), [[kernel.symbol("x"), syntax.encode(unit)]]),
    /Type mismatch/);
});

// The second review of #72. The kernel's weak head decides Glue eta by
// syntax, so a Glue term whose piece is the base's restriction only after a
// step stays a Glue term there; the driver's whnf move then takes its normal
// form, where the parts are compared reduced. G(d) = Glue [d = 0 ↦ (Unit, id)]
// Unit, p a path over G from point, b = p @ i: the constant tube
// glue [i = 0 ↦ point] (unglue b) of a composition over G(i) must agree with
// its base b, as b at i = 0 is p @ 0, which is point.
test("a Glue term that is its base by eta only after a step still agrees with it", async t => {
  const { T } = await import("../lib/cubical/core.mjs");
  const { face: F, interval: I } = await import("../lib/cubical/lattice.mjs");
  const { identityEquivalence } = await import("../lib/cubical/equivalence.mjs");
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check("def unit_point : Unit := point;\n", "glue_eta");
  const equivalence = identityEquivalence(T.unit);
  const G = face => T.glueType(T.unit, [{ face, type: T.unit, equiv: equivalence }]);
  const context = [["b1", G(F.bottom)], ["p", T.path("j", G(F.endpoint("j", 0)), T.point, T.variable("b1"))]];
  const b = T.at(T.variable("p"), I.variable("i")), over = G(F.endpoint("i", 0));
  const glued = T.glue(over, T.unglue(over, b), [{ face: F.endpoint("i", 0), term: T.point }]);
  const composite = T.comp("k", over, [{ face: F.endpoint("m", 0), term: glued }], b);
  const checked = program.checker.checkView(composite, over, context, new Map([["i", 0], ["m", 1]]));
  assert.equal(checked.term.tag, "Comp");
});

// The review of #73. The glue move is a last resort, bounded, and judged by
// alpha-equality. G = Glue [] Nat, u = glue_G [] x and H = Glue [] G: u and
// unglue_H(glue_H [] u) agree by the right side's weak head. Without syntax
// sharing, a normal form is a new handle even when nothing changed, so a
// move judged by handles would normalize u until the fuel ran out; and over a
// shared open graph t(n + 1) = f(t(n))(t(n)), normalizing u first would take
// time exponential in n, where the weak head needs none.
test("the glue move comes last, judges progress by syntax, and is bounded", async t => {
  const { T } = await import("../lib/cubical/core.mjs");
  const G = T.glueType(T.nat, []), H = T.glueType(G, []);
  const agrees = async (base, context, optimizations) => {
    const program = new CubicalProgram(await createCubical(), readLibrary, { optimizations });
    t.after(() => program.dispose());
    await program.check("def unit_point : Unit := point;\n", "glue_move");
    const u = T.glue(G, base, []), unglued = T.unglue(H, T.glue(H, u, []));
    const before = program.kernel.work();
    const checked = program.checker.checkView(T.line("i", G, u), T.path("i", G, u, unglued), context);
    const after = program.kernel.work();
    return { checked, instructions: after.instructions - before.instructions, exhausted: after.exhausted - before.exhausted,
      steps: after.instructionSteps - before.instructionSteps + after.querySteps - before.querySteps };
  };
  // Measured: 33 instructions here, where normalizing on the way took 40,027.
  const unshared = await agrees(T.variable("x"), [["x", T.nat]], { shareSyntax: false });
  assert.equal(unshared.checked.term.tag, "PLam");
  assert.ok(unshared.instructions < 1000, `${unshared.instructions} instructions`);
  // Measured: 473 steps here, where normalizing first ran out of all 10,000,000.
  let shared = T.variable("x");
  for (let n = 0; n < 40; n++) shared = T.app(T.app(T.variable("f"), shared), shared);
  const graph = await agrees(shared, [["x", T.nat], ["f", T.pi("a", T.nat, T.pi("b", T.nat, T.nat))]]);
  assert.equal(graph.checked.term.tag, "PLam");
  assert.ok(graph.steps < 100000 && graph.exhausted === 0, `${graph.steps} steps, ${graph.exhausted} exhausted`);
});
