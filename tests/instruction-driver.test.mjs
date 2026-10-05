import "./fresh-build.mjs";
import {naturalSort,numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { InstructionDriver, searchLimits } from "../web/cubical-instruction-driver.mjs";
import { instructions } from "../web/cubical-instructions.mjs";
import { judgementGraph } from "../web/cubical-graph-view.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { cubicalText } from "../web/cubical-notation.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { levelNormal } from "../web/cubical-levels.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { checkTestModule } from "./check-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

const readLibrary = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");
// The Cubist cases are cubist-tests/driver_*.cubist (tests/cubist-tests.test.mjs
// compares their verdicts); here, their derivations.
const firstProof = t => checkTestModule(t, "driver_first_proof");

async function checked(t) {
  return (await firstProof(t)).program.kernel;
}

test("the first proof and nat, trans included, derive in instruction mode, at their checked types", async t => {
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
  assert.deepEqual(derived, ["nat__add", "nat__mul", "nat__le", "nat__isLt", "nat__nat_zero_add",
    "nat__nat_add_zero", "nat__nat_add_succ", "nat__nat_add_assoc", "nat__nat_add_comm", "nat__nat_le_refl",
    "driver_first_proof__lt", "driver_first_proof__lt_succ", "driver_first_proof__exists_greater_number"]);
});

test("the judgement graph records each derivation: rule, premises, highlighted steps and entries", async t => {
  const kernel = await checked(t);
  const { value, type } = kernel.definition(kernel.definitions.get("driver_first_proof__lt_succ"));
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
  assert.equal(graph.judgement(entry.source).rule, "sortBegin");
  // Repeating an instruction returns the same judgement.
  assert.equal(driver.check(value, type), root.id);
});

test("the workbench's kernel graph lists lt_succ's derivation in THTH style", async t => {
  const { program } = await firstProof(t);
  const view = program.inspect("driver_first_proof__lt_succ");
  const checked = program.checker.checkView(view.expression, view.type, [], new Map());
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
  const { program } = await firstProof(t);
  const view = program.inspect("driver_first_proof__lt_succ");
  const checked = program.checker.checkView(view.expression, view.type, [], new Map());
  const folded = judgementGraph(program, view, checked);
  const lookup = folded.rows.find(row => row.definition?.name === "lt");
  assert.equal(lookup.definition.expanded, false);
  assert.equal(lookup.definition.root, null);
  // lt's body uses add; both are derived and spliced in, each before its lookup.
  const add = program.kernel.definitions.get("nat__add");
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
  const readArchive = sourceReader();
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
  const { value, type } = kernel.definition(kernel.definitions.get("nat__nat_add_comm"));
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
  const { program } = await checkTestModule(t, "driver_sums");
  const kernel = program.kernel;
  for (const name of ["driver_sums__left_zero", "driver_sums__tag_left_zero"]) {
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
  const readArchive = sourceReader();
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
  const readArchive = sourceReader();
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

test("declared pushouts: the suspension, its points and meridian, and its induction principle derive", async t => {
  const readArchive = sourceReader();
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
  for (const rule of ["sortBegin", "construct", "eliminator"]) assert.ok(rules.has(rule), rule);
});

test("W types: binary positive numbers, their constructors and their recursion derive", async t => {
  const readArchive = sourceReader();
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
  for (const rule of ["sortBegin", "construct", "lookup"]) assert.ok(rules.has(rule), rule);
});

test("Glue: univalence derives, and so does a Glue term over its Glue type", async t => {
  const readArchive = sourceReader();
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
  // (level β). The driver infers its type, then derives it at that type.
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
  const inferring = new InstructionDriver(kernel), inferred = inferring.graph.judgement(inferring.infer(value));
  rules.clear();
  derive(inferred.term, inferred.type);
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
  // The same definition at level 1: id {1} U0 Unit : U0.
  const atOne = { tag: "App", fn: { tag: "App", fn: { tag: "LApp", fn: id, level: 1 }, arg: U(0) }, arg: { tag: "Unit" } };
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
  derive({ tag: "LLam", name: "x", body: { tag: "Unit" } }, { tag: "LPi", name: "x", body: U(1) });
  assert.throws(() => derive({ tag: "LLam", name: "x", body: U(v("x")) }, { tag: "LPi", name: "x", body: U(v("x")) }),
    /Type mismatch|not included/);
  // Displays: kernel notation, and the source syntax L1.1 will parse.
  assert.equal(cubicalText(idType), "Π (y < ω), Π (B : y), (B → B)");
  assert.equal(cubicalText(atOne), "(λ (x < ω). λ (A : x). λ (a : A). a)(U1, U0, Unit)");
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
  const unit = { tag: "Unit" }, point = { tag: "Point" }, bool = { tag: "Sum", left: unit, right: unit };
  const zero = { tag: "Inl", as: bool, value: point }, one = { tag: "Inr", as: bool, value: point };
  const wrap = { tag: "Lam", name: "n", domain: unit, body: { tag: "Inr", as: bool, value: { tag: "Var", name: "n" } } };
  // Equal after computing heads; different constructors or neutral terms.
  assert.equal(guide(e({ tag: "App", fn: wrap, arg: point }), e(one)), true);
  assert.equal(guide(e(zero), e(one)), false);
  assert.equal(guide(e(bool), e({ tag: "U", level: 0 })), false);
  assert.equal(guide(e({ tag: "Var", name: "x" }), e({ tag: "Var", name: "y" })), false);
  assert.equal(guide(e({ tag: "Var", name: "x" }), e(zero)), false);
  // A lambda against a neutral function may be equal by eta: unknown.
  assert.equal(guide(e({ tag: "Lam", name: "m", domain: bool, body: { tag: "Var", name: "m" } }), e({ tag: "Var", name: "f" })), null);
  // A path at an endpoint of its annotated type is that endpoint: nothing is
  // computed, and the path may be a variable.
  const annotation = e({ tag: "Path", dim: "i", family: bool, left: zero, right: one });
  const at = end => kernel.term("PApp", syntax.formula(end ? [[]] : [], "interval"), e({ tag: "Var", name: "p" }), annotation);
  assert.equal(guide(at(0), e(zero)), true);
  assert.equal(guide(at(1), e(one)), true);
  assert.equal(guide(at(0), e(one)), false);
});

test("a derivation in one context is not reused in another that types a variable differently", async t => {
  const kernel = new CubicalKernel(await createCubical());
  t.after(() => kernel.dispose());
  const syntax = new CubicalSyntax(kernel), driver = new InstructionDriver(kernel), graph = driver.graph;
  const x = { tag: "Var", name: "x" }, unit = { tag: "Unit" }, bool = { tag: "Sum", left: unit, right: unit };
  const typeIn = type => syntax.decode(graph.judgement(driver.infer(syntax.encode(x), [[kernel.symbol("x"), syntax.encode(type)]])).type);
  assert.deepEqual(typeIn(bool), bool);
  // Each context's scope is its own memo key, including its assumptions.
  assert.deepEqual(typeIn(unit), unit);
  assert.throws(() => driver.check(syntax.encode(x), syntax.encode(bool), [[kernel.symbol("x"), syntax.encode(unit)]]),
    /Type mismatch/);
});

// The second review of #72. The kernel's weak head decides Glue eta by
// syntax, so a Glue term whose piece is the base's restriction only after a
// step stays a Glue term there; the driver's glue move then contracts it by
// the Glue step, which compares the two reduced. G(d) = Glue [d = 0 ↦
// (Unit, id)] Unit, p a path over G from point, b = p @ i: the constant tube
// glue [i = 0 ↦ point] (unglue b) of a composition over G(i) must agree with
// its base b, as b at i = 0 is p @ 0, which is point.
test("a Glue term that is its base by eta only after a step still agrees with it", async t => {
  const { T } = await import("../web/translator/core.mjs");
  const { face: F, interval: I } = await import("../web/translator/lattice.mjs");
  const { identityEquivalence } = await import("../web/translator/equivalence.mjs");
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check("import nat;\ndef unit_point : Unit := tt;\n", "glue_eta");
  const equivalence = identityEquivalence(T.unit);
  const G = face => T.glueType(T.unit, [{ face, type: T.unit, equiv: equivalence }]);
  const context = [["b1", G(F.bottom)], ["p", T.path("j", G(F.endpoint("j", 0)), T.point, T.variable("b1"))]];
  const b = T.at(T.variable("p"), I.variable("i")), over = G(F.endpoint("i", 0));
  const glued = T.glue(over, T.unglue(over, b), [{ face: F.endpoint("i", 0), term: T.point }]);
  const composite = T.comp("k", over, [{ face: F.endpoint("m", 0), term: glued }], b);
  const checked = program.checker.checkView(composite, over, context, new Map([["i", 0], ["m", 1]]));
  assert.equal(checked.term.tag, "Comp");
});

// The review of #73. The glue move is a last resort. G = Glue [] Nat,
// u = glue_G [] x and H = Glue [] G: u and unglue_H(glue_H [] u) agree by the
// right side's weak head. A move that took u's normal form first would, over
// a shared open graph t(n + 1) = f(t(n))(t(n)), take time exponential in n,
// where the weak head needs none; without syntax sharing, a normal form is a
// new handle even when nothing changed.
test("the glue move comes last, after the weak heads", async t => {
  const { T } = await import("../web/translator/core.mjs");
  const G = T.glueType(naturalSort, []), H = T.glueType(G, []);
  const agrees = async (base, context, optimizations) => {
    const program = new CubicalProgram(await createCubical(), readLibrary, { optimizations });
    t.after(() => program.dispose());
    await program.check("import nat;\ndef unit_point : Unit := tt;\n", "glue_move");
    const u = T.glue(G, base, []), unglued = T.unglue(H, T.glue(H, u, []));
    const before = program.kernel.work();
    const checked = program.checker.checkView(T.line("i", G, u), T.path("i", G, u, unglued), context);
    const after = program.kernel.work();
    return { checked, instructions: after.instructions - before.instructions, exhausted: after.exhausted - before.exhausted,
      steps: after.instructionSteps - before.instructionSteps + after.querySteps - before.querySteps };
  };
  // Measured: 33 instructions here, where normalizing on the way took 40,027.
  const unshared = await agrees(T.variable("x"), [["x", naturalSort]], { shareSyntax: false });
  assert.equal(unshared.checked.term.tag, "PLam");
  assert.ok(unshared.instructions < 1000, `${unshared.instructions} instructions`);
  // Measured: 473 steps here, where normalizing first ran out of all 10,000,000.
  let shared = T.variable("x");
  for (let n = 0; n < 40; n++) shared = T.app(T.app(T.variable("f"), shared), shared);
  const graph = await agrees(shared, [["x", naturalSort], ["f", T.pi("a", naturalSort, T.pi("b", naturalSort, naturalSort))]]);
  assert.equal(graph.checked.term.tag, "PLam");
  assert.ok(graph.steps < 100000 && graph.exhausted === 0, `${graph.steps} steps, ${graph.exhausted} exhausted`);
});

// The second review of #73: the glue move itself, where only it is left.
const glueSession = async (t, optimizations = {}) => {
  const { T } = await import("../web/translator/core.mjs");
  const { heuristicPolicy } = await import("../web/cubical-instruction-driver.mjs");
  const program = new CubicalProgram(await createCubical(), readLibrary, { optimizations });
  t.after(() => program.dispose());
  await program.check("import nat;\ndef unit_point : Unit := tt;\n", "glue_move");
  // Each move made, its outcome, and the kernel steps since the one before.
  const made = [], spent = [], steps = () => { const w = program.kernel.work(); return w.instructionSteps + w.querySteps; };
  let last = steps();
  program.kernel.policy = { name: "recording", rank: point => heuristicPolicy.rank(point),
    observe: (point, move, outcome) => {
      const name = `${move.move}${move.side ? `:${move.side}` : ""}:${outcome}`, now = steps();
      made.push(name); spent.push([name, now - last]); last = now;
    } };
  // A path between two Glue terms of G = Glue [] Nat, which only agree when
  // their bases do: the comparison fails, and its last moves are glue moves.
  const G = T.glueType(naturalSort, []);
  const compare = (left, right, context) => {
    const before = program.kernel.work();
    let error = null;
    try { program.checker.checkView(T.line("i", G, T.glue(G, left, [])), T.path("i", G, T.glue(G, left, []), T.glue(G, right, [])), context); }
    catch (thrown) { error = thrown; }
    const after = program.kernel.work();
    return { error, instructions: after.instructions - before.instructions, exhausted: after.exhausted - before.exhausted,
      steps: after.instructionSteps - before.instructionSteps + after.querySteps - before.querySteps };
  };
  return { T, program, made, spent, compare };
};

test("the glue move: no Glue eta redex is no progress, and the move's budget is its own", async t => {
  // A Glue term whose base is no unglue: the Glue step does not apply, and
  // the move is stuck, even without syntax sharing.
  const plain = await glueSession(t, { shareSyntax: false });
  const run = plain.compare(plain.T.variable("x"), plain.T.variable("y"), [["x", naturalSort], ["y", naturalSort]]);
  assert.ok(run.error, "different bases do not agree");
  assert.ok(plain.made.includes("glue:left:stuck"), plain.made.join(" "));
  assert.ok(run.instructions < 1000, `${run.instructions} instructions`);
  // The Glue step runs within the move's own budget, and running out of it
  // is no progress: the comparison goes on to its own mismatch.
  const shared = await glueSession(t);
  const { T } = shared;
  const { KernelError } = await import("../web/cubical-kernel.mjs");
  const g = shared.program.checker.driver.graph, within = g.within, budgets = [];
  g.within = steps => { budgets.push(steps); throw new KernelError("Kernel checking/reduction budget exhausted.", "budget"); };
  const heavy = shared.compare(T.variable("x"), T.variable("y"), [["x", naturalSort], ["y", naturalSort]]);
  g.within = within;
  assert.ok(heavy.error && heavy.error.kind !== "budget", heavy.error?.message);
  assert.ok(budgets.length && budgets.every(steps => steps === searchLimits.glueSteps), JSON.stringify(budgets));
  assert.ok(shared.made.includes("glue:left:stuck"), shared.made.join(" "));
  // And an operation within a budget of its own gives the session's back.
  const typing = shared.program.checker.driver.check(
    shared.program.checker.syntax.encode(T.app(T.lam("n", naturalSort, T.app(T.constructor(1,naturalSort,"succ"),T.variable("n"))), numeral(0))),
    shared.program.checker.syntax.encode(naturalSort));
  assert.throws(() => g.within(1, () => g.step(g.refl(typing), "other", [], "normalize")), error => error.kind === "budget");
  assert.ok(g.step(g.refl(typing), "other", [], "normalize"), "the session's budget is back");
});

test("the glue move rethrows a deadline, and a Glue term needs it at every focus", async t => {
  const { T, program, compare } = await glueSession(t);
  const { KernelError } = await import("../web/cubical-kernel.mjs");
  const graph = program.checker.driver.graph, within = graph.within;
  graph.within = () => { throw new KernelError("Declaration time limit exceeded.", "deadline"); };
  const interrupted = compare(T.variable("x"), T.variable("y"), [["x", naturalSort], ["y", naturalSort]]);
  graph.within = within;
  assert.equal(interrupted.error?.kind, "deadline", interrupted.error?.message);
  // Two tubes of one composition, each the same Glue term that is its base by
  // eta only after a step: the move rewrites one focus, and must still be
  // open at the other.
  const { face: F, interval: I } = await import("../web/translator/lattice.mjs");
  const { identityEquivalence } = await import("../web/translator/equivalence.mjs");
  const equivalence = identityEquivalence(T.unit);
  const Gd = face => T.glueType(T.unit, [{ face, type: T.unit, equiv: equivalence }]);
  const context = [["b1", Gd(F.bottom)], ["p", T.path("j", Gd(F.endpoint("j", 0)), T.point, T.variable("b1"))]];
  const b = T.at(T.variable("p"), I.variable("i")), over = Gd(F.endpoint("i", 0));
  const glued = T.glue(over, T.unglue(over, b), [{ face: F.endpoint("i", 0), term: T.point }]);
  const composite = T.comp("k", over, [{ face: F.endpoint("m", 0), term: glued }, { face: F.endpoint("m", 1), term: glued }], b);
  assert.equal(program.checker.checkView(composite, over, context, new Map([["i", 0], ["m", 1]])).term.tag, "Comp");
});

// The third review of #73: the glue move waits for enclosing reductions. With
// n0 := 0, n(k) := succ(n(k - 1)) up to n600, G = Glue [] Nat and
// f(A : U0, z : A) := point, f(G, glue_G [] n600) and f(G, glue_G [] y) agree
// by unfolding f. The heuristic first descends into the arguments, whose
// equality it cannot rule out; there, while the unfolding still waits, no
// glue move is made. Compared directly, the two Glue terms differ and the
// move is tried: the Glue step does not apply, and reduces nothing of n600,
// whose normal form is deeper than syntax may be, as the whole term's
// normal form, which the move once took, would.
test("the glue move waits for enclosing reductions, and reduces nothing beyond its side conditions", async t => {
  const { T } = await import("../web/translator/core.mjs");
  const { heuristicPolicy } = await import("../web/cubical-instruction-driver.mjs");
  const numbers = ["import nat;", "def n0 : Nat := 0;", ...Array.from({ length: 600 }, (_, k) => `def n${k + 1} : Nat := succ(n${k});`)];
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check([...numbers, "def f(A : U0, z : A) : Unit := tt;"].join("\n") + "\n", "deep");
  const made = [];
  program.kernel.policy = { name: "recording", rank: point => heuristicPolicy.rank(point),
    observe: (point, move, outcome) => made.push(`${move.move}:${point.depth}:${outcome}`) };
  const G = T.glueType(naturalSort, []), deep = T.glue(G, { tag: "DefRef", name: "deep__n600" }, []);
  const f = { tag: "DefRef", name: "deep__f" }, y = T.glue(G, T.variable("y"), []);
  const left = T.app(T.app(f, G), deep), right = T.app(T.app(f, G), y);
  assert.equal(program.checker.checkView(T.line("i", T.unit, left), T.path("i", T.unit, left, right), [["y", naturalSort]]).term.tag, "PLam");
  assert.ok(!made.some(move => move.startsWith("glue:")), made.join(" "));
  // Compared directly, the two Glue terms differ; the glue move is tried, and
  // is stuck without reaching the depth of syntax.
  let error = null;
  try { program.checker.checkView(T.line("i", G, deep), T.path("i", G, deep, y), [["y", naturalSort]]); }
  catch (thrown) { error = thrown; }
  assert.ok(error && !/syntax depth/.test(error.message), error?.message);
  assert.ok(made.some(move => move.startsWith("glue:") && move.endsWith(":stuck")), made.join(" "));
});

// The fourth review of #73: the glue move took the whole Glue term's normal
// form, the path in its base included. Here that path's right endpoint holds
// a shared graph, t(n + 1) = f(t(n))(t(n)) over x : Unit, with 2^40 paths,
// which the comparison never needs: the normal form ran out of the move's
// budget, and the tube disagreed with its base. The Glue step reduces only
// the piece and b at i = 0, which is point.
test("a Glue term agrees with its base though its path mentions a large shared graph", async t => {
  const { T } = await import("../web/translator/core.mjs");
  const { heuristicPolicy } = await import("../web/cubical-instruction-driver.mjs");
  const { face: F, interval: I } = await import("../web/translator/lattice.mjs");
  const { identityEquivalence } = await import("../web/translator/equivalence.mjs");
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check("import nat;\ndef unit_point : Unit := tt;\n", "glue_graph");
  // The glue moves made, and the kernel steps each took.
  const made = [], work = () => { const w = program.kernel.work(); return w.instructionSteps + w.querySteps; };
  let started = 0;
  program.kernel.policy = { name: "recording",
    *rank(point) { for (const move of heuristicPolicy.rank(point)) { if (move.move === "glue") started = work(); yield move; } },
    observe: (point, move, outcome) => { if (move.move === "glue") made.push([outcome, work() - started]); } };
  const equivalence = identityEquivalence(T.unit);
  const G = face => T.glueType(T.unit, [{ face, type: T.unit, equiv: equivalence }]);
  let graph = T.variable("x");
  for (let n = 0; n < 40; n++) graph = T.app(T.app(T.variable("f"), graph), graph);
  const end = T.glue(T.glueType(T.unit, []), graph, []);
  const context = [["x", T.unit], ["f", T.pi("a", T.unit, T.pi("b", T.unit, T.unit))],
    ["p", T.path("j", G(F.endpoint("j", 0)), T.point, end)]];
  const b = T.at(T.variable("p"), I.variable("i")), over = G(F.endpoint("i", 0));
  const glued = T.glue(over, T.unglue(over, b), [{ face: F.endpoint("i", 0), term: T.point }]);
  const composite = T.comp("k", over, [{ face: F.endpoint("m", 0), term: glued }], b);
  assert.equal(program.checker.checkView(composite, over, context, new Map([["i", 0], ["m", 1]])).term.tag, "Comp");
  assert.ok(made.some(([outcome, steps]) => outcome === "progress" && steps < 10000), JSON.stringify(made));
});

// The fifth review of #73: the Glue step exposes a base that is itself a
// Glue eta redex, as conversion does. With A = Glue [] Nat, A' = Glue []
// ((λ X. X)(Nat)), G = Glue [] A, g : G and u = unglue_G(g), the constant
// tube glue_G [] (glue_A' [] (unglue_A(u))) of a composition over G must
// agree with its base g: the inner Glue term is u once A' is A, and the
// outer Glue term and g have different heads, so congruence cannot reach it.
test("a Glue term whose base is a nested Glue eta redex agrees with its base", async t => {
  const { T } = await import("../web/translator/core.mjs");
  const { face: F } = await import("../web/translator/lattice.mjs");
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check("import nat;\ndef unit_point : Unit := tt;\n", "glue_nested");
  const A = T.glueType(naturalSort, []), redex = T.glueType(T.app(T.lam("X", T.universe(0), T.variable("X")), naturalSort), []);
  const G = T.glueType(A, []), g = T.variable("g");
  const outer = T.glue(G, T.glue(redex, T.unglue(A, T.unglue(G, g)), []), []);
  const composite = T.comp("k", G, [{ face: F.endpoint("m", 0), term: outer }], g);
  assert.equal(program.checker.checkView(composite, G, [["g", G]], new Map([["m", 0]])).term.tag, "Comp");
});

// The sixth review of #73: a Glue term's base may be the other side's unglue
// only by pair eta, and its Glue type the other side's only below its weak
// head, over large shared parts. Glue eta expands the neutral side to
// glue [φ ↦ g] (unglue g), and the two Glue terms are compared part by
// part: the bases by pair eta and beta, the types by one beta step, with
// the shared parts never normalized.
test("a Glue term agrees with its base through pair eta, and through types equal below their heads", async t => {
  const { T } = await import("../web/translator/core.mjs");
  const { face: F } = await import("../web/translator/lattice.mjs");
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check("import nat;\ndef unit_point : Unit := tt;\n", "glue_eta_expansion");
  const tube = (G, term, context) =>
    program.checker.checkView(T.comp("k", G, [{ face: F.endpoint("m", 0), term }], T.variable("g")), G, context, new Map([["m", 0]]));
  // A = Σ (n : Nat). Nat, G = Glue [] A, u = unglue_G(g): glue_G [] (fst u, snd ((λ x. x) u)) is g.
  const A = T.sigma("n", naturalSort, naturalSort), G = T.glueType(A, []), u = T.unglue(G, T.variable("g"));
  const paired = T.glue(G, T.pair(A, T.first(u), T.second(T.app(T.lam("x", A, T.variable("x")), u))), []);
  assert.equal(tube(G, paired, [["g", G]]).term.tag, "Comp");
  // r(n + 1) = f(r(n))(r(n)) over x : Unit, A2 = Path(Unit, r(40), r(40)), and
  // A2' the same over (λ X. X)(Unit): glue_(Glue [] A2') [] (unglue_(Glue [] A2)(g)) is g.
  let r = T.variable("x");
  for (let n = 0; n < 40; n++) r = T.app(T.app(T.variable("f"), r), r);
  const A2 = T.path("j", T.unit, r, r), A2beta = T.path("j", T.app(T.lam("X", T.universe(0), T.variable("X")), T.unit), r, r);
  const G2 = T.glueType(A2, []), G2beta = T.glueType(A2beta, []);
  const retyped = T.glue(G2beta, T.unglue(G2, T.variable("g")), []);
  const context = [["x", T.unit], ["f", T.pi("a", T.unit, T.pi("b", T.unit, T.unit))], ["g", G2]];
  assert.equal(tube(G2, retyped, context).term.tag, "Comp");
});

// Two gaps the differential generator found (tools/differential-driver.mjs),
// with G(d) = Glue [d = 0 ↦ (Unit, id)] Unit and p a path over G from point.
// A Glue term's piece is joined to the base at one type, though the Glue
// type's base is (λ X. X)(Unit) where the equivalence's codomain is Unit. And
// an eta expansion that the glue move contracts is not made again, which had
// looped until the fuel ran out.
test("generated Glue cases: a base type that computes, and no eta and glue loop", async t => {
  const { T } = await import("../web/translator/core.mjs");
  const { face: F, interval: I } = await import("../web/translator/lattice.mjs");
  const { identityEquivalence } = await import("../web/translator/equivalence.mjs");
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check("import nat;\ndef unit_point : Unit := tt;\n", "generated_glue");
  const e = identityEquivalence(T.unit), unitRedex = T.app(T.lam("X", T.universe(0), T.variable("X")), T.unit);
  const G = (base, d) => T.glueType(base, [{ face: F.endpoint(d, 0), type: T.unit, equiv: e }]);
  const context = [["b1", T.glueType(T.unit, [{ face: F.bottom, type: T.unit, equiv: e }])],
    ["p", T.path("j", G(T.unit, "j"), T.point, T.variable("b1"))]];
  const dims = new Map([["i", 0], ["m", 1]]), b = T.at(T.variable("p"), I.variable("i")), over = G(T.unit, "i");
  const glued = (as, base) => T.glue(as, T.unglue(over, base), [{ face: F.endpoint("i", 0), term: T.point }]);
  const id = term => T.app(T.lam("z", over, T.variable("z")), term);
  assert.equal(program.checker.checkView(glued(G(unitRedex, "i"), b), G(unitRedex, "i"), context, dims).term.tag, "GlueTerm");
  const left = id(glued(over, id(b))), right = id(glued(over, glued(over, b)));
  const composite = T.comp("k", over, [{ face: F.endpoint("m", 0), term: left }], right);
  assert.equal(program.checker.checkView(composite, over, context, dims).term.tag, "Comp");
});
