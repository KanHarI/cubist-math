import "./fresh-build.mjs";
import {naturalSort, numeral} from "../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { T, substituteTerm } from "../web/translator/core.mjs";
import { canonicalHasher } from "../tools/canonical-hash.mjs";
import { testModule } from "./check-program.mjs";

// L1.1 (G0 §4.3): universe binders U < UU0, universe constants of every tier,
// next and max, generic builtins and assumptions, and generic rewriting.
// Source cases carry the IDs of the G0 specification's section 5.
const module = await createCubical();
// The cases are cubist-tests/universe_generic*.cubist, whose comments state
// each refusal and what each print shows (tests/cubist-tests.test.mjs); here,
// what neither shows.
const generic = testModule("universe_generic", { module }), builtins = testModule("universe_generic_builtins", { module });
const parseError = source => { try { parse(source); return null; } catch (error) { return error.message; } };
const labels = (program, binding) => program.symbols[binding].axioms.map(id => program.checker.assumptionLabels.get(id)).sort();

test("B13: universe constants are reserved names", () => {
  assert.equal(parseError("def UU2 := Nat;"), "UU2 is a universe constant; pick another name.");
  assert.equal(parseError("def f := fun (U1 : U0) => U1;"), "U1 is a universe constant; pick another name.");
  assert.match(parseError("def f := exists U < UU0. U;"), /exists has no level form/);
});

// Goal displays, which the browser worker sends with every check, show a
// universe variable by its bound.
test("a goal under a universe binder shows the variable by its bound", async () => {
  const { result } = await generic();
  const goal = result.steps.find(step => step.declaration === "endo_id" && step.locals.length === 3);
  assert.deepEqual(goal.locals[0], { name: "U", type: "UU0", relation: "<" });
  assert.equal(goal.locals[1].relation, ":");
});
test("D6: a generic assumption is named once, whatever universes it is used at", async () => {
  const { program } = await generic();
  assert.deepEqual(labels(program, "universe_generic__both"), ["LEM", "Truncate"]);
  assert.ok(program.checker.assumptions.has("__assumption_LEM"));
  assert.equal([...program.checker.assumptions.keys()].some(name => /_U\d+$/.test(name)), false);
});
test("univalence is one generic definition, used at U0 and U1", async () => {
  const { program } = await builtins();
  const definitions = [...program.kernel.definitions.keys()].filter(name => name.startsWith("builtin__ua"));
  assert.deepEqual(definitions, ["builtin__ua"]);
  assert.deepEqual(program.symbols.universe_generic_builtins__large.axioms, []);
});
test("inspection names universe variables by their source names", async () => {
  const { program } = await generic();
  const view = program.inspect("universe_generic__identity");
  assert.equal(view.typeText, "Π (U < ω), Π (A : U), (A → A)");
  assert.deepEqual(view.statement.parameters.map(p => [p.name[0].text, p.relation, p.type.map(part => part.text).join("")]),
    [["U", "<", "UU0"], ["A", ":", "U"], ["x", ":", "A"]]);
});
// Seeded, so a failure reproduces.
function generator(seed) {
  const random = n => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed % n; };
  const x = { tag: "Var", name: "generic_x" };
  const levels = [x, 0, 2, { tag: "LSucc", count: 1, level: x }, { tag: "LMax", left: x, right: 1 }];
  const level = () => levels[random(levels.length)];
  const max = (a, b) => typeof a === "number" && typeof b === "number" ? Math.max(a, b) : { tag: "LMax", left: a, right: b };
  const succ = a => typeof a === "number" ? a + 1 : { tag: "LSucc", count: 1, level: a };
  let names = 0;
  const name = stem => `${stem}_${++names}`;
  // A type with the level variable free, and a level it lives at.
  const type = depth => {
    switch (depth ? random(5) : random(2)) {
      case 0: return { term: naturalSort, level: 0 };
      case 1: { const l = level(); return { term: T.universe(l), level: succ(l) }; }
      case 2: { const a = type(depth - 1), b = type(depth - 1); return { term: T.pi(name("p"), a.term, b.term), level: max(a.level, b.level) }; }
      case 3: { // (λ (A : U(m)). A → A)(a)
        const a = type(depth - 1), m = max(a.level, level()), A = name("A");
        return { term: T.app(T.lam(A, T.universe(m), T.pi(name("q"), T.variable(A), T.variable(A))), a.term), level: m };
      }
      default: { // (λ (y < ω). λ (A : U(y)). A){m}(a)
        const a = type(depth - 1), m = max(a.level, level()), y = name("y"), A = name("B");
        return { term: T.app(T.levelApply(T.levelLambda(y, T.lam(A, T.universe(T.variable(y)), T.variable(A))), m), a.term), level: m };
      }
    }
  };
  // A natural number, canonical data whatever the level.
  const number = depth => {
    switch (depth ? random(3) : 0) {
      case 0: return numeral(random(3));
      case 1: { const n = name("n"); return T.app(T.lam(n, naturalSort, T.app(T.constructor(1,naturalSort,"succ"),T.variable(n))), number(depth - 1)); }
      default: {
        const a = type(depth - 1), m = max(a.level, level()), A = name("C"), n = name("k");
        return T.app(T.app(T.lam(A, T.universe(m), T.lam(n, naturalSort, T.variable(n))), a.term), number(depth - 1));
      }
    }
  };
  // A type with the level variable free, and a closed inhabitant of it.
  const inhabited = depth => {
    switch (depth ? random(4) : random(2)) {
      case 0: return { type: naturalSort, value: numeral(1) };
      case 1: return { type: T.universe(level()), value: naturalSort };
      case 2: { const a = inhabited(depth - 1), b = inhabited(depth - 1), n = name("a"); return { type: T.pi(n, a.type, b.type), value: T.lam(n, a.type, b.value) }; }
      default: { const l = level(), A = name("D"); return { type: T.pi(A, T.universe(l), T.universe(l)), value: T.lam(A, T.universe(l), T.variable(A)) }; }
    }
  };
  return { x, type, number, inhabited };
}

test("Lemma 5: instantiating a level commutes with normalization", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  await program.check("def retained : Unit := tt;", "properties");
  const nf = term => program.checker.verify(term).normal, hash = canonicalHasher();
  const same = (a, b) => hash(a) === hash(b);
  const { x, type, number } = generator(12345);
  let levelDependent = 0;
  for (let i = 0; i < 40; i++) {
    const data = i % 2 === 1;
    const generic = T.levelLambda(x.name, data ? number(3) : type(3).term);
    const normal = nf(generic);
    if (!same(nf(T.levelApply(generic, 0)), nf(T.levelApply(generic, 1)))) levelDependent++;
    for (const n of [0, 1, 3]) {
      const instantiated = nf(T.levelApply(generic, n));
      assert.ok(same(instantiated, nf(T.levelApply(normal, n))), `term ${i} at ${n}`);
      // Canonical data does not mention the level: nf(t)[x := n] is nf(t).
      if (data) assert.ok(same(instantiated, normal.body), `data ${i} at ${n}`);
    }
  }
  assert.ok(levelDependent > 0, "the generated types must depend on their level");
});

test("composition at a level Π is pointwise: its reduct instantiated is the composition at the instance", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
  await program.check("def retained : Unit := tt;", "properties");
  const nf = term => program.checker.verify(term).normal, hash = canonicalHasher();
  const { x, inhabited } = generator(777);
  for (let i = 0; i < 30; i++) {
    const { type, value } = inhabited(3), dim = `i_${i}`;
    const generic = T.levelLambda(x.name, value);
    const transport = T.comp(dim, T.levelPi(x.name, type), [], generic);
    for (const n of [0, 2]) {
      const pointwise = T.comp(dim, substituteTerm(type, x.name, n), [], T.levelApply(generic, n));
      assert.equal(hash(nf(T.levelApply(transport, n))), hash(nf(pointwise)), `family ${i} at ${n}`);
    }
  }
});
