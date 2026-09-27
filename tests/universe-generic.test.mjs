import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { parse } from "../web/mathscript/parser.mjs";
import { T, substituteTerm } from "../lib/cubical/core.mjs";
import { canonicalHasher } from "../tools/proof-migration.mjs";

// L1.1 (G0 §4.3): universe binders U < UU0, universe constants of every tier,
// next and max, generic builtins and assumptions, and generic rewriting.
// Source cases carry the IDs of the G0 specification's section 5.
const module = await createCubical();
const readArchive = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
async function check(t, source, name = "generic") {
  const program = new CubicalProgram(module, readArchive);
  t.after(() => program.dispose());
  const result = await program.check(source, name);
  const verdicts = Object.fromEntries(result.outputs.map(output => [output.name, output.verified ? true : output.reason]));
  return { program, result, verdicts };
}
const parseError = source => { try { parse(source); return null; } catch (error) { return error.message; } };
const labels = (program, binding) => program.symbols[binding].axioms.map(id => program.checker.assumptionLabels.get(id)).sort();

test("a generic definition checks once and is instantiated at universes of tier 0", async t => {
  const { program, verdicts } = await check(t, `
    def identity(U < UU0, A : U, x : A) : A := x;
    def three := identity(U0, Nat, 3);
    def nat_again : U0 := identity(U1, U0, Nat);
    def Endo := forall U < UU0. U -> U;
    def pairing(U, V < UU0, A : U, B : V) : U0 := Nat;
    def mixed(U < UU0) : next(U) := U;
    def bigger(U, V < UU0) : next(max(U, V)) := max(U, V);
    def generic_lambda : forall U < UU0. U -> U := fun (U < UU0, A : U) => A;
    def at_variable(V < UU0, B : V, b : B) : B := identity(V, B, b);
    def at_successor(V < UU0) : V := identity(next(V), V, Nat);
  `);
  assert.ok(Object.values(verdicts).every(verdict => verdict === true), JSON.stringify(verdicts));
  assert.equal(program.inspect("generic__identity").type.tag, "LPi");
  assert.equal(program.checker.verify(T.app(T.levelApply({ tag: "DefRef", name: "generic__identity" }, 0), T.nat)).type.tag, "Pi");
  assert.deepEqual(program.checker.verify({ tag: "DefRef", name: "generic__three" }).normal, T.succ(T.succ(T.succ(T.zero))));
});

test("B11–B14, B16, B17: Universe is removed, and bounds, reserved names and universes are checked", async t => {
  const removed = "Universe was removed: bind a universe variable as U < UU0.";
  const bound = /A universe variable's bound must be UU0, as in U < UU0/;
  const { verdicts } = await check(t, `
    def u := Universe;
    def f(U : Universe, A : U) := A;
    def f1(U < UU1, A : U) := A;
    def f2(U < U5, A : U) := A;
    def f3(U < UUU0, A : U) := A;
    def malformed := U01;
    def g(UU : U1, x : UU) := x;
    def h := UU;
    def not_a_universe(U < UU0) := next(Nat);
    def identity(U < UU0, A : U, x : A) := x;
    def bad_identity := identity(Nat, Nat, 0);
    def numeral_bound := forall n < 3. n = n;
  `);
  assert.equal(verdicts.u, removed);                              // B11
  assert.equal(verdicts.f, removed);
  for (const name of ["f1", "f2", "f3"]) assert.match(verdicts[name], bound); // B12
  assert.match(verdicts.malformed, /Malformed universe constant: U01/); // B13
  assert.equal(verdicts.g, true);                                 // B14
  assert.match(verdicts.h, /Untranslated name: UU/);
  const universe = /Expected a universe: U0, UU0, a universe variable, next\(E\) or max\(E, F\)/;
  assert.match(verdicts.not_a_universe, universe);                // B16
  assert.match(verdicts.bad_identity, universe);
  assert.match(verdicts.numeral_bound, bound);                    // B17
  // B13: universe constants are reserved names.
  assert.equal(parseError("def UU2 := Nat;"), "UU2 is a universe constant; choose another name.");
  assert.equal(parseError("def f := fun (U1 : U0) => U1;"), "U1 is a universe constant; choose another name.");
  assert.match(parseError("def f := exists U < UU0. U;"), /exists has no level form/);
});

test("B15: universes of both tiers are terms, and cumulativity crosses tiers", async t => {
  const { verdicts } = await check(t, "def v : UU1 := UU0; def w : UU0 := U7; def x : UU3 := UU1;");
  assert.deepEqual(verdicts, { v: true, w: true, x: true });
  const { verdicts: wrong } = await check(t, "def down : U7 := UU0; def same : UU0 := UU0;");
  assert.match(wrong.down, /Type mismatch/);
  assert.match(wrong.same, /Type mismatch/);
});

test("S12, D4 and Q10: instantiation, assumptions and builtins take universes below UU0", async t => {
  const { verdicts } = await check(t, `import paths;
    def identity(U < UU0, A : U, x : A) := x;
    def S12(T : UU0, x : T) := identity(UU0, T, x);
    def D4(T : UU0, nn : (T -> Void) -> Void) := LEM(UU0, T, nn);
    def D4_small(T : U1, nn : (T -> Void) -> Void) := LEM(U1, T, nn);
    def Q10(A, B : UU0) := ua(UU0, A, B);
    def Q10_small(A, B : U1, e : Equiv(U1, A, B)) := ua(U1, A, B, e);
    def funext(A : UU0, f, g : A -> A, h : forall a : A. f(a) = g(a)) := FunExt(UU0, A, (fun (a : A) => A), f, g, h);
  `);
  assert.match(verdicts.S12, /A universe argument must lie below UU0/);
  assert.match(verdicts.D4, /LEM holds only for universes below UU0/);
  assert.equal(verdicts.D4_small, true);
  assert.match(verdicts.Q10, /ua takes a universe below UU0/);
  assert.equal(verdicts.Q10_small, true);
  assert.match(verdicts.funext, /FunExt takes a universe below UU0/);
});

test("a generic statement cannot use its universe as an element of a fixed universe", async t => {
  const { verdicts } = await check(t, `
    def fixed(U < UU0, f : U2 -> Nat) : Nat := f(U);
    def member(U < UU0) : U := U;
    def downward(U < UU0, A : next(U)) : U := A;
  `);
  assert.match(verdicts.fixed, /Type mismatch: found next\(U\), expected U2/);
  assert.match(verdicts.member, /Type mismatch: found next\(U\), expected U/);
  assert.match(verdicts.downward, /Type mismatch/);
});

test("proofs under universe binders introduce, reverse and transport like concrete ones", async t => {
  const { result, verdicts } = await check(t, `
    def endo_id : forall U < UU0. forall A : U. A -> A { intro U; intro A; intro a; exact a; }
    def reflexive(U < UU0, A : U, x : A) : x = x { rfl; }
    def reverse(U < UU0, A : U, x, y : A, p : x = y) : y = x { exact sym(p); }
    def congruence(U < UU0, A, B : U, f : A -> B, x, y : A, p : x = y) : f(x) = f(y) { exact cong(f, p); }
    def moved(U < UU0, A : U, C : A -> U, x, y : A, p : x = y, c : C(x)) : C(y) { exact along C by p from c; }
  `);
  assert.ok(Object.values(verdicts).every(verdict => verdict === true), JSON.stringify(verdicts));
  // Goal displays, which the browser worker sends with every check, show a
  // universe variable by its bound.
  const goal = result.steps.find(step => step.declaration === "endo_id" && step.locals.length === 3);
  assert.deepEqual(goal.locals[0], { name: "U", type: "UU0", relation: "<" });
  assert.equal(goal.locals[1].relation, ":");
});

test("D6: a generic assumption is named once, whatever universes it is used at", async t => {
  const { program, verdicts } = await check(t, `
    def both(nn0 : (Nat -> Void) -> Void, nn1 : (U0 -> Void) -> Void) : Truncate(U0, Nat) and Truncate(U1, U0) :=
      (LEM(U0, Nat, nn0), LEM(U1, U0, nn1));
  `);
  assert.equal(verdicts.both, true);
  assert.deepEqual(labels(program, "generic__both"), ["LEM", "Truncate"]);
  assert.ok(program.checker.assumptions.has("__assumption_LEM"));
  assert.equal([...program.checker.assumptions.keys()].some(name => /_U\d+$/.test(name)), false);
});

test("univalence is one generic definition, used at U0 and U1", async t => {
  const { program, verdicts } = await check(t, `import paths;
    def small(A, B : U0, e : Equiv(U0, A, B)) : A = B := ua(U0, A, B, e);
    def large(A, B : U1, e : Equiv(U1, A, B)) : A = B := ua(U1, A, B, e);
  `);
  assert.deepEqual(verdicts, { small: true, large: true });
  const builtins = [...program.kernel.definitions.keys()].filter(name => name.startsWith("builtin__ua"));
  assert.deepEqual(builtins, ["builtin__ua"]);
  assert.deepEqual(program.symbols.generic__large.axioms, []);
});

test("rewriting matches a generic rule's universe only where it is a bare variable", async t => {
  const { verdicts } = await check(t, `import primes;
    def Id(U < UU0, A : U) := A;
    def id_unfold(U < UU0, A : U) : Id(U, A) = A := refl(A);
    def void_id(U < UU0) : Id(U, Void) = Void := refl(typed(U, Void));
    def plus_zero(U < UU0, n : Nat) : n + 0 = n := nat_add_zero(n);
    def zero_at(U < UU0, f : U -> Nat, A : U, h : f(A) = 0) : f(A) = 0 := h;
    def next_rule(U < UU0, A : next(U)) : Id(next(U), A) = A := refl(A);
    simp_set identities := [id_unfold];
    def by_rw : Id(U2, Void) = Void { rw [void_id]; }
    def by_rw_twice : Id(U1, Id(U1, Void)) = Void { rw [void_id]; rw [void_id]; }
    def by_simp(A : U0) : Id(U0, Id(U0, A)) = A { simp only [id_unfold]; }
    def by_set(A : U3) : Id(U3, A) = A { simp only [identities]; }
    def level_free(n : Nat) : (n + 0) + 0 = n { simp only [plus_zero]; }
    def from_parameter(g : U1 -> Nat, h : g(U0) = 0) : g(U0) + 0 = 0 { simp only [zero_at, nat_add_zero] with [h]; }
    def not_bare(A : U3) : Id(U3, A) = A { simp only [next_rule]; }
    def explicit(A : U3) : Id(U3, A) = A { simp only [next_rule(U2)]; }
    def undetermined : Void = Id(U3, Void) { rw [<- void_id]; }
  `);
  for (const name of ["by_rw", "by_rw_twice", "by_simp", "by_set", "level_free", "from_parameter", "explicit"])
    assert.equal(verdicts[name], true, `${name}: ${verdicts[name]}`);
  assert.match(verdicts.not_bare, /matched only where its universe is a bare variable; supply its universe argument/);
  assert.match(verdicts.undetermined, /universe is not determined by the matched side; supply it/);
});

test("inspection names universe variables by their source names", async t => {
  const { program } = await check(t, `
    def identity(U < UU0, A : U, x : A) : A := x;
    def lifted(V < UU0) := identity(next(V), V);
  `);
  const view = program.inspect("generic__identity");
  assert.equal(view.typeText, "Π (U < ω), Π (A : U), (A → A)");
  assert.deepEqual(view.statement.parameters.map(p => [p.name[0].text, p.relation, p.type.map(part => part.text).join("")]),
    [["U", "<", "UU0"], ["A", ":", "U"], ["x", ":", "A"]]);
  assert.equal(program.inspect("generic__lifted").expressionText, "λ (V < ω). identity(next(V), V)");
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
      case 0: return { term: T.nat, level: 0 };
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
      case 0: { let n = T.zero; for (let i = random(3); i > 0; i--) n = T.succ(n); return n; }
      case 1: { const n = name("n"); return T.app(T.lam(n, T.nat, T.succ(T.variable(n))), number(depth - 1)); }
      default: {
        const a = type(depth - 1), m = max(a.level, level()), A = name("C"), n = name("k");
        return T.app(T.app(T.lam(A, T.universe(m), T.lam(n, T.nat, T.variable(n))), a.term), number(depth - 1));
      }
    }
  };
  // A type with the level variable free, and a closed inhabitant of it.
  const inhabited = depth => {
    switch (depth ? random(4) : random(2)) {
      case 0: return { type: T.nat, value: T.succ(T.zero) };
      case 1: return { type: T.universe(level()), value: T.nat };
      case 2: { const a = inhabited(depth - 1), b = inhabited(depth - 1), n = name("a"); return { type: T.pi(n, a.type, b.type), value: T.lam(n, a.type, b.value) }; }
      default: { const l = level(), A = name("D"); return { type: T.pi(A, T.universe(l), T.universe(l)), value: T.lam(A, T.universe(l), T.variable(A)) }; }
    }
  };
  return { x, type, number, inhabited };
}

test("Lemma 5: instantiating a level commutes with normalization", async t => {
  const program = new CubicalProgram(module, async () => ""); t.after(() => program.dispose());
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
