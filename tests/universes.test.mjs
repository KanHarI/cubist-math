import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";

const module = await createKernel();
const sources = { paths: await readFile(new URL("../web/proofs/paths.proof", import.meta.url), "utf8") };
const identityEquivalence = `
  def identity_equiv(U : Universe, A : U) : Equiv(U, A, A) {
    exact ((fun (x : A) => x), ((fun (x : A) => x),
      ((fun (x : A) => refl(x)), ((fun (x : A) => refl(x)), (fun (x : A) => refl(refl(x)))))));
  }
`;
function checked(source) {
  const c = compile(module, source, sources);
  for (const o of c.outputs) assert.ok(c.kernel.verify(o.proposition, o.binding), o.name);
  return c;
}

test("universe parameters specialize one equivalence definition at every supported level", () => {
  const c = checked(`import paths; ${identityEquivalence}
    def small = identity_equiv(U0, Nat);
    def large = identity_equiv(U1, U0);
    def larger = identity_equiv(U2, U1);
    def largest = identity_equiv(U3, U2);
    def identity(U : Universe, A : U, x : A) = x;
    def computes = identity(U2, U1, U0);
    theorem reflexive(U : Universe, A : U, x : A) : x =[A] x { exact refl(x); }
  `);
  try {
    assert.ok(c.kernel.steps.some(s => s.op === "UVble"));
    assert.equal(c.axiomCount, 0);
    assert.equal(c.outputs.find(o => o.name === "computes").type, "U1");
    assert.ok(!c.kernel.bindings.has("HigherEquiv"));
    assert.ok(!c.kernel.bindings.has("HigherIsEquiv"));
  } finally { c.kernel.dispose(); }
  for (const bad of [
    `def id(U : Universe, A : U, x : A) = x; def bad = id(Nat, 0, 0);`,
    `def id(U : Universe, A : U, x : A) = x; def bad = id(U0, U0, Nat);`,
    `def bad : Universe { exact Nat; }`,
    `def bad(A : U0, x : A) = x =[Nat] x;`,
    `def bad = U1 =[U1] U1;`,
  ]) assert.throws(() => compile(module, bad, sources), /Expected|universe|type/i);
});

test("explicit equality retains its requested carrier in checked and folded terms", () => {
  const c = checked(`def lifted = U0 =[U2] U0;
    theorem reflexive : U0 =[U2] U0 { exact refl(typed(U2, U0)); }`);
  try {
    const binding = c.kernel.bindings.get("lifted");
    const id = c.kernel.module._wb_view(c.kernel.handle, 0, binding.id, 0);
    const eq = c.kernel.node(id);
    assert.equal(eq.kind, "Eq");
    const carrier = c.kernel.node(eq.children[0]);
    assert.equal(carrier.kind, "U");
    assert.equal(carrier.parameter, 2);
    const folded = checkedFoldedView(c, "lifted");
    assert.ok(folded.verified.expression);
  } finally { c.kernel.dispose(); }
});

test("generic equivalences work with univalence and higher-universe computation", () => {
  const c = checked(`import prelude; import paths; ${identityEquivalence}
    def identify(U : Universe, A : U) = ua(U)(A, A, identity_equiv(U, A));
    def compute(A : U3, x : A) = UnivalenceBeta(U3)(A, A, identity_equiv(U3, A), x);
    def Two = Unit or Unit;
    def swap(x : Two) = match x return Two { left a => right(a); right b => left(b); };
    def swap_twice(x : Two) = match x as z return (swap(swap(z)) = z) {
      left a => refl(typed(Two, left(a))); right b => refl(typed(Two, right(b)));
    };
    def swapping : Equiv(U1, Two, Two) {
      exact (swap, (swap, (swap_twice, (swap_twice,
        (fun (x : Two) => match x as z return
          (ap(U1, Two, Two, swap, swap(swap(z)), z, swap_twice(z)) = swap_twice(swap(z))) {
            left a => refl(refl(typed(Two, right(a))));
            right b => refl(refl(typed(Two, left(b))));
          })))));
    }
    theorem transport_swaps :
      transport((fun (T : U1) => T), Two, Two, ua(U1)(Two, Two, swapping), typed(Two, left(tt))) = typed(Two, right(tt)) {
      exact UnivalenceBeta(U1)(Two, Two, swapping, typed(Two, left(tt)));
    }
  `);
  try {
    assert.deepEqual(c.kernel.axiomsFor("identify"), ["lib_univalence"]);
    assert.deepEqual(c.kernel.axiomsFor("transport_swaps").sort(), ["lib_univalence"]);
    assert.ok(!c.kernel.bindings.has("AOC"));
    assert.ok(!c.kernel.bindings.has("LEM"));
  } finally { c.kernel.dispose(); }
});

test("Choice is universe-indexed, first-class, set-restricted and still truncated", () => {
  const statement = `import prelude;
    def SetAt(U : Universe, A : U) = forall x : A, forall y : A, forall p : x = y, forall q : x = y, p = q;
    def choose(U : Universe, A : U, B : A -> U, base : SetAt(U, A),
      fibers : (forall x : A, SetAt(U, B(x))), inhabited : (forall x : A, Truncate(U, B(x)))) :
      Truncate(U, (forall x : A, B(x))) {
      exact Choice(U)(A, B, base, fibers, inhabited);
    }
    def large_choice = choose(U1);
    def larger_choice = Choice(U2);
  `;
  const c = checked(statement);
  try {
    for (const name of ["choose", "large_choice", "larger_choice"])
      assert.deepEqual(c.kernel.axiomsFor(name).sort(), ["AOC", "lib_Trunc"]);
    assert.ok(c.links.some(l => l.name === "Choice" && l.binding === "AOC"));
    assert.ok(!c.kernel.bindings.has("LEM"));
  } finally { c.kernel.dispose(); }
  for (const args of ["A, B, tt, fibers, inhabited", "A, B, base, tt, inhabited", "A, B, base, fibers, tt"])
    assert.throws(() => compile(module, statement.replace("A, B, base, fibers, inhabited", args), sources), /Expected/);
  assert.throws(() => compile(module, statement.replace("Truncate(U, (forall x : A, B(x))) {", "(forall x : A, B(x)) {"), sources), /Expected/);
  assert.throws(() => compile(module, `import prelude; def bad = Choice(Nat);`, sources), /Expected a universe/);
  assert.throws(() => compile(module, `import prelude; def bad = set_choice(U0);`, sources), /Unknown name/);
});

test("generic truncation and function extensionality remain independent of choice and LEM", () => {
  const c = checked(`import prelude;
    def mere(U : Universe, A : U) = Truncate(U)(A);
    def introduce(U : Universe, A : U, x : A) = TruncateIntro(U)(A, x);
    def proposition(U : Universe, A : U) = TruncateProp(U)(A);
    def eliminate(U : Universe, A : U, P : U, prop : (forall x : P, forall y : P, x = y), f : A -> P) = TruncateElim(U)(A, P, prop, f);
    def extensionality(U : Universe, A : U, B : A -> U, f : (forall x : A, B(x))) =
      FunExt(U)(A, B, f, f, (fun (x : A) => refl(f(x))));
  `);
  try {
    assert.ok(!c.kernel.bindings.has("AOC"));
    assert.ok(!c.kernel.bindings.has("LEM"));
    assert.deepEqual(c.kernel.axiomsFor("extensionality"), ["lib_funext"]);
  } finally { c.kernel.dispose(); }
});

test("LEM specializes excluded middle at an explicit universe", () => {
  const c = checked(`import prelude;
    def double_negation(U : Universe, A : U, nn : (A -> Void) -> Void) : Truncate(U, A) {
      exact LEM(U)(A, nn);
    }
    def large_lem = LEM(U1);
  `);
  try {
    for (const name of ["double_negation", "large_lem"])
      assert.deepEqual(c.kernel.axiomsFor(name).sort(), ["LEM", "lib_Trunc"]);
    assert.ok(c.links.some(l => l.name === "LEM" && l.binding === "LEM"));
    assert.ok(!c.kernel.bindings.has("AOC"));
  } finally { c.kernel.dispose(); }
  assert.throws(() => compile(module, `import prelude; def bad = LEM(Nat);`, sources), /Expected a universe/);
});

test("standard univalence is IsEquiv(idtoequiv); ua and both laws are derived", () => {
  const c = checked(`import prelude; import paths; ${identityEquivalence}
    theorem canonical(A : U0, B : U0) :
      IsEquiv(U1, (A =[U0] B), Equiv(U0, A, B), idtoequiv(U0, A, B)) {
      exact Univalence(U0, A, B);
    }
    theorem higher(A : U2, B : U2) :
      IsEquiv(U3, (A =[U2] B), Equiv(U2, A, B), idtoequiv(U2, A, B)) {
      exact Univalence(U2, A, B);
    }
    def generic_axiom(U : Universe, A : U, B : U) = Univalence(U, A, B);
    def generic_beta(U : Universe, A : U, x : A) = UnivalenceBeta(U, A, A, identity_equiv(U, A), x);
    theorem eta(A : U0, B : U0, p : A =[U0] B) :
      ua(U0, A, B, idtoequiv(U0, A, B, p)) = p {
      exact UnivalenceEta(U0, A, B, p);
    }
    theorem canonical_reflexivity(A : U0) :
      idtoequiv(U0, A, A, refl(A)) = identity_equiv(U0, A) {
      exact refl(identity_equiv(U0, A));
    }
  `);
  try {
    for (const name of ["canonical", "higher", "generic_axiom", "generic_beta", "eta"])
      assert.deepEqual(c.kernel.axiomsFor(name), ["lib_univalence"], name);
    assert.deepEqual(c.kernel.axiomsFor("canonical_reflexivity"), []);
    for (const name of ["lib_ua", "lib_ua_elim", "lib_ua_unique"])
      assert.notEqual(c.kernel.steps.find(s => s.name === name).op, "Axiom", name);
    assert.equal(c.kernel.steps.find(s => s.name === "lib_univalence").op, "Axiom");
    const f = checkedFoldedView(c, "canonical");
    assert.ok(f.verified.type, JSON.stringify(f.failures));
  } finally { c.kernel.dispose(); }
});

test("based induction has independent carrier and motive universes and computes at reflexivity", () => {
  const c = checked(`import paths;
    def induction_at(U : Universe, V : Universe) = based_induction(U, V);
    def higher_carrier = induction_at(U2, U0);
    def higher_motive = induction_at(U0, U2);
    theorem computes_at_refl : based_induction(U2, U0, U1, U0,
      (fun (b : U1) => fun (p : U0 = b) => Unit), tt, U0, refl(U0)) = tt {
      exact refl(tt);
    }
    theorem computes_large_motive : based_induction(U0, U2, Unit, tt,
      (fun (b : Unit) => fun (p : tt = b) => typed(U2, Unit)), tt, tt, refl(tt)) = tt {
      exact refl(tt);
    }
  `);
  try { for (const o of c.outputs) assert.deepEqual(c.kernel.axiomsFor(o.binding), []); }
  finally { c.kernel.dispose(); }
});

test("inverse data into a set supplies equivalence coherence at every universe without axioms", () => {
  const c = checked(`import paths;
    def SetAt(U : Universe, A : U) = forall x : A, forall y : A,
      forall p : x = y, forall q : x = y, p = q;
    def set_identity(U : Universe, A : U, setA : SetAt(U, A)) : Equiv(U, A, A) {
      exact equiv_from_inverse_into_set(U, A, A, setA,
        (fun (x : A) => x), (fun (x : A) => x),
        (fun (x : A) => refl(x)), (fun (x : A) => refl(x)));
    }
    def at_small = set_identity(U0);
    def at_large = set_identity(U2);
  `);
  try { for (const o of c.outputs) assert.deepEqual(c.kernel.axiomsFor(o.binding), []); }
  finally { c.kernel.dispose(); }
  assert.throws(() => checked(`import paths;
    def invalid(U : Universe, A : U, B : U, f : A -> B, g : B -> A,
      setB : (forall x : B, forall y : B, forall p : x = y, forall q : x = y, p = q)) : Equiv(U, A, B) {
      exact equiv_from_inverse_into_set(U, A, B, setB, f, g,
        (fun (x : A) => refl(x)), (fun (y : B) => refl(y)));
    }
  `), /Expected|differ|equality|type/i);
});
