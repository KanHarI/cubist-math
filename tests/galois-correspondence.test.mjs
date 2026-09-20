import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { checkedFoldedView } from "../web/mathscript/kernel-folding.mjs";
import { loadProof } from "../tools/test-selection.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/f4_galois_correspondence.proof");
const subgroup = await loadProof("web/proofs/subgroup_carriers.proof");
const sources = { ...loaded.sources, ...subgroup.sources, subgroup_carriers: subgroup.source };
const source = "import subgroup_carriers;\n" + loaded.source + `
  def inverse_equiv_small(A : U0, B : U0, f : A -> B, g : B -> A,
    eta : (forall x : A, g(f(x)) = x), epsilon : (forall y : B, f(g(y)) = y)) =
    equiv_from_inverse(U0, A, B, f, g, eta, epsilon);
  def inverse_equiv_large(A : U2, B : U2, f : A -> B, g : B -> A,
    eta : (forall x : A, g(f(x)) = x), epsilon : (forall y : B, f(g(y)) = y)) =
    equiv_from_inverse(U2, A, B, f, g, eta, epsilon);
  theorem correspondence_map_computes :
    field_first((DecidableSubgroup(F4GaloisGroup) -> DecidableIntermediateField(F2, F4OverF2)),
      (fun (f : DecidableSubgroup(F4GaloisGroup) -> DecidableIntermediateField(F2, F4OverF2)) =>
        IsEquiv(U1, DecidableSubgroup(F4GaloisGroup), DecidableIntermediateField(F2, F4OverF2), f)),
      f4_galois_correspondence) = f4_decidable_fixed {
    exact refl(f4_decidable_fixed);
  }
  def decision_tag(P : U0, d : Decidable(P)) = match d return Nat { left p => 0; right noP => 1; };
  theorem all_unit_is_decided :
    decision_tag((forall x : Fin(2), Unit), finite_forall_decidable(2, (fun (x : Fin(2)) => Unit),
      (fun (x : Fin(2)) => typed(Decidable(Unit), left(tt))))) = 0 {
    exact refl(0);
  }
  theorem void_is_rejected :
    decision_tag((forall x : Fin(2), Void), finite_forall_decidable(2, (fun (x : Fin(2)) => Void),
      (fun (x : Fin(2)) => typed(Decidable(Void), right(fun (v : Void) => v))))) = 1 {
    exact refl(1);
  }
  theorem empty_search_succeeds :
    decision_tag((forall x : Fin(0), Void), finite_forall_decidable(0, (fun (x : Fin(0)) => Void),
      (fun (x : Fin(0)) => typed(Decidable(Void), absurd(x))))) = 0 {
    exact refl(0);
  }
`;
const c = compile(module, source, sources);
after(() => c.kernel.dispose());
function check(name, axioms) {
  assert.ok(c.kernel.verify(name + "_type", name), name);
  assert.deepEqual(c.kernel.axiomsFor(name).sort(), axioms, name);
}

test("adjointification works for arbitrary types in U0 and U2 without axioms", () => {
  for (const name of ["inverse_equiv_small", "inverse_equiv_large"]) check(name, []);
});

test("finite decisions and subgroup carriers have exact constructive dependencies", () => {
  for (const name of ["decision_transfer", "decision_implies", "finite_forall_decidable", "all_unit_is_decided", "void_is_rejected", "empty_search_succeeds",
    "subgroup_as_group", "subgroup_inclusion", "subgroup_inclusion_injective", "subgroup_factor",
    "f4_fixing_decision"]) check(name, []);
  for (const name of ["f4_fixed_decision", "decision_prop", "subgroup_decisions_prop", "intermediate_decisions_prop",
    "subgroup_factor_triangle", "subgroup_factor_unique"]) check(name, ["lib_funext"]);
});

test("the actual fixed and fixing maps form an order-reversing equivalence without LEM or choice", () => {
  for (const name of ["f4_galois_correspondence", "f4_decidable_fixing_fixed", "f4_decidable_fixed_fixing"])
    check(name, ["lib_funext", "lib_univalence"]);
  check("correspondence_map_computes", ["lib_funext", "lib_univalence"]);
  for (const name of ["f4_decidable_fixed_antitone", "f4_decidable_fixing_antitone"])
    assert.ok(c.kernel.verify(name + "_type", name));
  assert.ok(!c.kernel.bindings.has("LEM"));
  assert.ok(!c.kernel.bindings.has("AOC"));
});

test("correspondence and subgroup factorization retain checked folded kernel types", () => {
  for (const name of ["f4_galois_correspondence", "f4_decidable_fixed_antitone", "subgroup_factor_unique"]) {
    const folded = checkedFoldedView(c, name);
    assert.deepEqual(folded.failures, {}, name);
    assert.ok(folded.verified.type, name);
  }
});

test("an arbitrary subgroup does not supply its own membership decisions", () => {
  assert.throws(() => compile(module, source + `
    def false_decidable(H : Subgroup(F4GaloisGroup)) : DecidableSubgroup(F4GaloisGroup) {
      exact (H, (fun (e : F4Automorphism) => typed(Decidable(subgroup_members(F4GaloisGroup, H, e)), left(tt))));
    }
  `, sources), /Expected|differ/);
});

test("a two-sided inverse still needs the half-adjoint triangle", () => {
  assert.throws(() => compile(module, source + `
    def false_triangle(A : U0, B : U0, f : A -> B, g : B -> A,
      eta : (forall x : A, g(f(x)) = x), epsilon : (forall y : B, f(g(y)) = y)) : Equiv(U0, A, B) {
      exact (f, g, eta, epsilon, (fun (x : A) => refl(epsilon(f(x)))));
    }
  `, sources), /Expected|differ/);
});

test("a homomorphism cannot factor through an arbitrary subgroup without membership", () => {
  assert.throws(() => compile(module, source + `
    def false_subgroup_factor(G : Group, S : Subgroup(G)) : GroupHom(G, subgroup_as_group(G, S)) {
      exact subgroup_factor(G, G, group_hom_identity(G), S, (fun (x : group_carrier(G)) => tt));
    }
  `, sources), /Expected|differ/);
});
