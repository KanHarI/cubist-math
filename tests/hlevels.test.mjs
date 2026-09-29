import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// The h-levels of library/hlevels.cubist (work-plan L2.5a): the levels are
// one definition by recursion on Nat, so each named level is that
// definition at a numeral, by conversion; the lemmas hold in every universe
// below UU0; and none proves more than it states.
async function check(t, source) {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(`import hlevels;\n${source}`, "main");
  return name => {
    const found = result.outputs.find(output => output.name === name);
    assert.ok(found, `no declaration ${name}`);
    return found;
  };
}
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};

test("each named level is the recursive definition at a numeral, by conversion", async t => {
  const get = await check(t, `
def level_zero(U < UU0, A : U) : HasLevel(U, 0, A) = IsProp(U, A) := refl(IsProp(U, A));
def set_unfolds(U < UU0, A : U) : IsSet(U, A) = (forall x, y : A. forall p, q : x = y. p = q) := refl(IsSet(U, A));
def level_two(U < UU0, A : U) : HasLevel(U, 2, A) = (forall x, y : A. IsSet(U, x = y)) := refl(HasLevel(U, 2, A));
`);
  for (const name of ["level_zero", "set_unfolds", "level_two"]) ok(get(name));
});

test("the lemmas hold in a universe above U0", async t => {
  const get = await check(t, `
def prop_set_in_u1(A : U1, h : IsProp(U1, A)) : IsSet(U1, A) := prop_is_set(U1, A, h);
def every_level_in_u1(n : Nat, A : U1, h : IsProp(U1, A)) : HasLevel(U1, n, A) := prop_has_level(U1, n, A, h);
def functions_into_u0_props(A : U1, B : A -> U1, h : forall x : A. IsProp(U1, B(x))) : IsProp(U1, forall x : A. B(x)) :=
  pi_is_prop(U1, A, B, h);
`);
  for (const name of ["prop_set_in_u1", "every_level_in_u1", "functions_into_u0_props"]) ok(get(name));
});

test("retracts and function types keep every level", async t => {
  const get = await check(t, `
def retract_of_prop(A, B : U0, s : B -> A, r : A -> B, e : forall b : B. r(s(b)) = b, h : IsProp(U0, A)) :
  IsProp(U0, B) := retract_has_level(U0, 0, A, B, s, r, e, h);
def retract_of_groupoid(A, B : U1, s : B -> A, r : A -> B, e : forall b : B. r(s(b)) = b, h : HasLevel(U1, 2, A)) :
  HasLevel(U1, 2, B) := retract_has_level(U1, 2, A, B, s, r, e, h);
def functions_into_sets(A : U0, B : A -> U0, h : forall x : A. IsSet(U0, B(x))) : IsSet(U0, forall x : A. B(x)) :=
  pi_has_level(U0, 1, A, B, h);
def functions_into_groupoids(A : U0, B : A -> U0, h : forall x : A. HasLevel(U0, 2, B(x))) :
  HasLevel(U0, 2, forall x : A. B(x)) := pi_has_level(U0, 2, A, B, h);
`);
  for (const name of ["retract_of_prop", "retract_of_groupoid", "functions_into_sets", "functions_into_groupoids"]) ok(get(name));
});

test("pairs, products and subtypes keep every level, and being contractible is a proposition", async t => {
  const get = await check(t, `
def pairs_of_sets(A : U0, B : A -> U0, hA : IsSet(U0, A), hB : forall a : A. IsSet(U0, B(a))) :
  IsSet(U0, exists a : A. B(a)) := sigma_has_level(U0, 1, A, B, hA, hB);
def pairs_of_groupoids(A : U1, B : A -> U1, hA : HasLevel(U1, 2, A), hB : forall a : A. HasLevel(U1, 2, B(a))) :
  HasLevel(U1, 2, exists a : A. B(a)) := sigma_has_level(U1, 2, A, B, hA, hB);
def product_of_props(A, B : U0, hA : IsProp(U0, A), hB : IsProp(U0, B)) : IsProp(U0, A and B) :=
  product_has_level(U0, 0, A, B, hA, hB);
def subset_of_nat(P : Nat -> U0, hP : forall n : Nat. IsProp(U0, P(n))) : IsSet(U0, exists n : Nat. P(n)) :=
  subtype_has_level(U0, 1, Nat, P, nat_is_set, hP);
def contractible_is_prop(A : U1) : IsProp(U1, IsContr(U1, A)) := is_contr_is_prop(U1, A);
`);
  for (const name of ["pairs_of_sets", "pairs_of_groupoids", "product_of_props", "subset_of_nat", "contractible_is_prop"])
    ok(get(name));
});

// The first review of #87: contractible types are closed under the same
// constructions, keeping their centers, not only as propositions.
test("contractible types are closed under retracts, functions, pairs, products and paths", async t => {
  const get = await check(t, `
def retract_contractible(A, B : U0, s : B -> A, r : A -> B, e : forall b : B. r(s(b)) = b, c : IsContr(U0, A)) :
  IsContr(U0, B) := retract_is_contr(U0, A, B, s, r, e, c);
def functions_into_contractible(A : U0, B : A -> U0, h : forall x : A. IsContr(U0, B(x))) :
  IsContr(U0, forall x : A. B(x)) := pi_is_contr(U0, A, B, h);
def pairs_contractible(A : U1, B : A -> U1, hA : IsContr(U1, A), hB : forall a : A. IsContr(U1, B(a))) :
  IsContr(U1, exists a : A. B(a)) := sigma_is_contr(U1, A, B, hA, hB);
def product_contractible(A, B : U0, hA : IsContr(U0, A), hB : IsContr(U0, B)) : IsContr(U0, A and B) :=
  product_is_contr(U0, A, B, hA, hB);
def paths_contractible(A : U0, c : IsContr(U0, A), x, y : A) : IsContr(U0, x = y) := path_is_contr(U0, A, c, x, y);
`);
  for (const name of ["retract_contractible", "functions_into_contractible", "pairs_contractible",
    "product_contractible", "paths_contractible"]) ok(get(name));
});

// Hedberg's theorem, and the HoTT roadmap's D completion: with Nat a set,
// parallel paths of numbers are equal, but 0 = 1 stays unproved.
test("a type with decidable equality is a set, and Nat is one", async t => {
  const get = await check(t, `
def decided_set(A : U1, decide : forall x, y : A. (x = y) or ((x = y) -> Void)) : IsSet(U1, A) := hedberg(U1, A, decide);
def parallel_nat_paths(p, q : 0 = 0) : p = q := nat_is_set(0, 0, p, q);
def zero_is_one : 0 = 1 := nat_is_set(0, 1);
`);
  for (const name of ["decided_set", "parallel_nat_paths"]) ok(get(name));
  refused(get("zero_is_one"), /mismatch/i);
});

// The HoTT roadmap's D1: a set's evidence never equates arbitrary elements,
// and a proposition's never invents an element.
test("no lemma proves more than it states", async t => {
  const get = await check(t, `
def set_equates_elements(U < UU0, A : U, s : IsSet(U, A), x, y : A) : x = y := s(x, y);
def set_is_prop(U < UU0, A : U, s : IsSet(U, A)) : IsProp(U, A) := s;
def prop_has_center(U < UU0, A : U, h : IsProp(U, A)) : IsContr(U, A) := h;
def retract_backwards(A, B : U0, s : B -> A, r : A -> B, e : forall a : A. s(r(a)) = a, h : IsProp(U0, A)) :
  IsProp(U0, B) := retract_has_level(U0, 0, A, B, s, r, e, h);
`);
  for (const name of ["set_equates_elements", "set_is_prop", "prop_has_center", "retract_backwards"])
    refused(get(name), /mismatch/i);
});
