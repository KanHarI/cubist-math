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

// The HoTT roadmap's D1: a set's evidence never equates arbitrary elements,
// and a proposition's never invents an element.
test("no lemma proves more than it states", async t => {
  const get = await check(t, `
def set_equates_elements(U < UU0, A : U, s : IsSet(U, A), x, y : A) : x = y := s(x, y);
def set_is_prop(U < UU0, A : U, s : IsSet(U, A)) : IsProp(U, A) := s;
def prop_has_center(U < UU0, A : U, h : IsProp(U, A)) : IsContr(U, A) := h;
`);
  for (const name of ["set_equates_elements", "set_is_prop", "prop_has_center"]) refused(get(name), /mismatch/i);
});
