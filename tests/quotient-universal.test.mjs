import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

const module = await createCubical();
const readSource = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const create = t => {
  const program = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => program.dispose());
  return program;
};

test("homomorphism universe schemas check at U0–U3 and agree with small homomorphisms", async t => {
  const program = create(t);
  const schemas = ["GroupHomLawsAt", "GroupHomAt", "group_hom_map_at", "group_hom_multiply_at",
    "group_is_set_at", "group_hom_laws_prop_at", "group_hom_ext_at",
    "group_hom_identity_at", "group_hom_compose_at", "group_hom_object_at"];
  const specializations = [0, 1, 2, 3].flatMap(level => schemas.map(name => `def check_${name}_${level} = ${name}(U${level});`));
  const result = await program.check(`import group_homomorphisms;
    ${specializations.join("\n")}
    def small_hom_specialization(G : Group, H : Group) : GroupHomAt(U0, G, H) =[U0] GroupHom(G, H) {
      exact refl(GroupHom(G, H));
    }
    def identity_computes(G : GroupAt(U2), x : group_carrier_at(U2, G)) :
      group_hom_map_at(U2, G, G, group_hom_identity_at(U2, G), x) = x { exact refl(x); }
  `, "hom_universe_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const symbol of result.outputs) {
    assert.equal(symbol.verified, true, symbol.name);
    assert.deepEqual(symbol.axioms, [], symbol.name);
  }
});

test("quotient universal property works for genuinely U1 targets without representative choice", async t => {
  const program = create(t);
  const result = await program.check(`import quotient_group_universal;
    def projection_descends_to_identity(G : Group, S : Subgroup(G), normal : IsNormal(G, S)) :
      quotient_descend_hom(G, QuotientGroup(G, S, normal), quotient_projection(G, S, normal), S, normal,
        quotient_projection_kills(G, S, normal)) = group_hom_identity_at(U1, QuotientGroup(G, S, normal)) {
      let Q := QuotientGroup(G, S, normal);
      let projection := quotient_projection(G, S, normal);
      let descended := quotient_descend_hom(G, Q, projection, S, normal, quotient_projection_kills(G, S, normal));
      let identity := group_hom_identity_at(U1, Q);
      have right : group_hom_compose_at(U1, group_lift(G), Q, Q, projection, identity) = projection {
        exact group_hom_ext_at(U1, group_lift(G), Q, group_hom_compose_at(U1, group_lift(G), Q, Q, projection, identity), projection,
          (fun (x : group_carrier(G)) => refl(left_coset(G, S, x))));
      }
      exact quotient_projection_epimorphism(G, Q, S, normal, descended, identity,
        trans(quotient_descend_triangle(G, Q, projection, S, normal, quotient_projection_kills(G, S, normal)), sym(right)));
    }
  `, "quotient_universal_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const binding of ["quotient_group_universal__quotient_group_universal", "quotient_group_universal__quotient_projection_epimorphism", "quotient_universal_regression__projection_descends_to_identity"]) {
    const symbol = program.symbols[binding];
    assert.equal(symbol.verified, true, binding);
    const assumptions = symbol.axioms.map(name => program.checker.assumptionLabels.get(name) ?? name).sort();
    t.diagnostic(`${symbol.name}: ${JSON.stringify(assumptions)}`);
    assert.ok(assumptions.length > 0);
    assert.ok(assumptions.every(name => /^Truncate(?:Intro|Elim|Prop)?\(U[01]\)$/.test(name)), JSON.stringify(assumptions));
  }
});

test("factorization cannot omit the subgroup-killing hypothesis", async t => {
  const program = create(t);
  const result = await program.check(`import quotient_group_universal;
    def unjustified_factor(G : Group, H : GroupAt(U1), h : GroupHomAt(U1, group_lift(G), H), S : Subgroup(G), normal : IsNormal(G, S)) : GroupHomAt(U1, QuotientGroup(G, S, normal), H) {
      exact quotient_descend_hom(G, H, h, S, normal);
    }
  `, "bad_factorization");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 1);
  assert.equal(result.outputs[0].verified, false);
  assert.ok(result.gaps.every(gap => gap.module === "bad_factorization"), JSON.stringify(result.gaps));
});
