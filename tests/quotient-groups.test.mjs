import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";

const module = await createCubical();
const readSource = name => readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");

test("quotient groups and the first isomorphism theorem check constructively across universes", async t => {
  const program = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(`import group_first_isomorphism;
    def lift_again(G : GroupAt(U1)) : GroupAt(U2) {
      exact group_object_at(U2, group_carrier_at(U1, G), group_unit_at(U1, G),
        group_multiply_at(U1, G), group_laws_at(U1, G));
    }
    def identity_quotient(G : Group) : GroupIsoAt(U1,
      KernelQuotientGroup(G, G, group_hom_identity(G)),
      group_lift(ImageGroup(G, G, group_hom_identity(G)))) {
      exact group_first_isomorphism(G, G, group_hom_identity(G));
    }
    def trivial_quotient(G : Group, H : Group) : GroupIsoAt(U1,
      KernelQuotientGroup(G, H, group_hom_trivial(G, H)),
      group_lift(ImageGroup(G, H, group_hom_trivial(G, H)))) {
      exact group_first_isomorphism(G, H, group_hom_trivial(G, H));
    }`, "quotient_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const binding of ["quotient_sets__quotient_is_set", "quotient_groups__QuotientGroup", "group_first_isomorphism__group_first_isomorphism"]) {
    const symbol = program.symbols[binding];
    assert.equal(symbol.verified, true, binding);
    const assumptions = symbol.axioms.map(name => program.checker.assumptionLabels.get(name) ?? name).sort();
    t.diagnostic(`${symbol.name}: ${JSON.stringify(assumptions)}`);
    assert.ok(assumptions.length > 0, "quotient construction must disclose truncation");
    assert.ok(assumptions.every(name => /Truncate|truncate|truncation/i.test(name)), JSON.stringify(assumptions));
  }
});

test("quotient construction rejects omitted normality and silent universe lowering", async t => {
  const program = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(`import quotient_groups;
    def missing_normal(G : Group, S : Subgroup(G)) : GroupAt(U1) {
      exact QuotientGroup(G, S);
    }
    def resize_quotient(G : Group, S : Subgroup(G), normal : IsNormal(G, S)) : Group {
      exact QuotientGroup(G, S, normal);
    }`, "invalid_quotient");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(d => !d.verified && !d.template));
  assert.ok(result.gaps.every(g => g.module === "invalid_quotient"), JSON.stringify(result.gaps));
});
