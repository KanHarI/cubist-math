import test from "node:test";
import { replaceSyntax } from "./source-edit.mjs";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/group_univalence.proof");
const assumptions = ["lib_funext", "lib_univalence"];

function checked(source, sources = loaded.sources) {
  const c = compile(module, source, sources);
  for (const output of c.outputs)
    assert.ok(c.kernel.verify(output.proposition, output.binding), output.name);
  return c;
}

test("group structure identity is a full equivalence with both canonical inverse laws", () => {
  const c = checked(loaded.source);
  try {
    for (const name of ["group_structure_identity", "group_isomorphism_is_equality", "group_isotoid_idtoiso", "group_idtoiso_isotoid", "group_isomorphism_paths_injective"]) {
      const output = c.outputs.find(o => o.name === name);
      assert.ok(output, name);
      assert.deepEqual(c.kernel.axiomsFor(output.binding).sort(), assumptions);
    }
    assert.match(loaded.source.replace(/\s+/g, " "), /Equiv\(U1, \(G = H\), GroupIso\(G, H\)\)/);
    assert.match(c.outputs.find(o => o.name === "group_isomorphism_is_equality").type,
      /GroupIso\(G, H\).*?=\[U1\].*?G =\[Group\] H/);
    assert.match(loaded.sources.groups.replace(/\s+/g, " "), /def Group = exists A : U0, GroupStructure\(A\)/);
    assert.match(loaded.sources.groups.replace(/\s+/g, " "), /def GroupStructure\(A : U0\) = exists unit : A, exists multiply : A -> A -> A, GroupLaws\(A, unit, multiply\)/);
    // No local postulate can substitute for the structure identity argument.
    for (const id of ["group_identity", "group_isomorphisms", "group_total_identity", "identity_systems"])
      assert.doesNotMatch(loaded.sources[id], /\baxiom\s|\bpostulate\s*\(/);
  } finally { c.kernel.dispose(); }
});

test("group identity identifies full records over genuinely different singleton carriers", () => {
  const source = `${loaded.source}
    def singleton_group_laws(A : U0, point : A, contracts : (forall x : A, point = x)) :
      GroupLaws(A, point, (fun (x : A) => fun (y : A) => point)) {
      exact (proposition_is_set(A, (fun (x : A) => fun (y : A) => trans(sym(contracts(x)), contracts(y)))),
        ((fun (x : A) => fun (y : A) => fun (z : A) => refl(point)),
          (contracts, (contracts, (fun (x : A) => typed((exists y : A, (point = point) and (point = point)), (point, (refl(point), refl(point)))))))));
    }
    def UnitGroup = group_object(Unit, tt, (fun (x : Unit) => fun (y : Unit) => tt), singleton_group_laws(Unit, tt, unit_equal));
    def PairUnit = Unit and Unit;
    def pairUnit = typed(PairUnit, (tt, tt));
    def pair_unit_contract(p : PairUnit) =
      pair_induction((fun (p : PairUnit) => pairUnit = p),
        (fun (x : Unit) => fun (y : Unit) => product_path(Unit, Unit, tt, x, unit_equal(x), tt, y, unit_equal(y))), p);
    def PairUnitGroup = group_object(PairUnit, pairUnit, (fun (x : PairUnit) => fun (y : PairUnit) => pairUnit), singleton_group_laws(PairUnit, pairUnit, pair_unit_contract));
    def singleton_iso = typed(GroupIso(UnitGroup, PairUnitGroup),
      ((fun (x : Unit) => pairUnit), ((fun (x : PairUnit) => tt),
        (unit_equal, (pair_unit_contract, (fun (x : Unit) => fun (y : Unit) => refl(pairUnit)))))));
    def singleton_group_equality : UnitGroup = PairUnitGroup { exact group_isotoid(UnitGroup, PairUnitGroup, singleton_iso); }
    theorem singleton_iso_round_trip : group_idtoiso(UnitGroup, PairUnitGroup, singleton_group_equality) = singleton_iso {
      exact group_idtoiso_isotoid(UnitGroup, PairUnitGroup, singleton_iso);
    }
  `;
  const c = checked(source);
  try {
    assert.deepEqual(c.kernel.axiomsFor("singleton_group_equality").sort(), assumptions);
    assert.deepEqual(c.kernel.axiomsFor("singleton_iso_round_trip").sort(), assumptions);
  } finally { c.kernel.dispose(); }
});

test("group identity cannot replace multiplication preservation by an arbitrary reflexivity proof", () => {
  const original = loaded.sources.group_total_identity;
  const mutated = replaceSyntax(original, "trans(preserves(x, y),", "trans(refl(f(multiplyA(x, y))),");
  assert.notEqual(mutated, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, group_total_identity: mutated }), /Expected|differ|equality|type/i);
});

test("the identity-system proof does not assert every group isomorphism is identity", () => {
  const mutated = replaceSyntax(loaded.source,
    "exact identity_system_section(Group, G, group_identity_family(G), group_identity_iso(G), group_total_contraction(G), H, iso);",
    "exact refl(iso);",
  );
  assert.notEqual(mutated, loaded.source);
  assert.throws(() => compile(module, mutated, loaded.sources), /Expected|differ|equality|type/i);
});

test("the existing circle winding isomorphism becomes equality of complete groups and round-trips", async () => {
  const circle = await loadProof("web/proofs/circle_group_identity.proof");
  const c = checked(circle.source, circle.sources);
  try {
    for (const name of ["circle_group_isomorphism", "circle_loop_group_equals_integers", "circle_group_identification_recovers_winding"])
      assert.deepEqual(c.kernel.axiomsFor(name).sort(), assumptions);
  } finally { c.kernel.dispose(); }
});

test("the basic group interface is axiom-free and separates laws from bundles", async () => {
  const basic = await loadProof("web/proofs/groups.proof");
  const c = checked(`${basic.source}
    theorem idtoiso_refl(G : Group) : group_idtoiso(G, G, refl(G)) = group_identity_iso(G) {
      exact refl(group_identity_iso(G));
    }
  `, basic.sources);
  try {
    for (const name of ["GroupLaws", "Group", "GroupIso", "group_object_eta", "group_idtoiso", "idtoiso_refl"])
      assert.deepEqual(c.kernel.axiomsFor(name), [], name);
    assert.equal(c.outputs.find(o => o.name === "Group").type, "U1");
    assert.ok(!c.kernel.bindings.has("GroupType"));
    assert.ok(!c.kernel.bindings.has("group_isotoid"));
  } finally { c.kernel.dispose(); }
  const laws = await loadProof("web/proofs/group_identity.proof");
  const d = checked(laws.source, laws.sources);
  try {
    assert.deepEqual(d.kernel.axiomsFor("group_inverse_unique"), []);
    assert.deepEqual(d.kernel.axiomsFor("group_laws_prop"), ["lib_funext"]);
  } finally { d.kernel.dispose(); }
});
