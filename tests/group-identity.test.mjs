import test from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { loadProof } from "../tools/test-selection.mjs";

const module = await createKernel();
const loaded = await loadProof("web/proofs/group_univalence.proof");
const assumptions = ["lib_funext", "lib_ua_elim", "lib_univalence"];

function checked(source, sources = loaded.sources) {
  const c = compile(module, source, sources);
  for (const output of c.outputs)
    assert.ok(c.kernel.verify(output.proposition, output.binding), output.name);
  return c;
}

test("group structure identity is a full equivalence with both canonical inverse laws", () => {
  const c = checked(loaded.source);
  try {
    for (const name of ["group_structure_identity", "group_identity_encode_decode", "group_identity_decode_encode", "group_isomorphism_paths_injective"]) {
      const output = c.outputs.find(o => o.name === name);
      assert.ok(output, name);
      assert.deepEqual(c.kernel.axiomsFor(output.binding).sort(), assumptions);
    }
    assert.match(loaded.source, /HigherEquiv\(\(G = H\), GroupIso\(G, H\)\)/);
    assert.match(loaded.sources.group_identity, /def GroupType = exists A : Type, GroupOperations\(A\)/);
    assert.match(loaded.sources.group_identity, /def GroupOperations\(A : Type\) = exists unit : A, exists multiply : A -> A -> A, Group\(A, unit, multiply\)/);
    // No local postulate can substitute for the structure identity argument.
    for (const id of ["group_identity", "group_isomorphisms", "group_total_identity", "identity_systems"])
      assert.doesNotMatch(loaded.sources[id], /\baxiom\s|\bpostulate\s*\(/);
  } finally { c.kernel.dispose(); }
});

test("group identity identifies full records over genuinely different singleton carriers", () => {
  const source = `${loaded.source}
    def singleton_group_laws(A : Type, point : A, contracts : (forall x : A, point = x)) :
      Group(A, point, (fun (x : A) => fun (y : A) => point)) {
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
    def singleton_group_equality : UnitGroup = PairUnitGroup { exact group_identity_encode(UnitGroup, PairUnitGroup, singleton_iso); }
    theorem singleton_iso_round_trip : group_equality_iso(UnitGroup, PairUnitGroup, singleton_group_equality) = singleton_iso {
      exact group_identity_decode_encode(UnitGroup, PairUnitGroup, singleton_iso);
    }
  `;
  const c = checked(source);
  try {
    assert.deepEqual(c.kernel.axiomsFor("singleton_group_equality").sort(), assumptions);
    assert.deepEqual(c.kernel.axiomsFor("singleton_iso_round_trip").sort(), assumptions);
  } finally { c.kernel.dispose(); }
});

test("group identity cannot replace multiplication preservation by an arbitrary reflexivity proof", () => {
  const original = loaded.sources.group_identity;
  const mutated = original.replace("trans(preserves(x, y),", "trans(refl(f(multiplyA(x, y))),");
  assert.notEqual(mutated, original);
  assert.throws(() => compile(module, loaded.source, { ...loaded.sources, group_identity: mutated }), /Expected|differ|equality|type/i);
});

test("the identity-system proof does not assert every group isomorphism is identity", () => {
  const mutated = loaded.source.replace(
    "exact identity_system_section(GroupType, G, group_identity_family(G), group_identity_iso(G), group_total_contraction(G), H, iso);",
    "exact refl(iso);",
  );
  assert.notEqual(mutated, loaded.source);
  assert.throws(() => compile(module, mutated, loaded.sources), /Expected|differ|equality|type/i);
});

test("the existing circle winding isomorphism becomes equality of complete groups and round-trips", async () => {
  const circle = await loadProof("web/proofs/circle_group_identity.proof");
  const c = checked(circle.source, circle.sources);
  try {
    for (const name of ["circle_loop_group_equals_integers", "circle_group_identification_recovers_winding"])
      assert.deepEqual(c.kernel.axiomsFor(name).sort(), assumptions);
  } finally { c.kernel.dispose(); }
});
