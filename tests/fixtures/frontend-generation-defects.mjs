// Explicit observations of the documented baseline defects, not desired output.
// Only the expected-failure lifecycle reads these records: cases, contracts and
// their audit never do, so removing a fixed case's entry activates it without
// any other edit. A changed diagnostic, client verdict or link must be
// investigated, not rerecorded. RC0 deletes this module with the lifecycle.
export const knownDefects = {
  "G1": {
    "dependencies": [],
    "rootCauses": [["original", {"found": "U0", "expected": "Unit"}]],
    "gaps": ["original E606"],
    "clients": {"original": "refused", "independent": "checked", "leaked_c": "checked"},
    "originalType": "U0",
    "duplicateRefused": false,
    "forbiddenOutputs": []
  },
  "G2": {
    "dependencies": [["T.Hom", ["T.Hom.compose", "T.Hom.id", "T.Hom.make", "T.Hom.map", "T.Hom.map_op", "T.Iso", "T.Iso.make", "identity", "identity_u1", "level", "level_u1", "lowered", "preserves", "preserves_u1"]], ["T.Hom.compose", ["computation", "computation_u1"]], ["T.Iso", ["T.Iso.compose", "T.Iso.from", "T.Iso.from_to", "T.Iso.id", "T.Iso.inverse", "T.Iso.to", "T.Iso.to_from", "iso", "iso_u1"]]],
    "rootCauses": [["T.Hom", {"found": "max(U, max(V, U1))", "expected": "max(U, V)"}]],
    "gaps": [
      "T.Hom E606",
      "T.Hom.compose E340",
      "T.Hom.id E340",
      "T.Hom.make E340",
      "T.Hom.map E340",
      "T.Hom.map_op E340",
      "T.Iso E340",
      "T.Iso.compose E340",
      "T.Iso.from E340",
      "T.Iso.from_to E340",
      "T.Iso.id E340",
      "T.Iso.inverse E340",
      "T.Iso.make E340",
      "T.Iso.to E340",
      "T.Iso.to_from E340",
      "computation E340",
      "computation_u1 E340",
      "identity E340",
      "identity_u1 E340",
      "iso E340",
      "iso_u1 E340",
      "level E340",
      "level_u1 E340",
      "lowered E340",
      "preserves E340",
      "preserves_u1 E340"
    ],
    "clients": {
      "T.Hom": "refused",
      "identity": "refused",
      "computation": "refused",
      "iso": "refused",
      "preserves": "refused",
      "level": "refused",
      "identity_u1": "refused",
      "computation_u1": "refused",
      "iso_u1": "refused",
      "preserves_u1": "refused",
      "level_u1": "refused",
      "lowered": "refused"
    }
  },
  "G3": {
    "dependencies": [["T.Hom", ["T.Hom.compose", "T.Hom.id", "T.Hom.make", "T.Hom.map", "T.Hom.map_c", "T.Hom.map_op", "T.Iso", "T.Iso.make"]], ["T.Hom.id", ["unsupported"]], ["T.Iso", ["T.Iso.compose", "T.Iso.from", "T.Iso.from_to", "T.Iso.id", "T.Iso.inverse", "T.Iso.to", "T.Iso.to_from"]]],
    "rootCauses": [["T.Hom", {"found": "A.l = A.l", "expected": "B.l = B.l"}]],
    "gaps": [
      "T.Hom E606",
      "T.Hom.compose E340",
      "T.Hom.id E340",
      "T.Hom.make E340",
      "T.Hom.map E340",
      "T.Hom.map_c E340",
      "T.Hom.map_op E340",
      "T.Iso E340",
      "T.Iso.compose E340",
      "T.Iso.from E340",
      "T.Iso.from_to E340",
      "T.Iso.id E340",
      "T.Iso.inverse E340",
      "T.Iso.make E340",
      "T.Iso.to E340",
      "T.Iso.to_from E340",
      "unsupported E340"
    ],
    "clients": {"T": "checked", "T.make": "checked", "T.op": "checked", "usable": "checked", "unsupported": "refused"},
    "forbiddenOutputs": [
      "T.Hom",
      "T.Hom.compose",
      "T.Hom.id",
      "T.Hom.make",
      "T.Hom.map",
      "T.Hom.map_c",
      "T.Hom.map_op",
      "T.Iso",
      "T.Iso.compose",
      "T.Iso.from",
      "T.Iso.from_to",
      "T.Iso.id",
      "T.Iso.inverse",
      "T.Iso.make",
      "T.Iso.to",
      "T.Iso.to_from"
    ],
    "refusals": [{"name": "unsupported", "code": "E340", "words": [false, false, false], "unsupported": true}]
  },
  "G4": {
    "dependencies": [["T.value", ["computation", "empty_computation", "off_computation", "wrong"]]],
    "rootCauses": [["T.value", {"obligation": "Bit.squash", "requirement": "m.M must be of h-level 1"}]],
    "gaps": ["T.value E546", "computation E340", "empty_computation E340", "off_computation E340", "wrong E340"],
    "clients": {"T.value": "refused", "computation": "refused", "wrong": "refused", "empty_computation": "refused", "off_computation": "refused"},
    "generation": [["T.value", "Bit.squash"]]
  },
  "G5": {
    "dependencies": [],
    "rootCauses": [["identity", {"reason": "T's models have no homomorphisms: its op's result mentions a carrier on both sides of an arrow, and such homomorphisms need not compose."}], ["N", {"reason": "op uses an arrow type: the equational strategy requires named operation arguments, as in succ(x : M) : M."}]],
    "advice": [{"code": "W706", "declaration": "T", "message": "x is unused in the body: take it out of the group and write M -> … for it."}, {"code": "W706", "declaration": "T", "message": "y is unused in the body: take it out of the group and write M -> … for it."}],
    "gaps": ["N E864", "identity E817"],
    "clients": {"identity": "refused", "applied": "checked", "N": "refused", "N.model": "missing", "N.fold": "missing"}
  },
  "G6": {
    "dependencies": [],
    "rootCauses": [["C", {"untranslated": "Undefined"}], ["P", {"untranslated": "Undefined"}]],
    "gaps": ["C E343", "P E343"],
    "clients": {"independent": "checked"},
    "childNamesParent": false,
    "childRepeatsCause": true
  },
  "G8": {
    "dependencies": [],
    "rootCauses": [["h", {"obligation": "seg", "requirement": "T must be a proposition"}]],
    "gaps": ["h E546"],
    "clients": {},
    "generation": [["h", "seg"]],
    "endpoints": [false, false],
    "range": {"nonempty": true, "withinScope": true, "coversToken": false}
  },
  "G9": {
    "dependencies": [],
    "rootCauses": [],
    "gaps": [],
    "clients": {"meaning": "checked"},
    "links": [[["c", null]], [["c1", null]], [["c1", null]], [["c1", null]]]
  },
  "G10": {
    "dependencies": [],
    "rootCauses": [["T", {"helper": "k", "field": "c"}]],
    "gaps": ["T E871"],
    "clients": {},
    "range": {"nonempty": false, "withinConflict": false, "coversConflict": false}
  },
  "G11": {
    "dependencies": [],
    "rootCauses": [["intended", {"found": "S.op(x, S.c) = S.op(x, S.c)", "expected": "T.kk{{U0}}(S, x) = S.op(x, S.c)"}]],
    "gaps": ["intended E606"],
    "clients": {"intended": "refused", "captured": "checked"}
  },
  "G12": {
    "dependencies": [["T", ["base", "computation", "computation2", "wrong"]]],
    "rootCauses": [["T", {"recursive": "iter", "context": "field type"}]],
    "gaps": ["T E845", "base E340", "computation E340", "computation2 E340", "wrong E340"],
    "clients": {"T.iter": "missing", "T.twice": "missing", "computation": "refused", "computation2": "refused", "wrong": "refused", "base": "refused"}
  },
  "G12-range": {
    "dependencies": [],
    "rootCauses": [["T", {"recursive": "iter", "context": "field type"}]],
    "gaps": ["T E845"],
    "clients": {},
    "range": {"nonempty": false, "withinScope": true, "coversToken": false}
  },
  "G1-initial": {
    "dependencies": [],
    "rootCauses": [["original", {"found": "U0", "expected": "Unit"}]],
    "gaps": ["original E606"],
    "clients": {"original": "refused", "independent": "checked", "leaked_one": "checked", "leaked_mul": "checked"},
    "originalType": "U0",
    "duplicateRefused": false,
    "forbiddenOutputs": ["N.fold", "N.fold_map", "N.model"]
  },
  "G1-reverse": {
    "dependencies": [],
    "rootCauses": [["constructor", {"reason": "Instruction kernel: Expected U, found Unit."}], ["original", {"found": "Unit", "expected": "U0"}]],
    "gaps": ["constructor E604", "original E606"],
    "clients": {"original": "refused", "constructor": "refused", "independent": "checked"},
    "originalType": "Unit",
    "duplicateRefused": false,
    "forbiddenOutputs": []
  },
  "G1-same-kind": {
    "dependencies": [["N", ["original"]]],
    "rootCauses": [["N", {"reason": "Instruction kernel: Definition symbol is already registered."}]],
    "gaps": ["N E604", "original E340"],
    "clients": {"original": "refused", "independent": "checked"},
    "originalType": null,
    "duplicateRefused": true,
    "forbiddenOutputs": []
  },
  "G4-flat": {
    "dependencies": [["T.value", ["computation", "empty_computation", "wrong"]]],
    "rootCauses": [["T.value", {"obligation": "Bits.squash", "requirement": "m.M must be of h-level 1"}]],
    "gaps": ["T.value E546", "computation E340", "empty_computation E340", "wrong E340"],
    "clients": {"T.value": "refused", "computation": "refused", "wrong": "refused", "empty_computation": "refused"},
    "generation": [["T.value", "Bits.squash"]]
  },
  "G5-single": {
    "dependencies": [],
    "rootCauses": [["identity", {"reason": "T's models have no homomorphisms: its op's result mentions a carrier on both sides of an arrow, and such homomorphisms need not compose."}], ["N", {"reason": "op uses an arrow type: the equational strategy requires named operation arguments, as in succ(x : M) : M."}]],
    "advice": [{"code": "W705", "declaration": "T", "message": "x is unused in the body: write M -> … instead of forall x : M. …."}],
    "gaps": ["N E864", "identity E817"],
    "clients": {"identity": "refused", "applied": "checked", "N": "refused", "N.model": "missing", "N.fold": "missing"}
  },
  "G11-grouped-dependent": {
    "dependencies": [],
    "rootCauses": [["intended", {"found": "S.op(x, S.c) = S.op(x, S.c)", "expected": "T.kk{{U0}}(S, x, x, refl(x)) = S.op(x, S.c)"}]],
    "gaps": ["intended E606"],
    "clients": {"intended": "refused", "captured": "checked"}
  },
  "G11-inherited": {
    "dependencies": [],
    "rootCauses": [["intended", {"found": "S.op(x, S.c) = S.op(x, S.c)", "expected": "Child.kk{{U0}}(S, x) = S.op(x, S.c)"}]],
    "gaps": ["intended E606"],
    "clients": {"intended": "refused", "captured": "checked"}
  },
  "G11-initial": {
    "dependencies": [],
    "rootCauses": [["intended", {"found": "N.op(x, N.c) = N.op(x, N.c)", "expected": "T.kk{{U0}}(N.model, x) = N.op(x, N.c)"}]],
    "gaps": ["intended E606"],
    "clients": {"intended": "refused", "captured": "checked"}
  },
  "G12-inherited": {
    "dependencies": [["Child", ["base", "computation", "computation2", "wrong"]]],
    "rootCauses": [["Child", {"reason": "T is not a theory here: Child extends theories in scope."}], ["T", {"recursive": "iter", "context": "field type"}]],
    "gaps": ["Child E805", "T E845", "base E340", "computation E340", "computation2 E340", "wrong E340"],
    "clients": {"Child.iter": "missing", "Child.twice": "missing", "computation": "refused", "computation2": "refused", "wrong": "refused", "base": "refused"}
  },
  "G12-initial": {
    "dependencies": [["N", ["base", "computation", "computation2", "wrong"]], ["T", ["N"]]],
    "rootCauses": [["T", {"recursive": "iter", "context": "field type"}]],
    "gaps": ["N E340", "T E845", "base E340", "computation E340", "computation2 E340", "wrong E340"],
    "clients": {"N": "refused", "N.model": "missing", "computation": "refused", "computation2": "refused", "wrong": "refused", "base": "refused"}
  },
  "G12-shadowed": {
    "dependencies": [["T", ["captured", "intended"]]],
    "rootCauses": [["T", {"recursive": "iter", "context": "field type"}]],
    "gaps": ["T E845", "captured E340", "intended E340"],
    "clients": {"intended": "refused", "captured": "refused"}
  }
};
