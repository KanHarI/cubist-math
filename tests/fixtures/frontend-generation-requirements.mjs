// Independently authored from the FG0–FG5 acceptance contracts, not generated
// from the case registry. Keep an obligation when a fixture is removed: losing
// both a fixture and its manifest row must still expose the missing behavior.
// `checks` names the contract requirements each witness must keep; the audit
// applies every requirement's counterexamples to an accepted observation, so
// these labels name executable distinctions rather than establish them.
//
// Each witness states the minimum its case must keep, as data: clients,
// refused-client and declaration diagnostics, absent outputs, refusal words
// and observation sites. A fixture may state more. A diagnostic cause outside
// the codes that always carry one must be required here, so that weakening a
// fixture's expectation fails validation and its cause counterexamples come
// from this map rather than from the expectation under test.
const wrongEquation = {refusedClients: {wrong: {code: "E606"}}};
const recursiveResults = {clients: ["base", "computation", "computation2"], ...wrongEquation};
const opposedEquations = {clients: ["intended"], refusedClients: {captured: {code: "E606"}}};
const generatedInterface = {clients: ["identity", "applied", "N.fold"]};

export const obligations = [
  {id: "ownership", phase: "FG1", checks: ["clients", "originalType", "duplicateRefused", "diagnostics"],
    witnesses: {G1: {}, "G1-initial": {}, "G1-reverse": {clients: ["constructor"]}, "G1-same-kind": {}},
    counterexample: "replaced original binding, lost original client or a duplicate refused for another reason"},
  {id: "name-availability", phase: "FG1", checks: ["refusedClients", "diagnostics"],
    witnesses: {
      G1: {refusedClients: {leaked_c: {code: "E343", cause: {untranslated: "c"}}}},
      "G1-initial": {refusedClients: {leaked_one: {code: "E343", cause: {untranslated: "N.one"}},
        leaked_mul: {code: "E343", cause: {untranslated: "N.mul"}}}},
    },
    counterexample: "refusal alongside a resolvable constructor"},
  {id: "atomic-publication", phase: "FG1", checks: ["outputsAbsent"],
    witnesses: {"G1-initial": {absentOutputs: ["N.model", "N.fold_map", "N.fold"]}, G3: {absentOutputFamilies: ["T.Hom", "T.Iso"]}},
    counterexample: "a refused declaration's model/fold or Hom/Iso output is reported"},
  {id: "universe-contribution", phase: "FG3", checks: ["clients", "refusedClients", "diagnostics"],
    witnesses: {G2: {clients: ["preserves", "level", "preserves_u1", "level_u1"],
      refusedClients: {lowered: {code: "E606", cause: {found: "U1", expected: "U0"}}}}},
    counterexample: "generated Hom omits a fixed domain's universe contribution or preservation field, or lowers its universe"},
  {id: "unsupported-transport", phase: "FG2", checks: ["clients", "refusals", "outputsAbsent"],
    witnesses: {G3: {refusalWords: ["op", "p", "l"]}},
    counterexample: "usable base erased, unsupported Hom/Iso family leaked or a refusal without the dependent law"},
  {id: "match-computation", phase: "FG4", checks: ["clients", "refusedClients"],
    witnesses: {G4: {clients: ["computation", "off_computation", "empty_computation"], ...wrongEquation},
      "G4-flat": {clients: ["computation", "empty_computation"], ...wrongEquation}},
    counterexample: "constant result or wrong clause selected"},
  {id: "lint-interface", phase: "FG5", checks: ["advice", "clients"],
    witnesses: {G5: generatedInterface, "G5-single": generatedInterface},
    counterexample: "unsafe edit or suppression limited to grouped binders"},
  {id: "failed-dependency", phase: "FG1", checks: ["diagnostics"], witnesses: {G6: {}},
    counterexample: "wrong dependency identity or re-expanded parent failure"},
  {id: "wildcard-diagnostic", phase: "FG4", checks: ["range", "diagnostics"],
    witnesses: {G8: {diagnostic: {name: "h", code: "E606", cause: {found: "t1 = t1", expected: "t0 = t1"}}}},
    counterexample: "reversed endpoints or unrelated source span"},
  {id: "written-navigation", phase: "FG5", checks: ["links", "clients"], witnesses: {G9: {sites: 4}},
    counterexample: "wrong label, missing site or wrong binder target"},
  {id: "capture-origin", phase: "FG2/FG5", checks: ["range", "diagnostics"],
    witnesses: {G10: {diagnostic: {name: "T", code: "E871", cause: {helper: "k", field: "c"}}}},
    counterexample: "empty or unrelated conflict origin"},
  {id: "helper-meaning", phase: "FG2", checks: ["clients", "refusedClients"],
    witnesses: {G11: opposedEquations, "G11-grouped-dependent": opposedEquations, "G11-inherited": opposedEquations, "G11-initial": opposedEquations},
    counterexample: "captured equation checks instead of the intended equation"},
  {id: "recursive-step", phase: "FG2/FG4", checks: ["clients", "refusedClients"],
    witnesses: {G12: recursiveResults, "G12-inherited": recursiveResults, "G12-initial": recursiveResults},
    counterexample: "constant iter or a successor returning op(c) instead of using its recursive result; distinguished at depth two"},
  {id: "lexical-shadowing", phase: "FG2/FG4", checks: ["clients", "refusedClients"], witnesses: {"G12-shadowed": opposedEquations},
    counterexample: "local iter resolved as the earlier recursive field"},
  {id: "type-unfolding-origin", phase: "FG5", checks: ["range", "diagnostics"],
    witnesses: {"G12-range": {diagnostic: {name: "T", code: "E845", cause: {recursive: "iter", context: "field type"}}}},
    counterexample: "unfolding accepted or its refusal loses the responsible reference"},
];
