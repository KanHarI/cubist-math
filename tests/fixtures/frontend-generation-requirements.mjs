// Independently authored from the FG0–FG5 acceptance contracts, not generated
// from the case registry. Keep an obligation when a fixture is removed: losing
// both a fixture and its manifest row must still expose the missing behavior.
// `checks` names the contract requirements each witness must keep; the audit
// applies every requirement's counterexamples to an accepted observation, so
// these labels name executable distinctions rather than establish them.
export const obligations = [
  {id: "ownership", phase: "FG1", cases: ["G1", "G1-initial", "G1-reverse", "G1-same-kind"],
    checks: ["clients", "originalType", "duplicateRefused", "diagnostics"],
    counterexample: "replaced original binding, lost original client or a duplicate refused for another reason"},
  {id: "name-availability", phase: "FG1", cases: ["G1", "G1-initial"], checks: ["refusedClients", "diagnostics"],
    counterexample: "refusal alongside a resolvable constructor"},
  {id: "atomic-publication", phase: "FG1", cases: ["G1-initial", "G3"], checks: ["outputsAbsent"],
    counterexample: "a refused declaration's model/fold or Hom/Iso output is reported"},
  {id: "universe-contribution", phase: "FG3", cases: ["G2"], checks: ["clients", "refusedClients", "diagnostics"],
    counterexample: "generated Hom omits a fixed domain's universe contribution or preservation field, or lowers its universe"},
  {id: "unsupported-transport", phase: "FG2", cases: ["G3"], checks: ["clients", "refusals", "outputsAbsent"],
    counterexample: "usable base erased, unsupported Hom/Iso family leaked or a refusal without the dependent law"},
  {id: "match-computation", phase: "FG4", cases: ["G4", "G4-flat"], checks: ["clients", "refusedClients"],
    counterexample: "constant result or wrong clause selected"},
  {id: "lint-interface", phase: "FG5", cases: ["G5", "G5-single"], checks: ["advice", "clients"],
    counterexample: "unsafe edit or suppression limited to grouped binders"},
  {id: "failed-dependency", phase: "FG1", cases: ["G6"], checks: ["diagnostics"],
    counterexample: "wrong dependency identity or re-expanded parent failure"},
  {id: "wildcard-diagnostic", phase: "FG4", cases: ["G8"], checks: ["range", "diagnostics"],
    counterexample: "reversed endpoints or unrelated source span"},
  {id: "written-navigation", phase: "FG5", cases: ["G9"], checks: ["links", "clients"],
    counterexample: "wrong label, missing site or wrong binder target"},
  {id: "capture-origin", phase: "FG2/FG5", cases: ["G10"], checks: ["range", "diagnostics"],
    counterexample: "empty or unrelated conflict origin"},
  {id: "helper-meaning", phase: "FG2", cases: ["G11", "G11-grouped-dependent", "G11-inherited", "G11-initial"],
    checks: ["clients", "refusedClients"],
    counterexample: "captured equation checks instead of the intended equation"},
  {id: "recursive-step", phase: "FG2/FG4", cases: ["G12", "G12-inherited", "G12-initial"], checks: ["clients", "refusedClients"],
    counterexample: "constant iter or a successor returning op(c) instead of using its recursive result; distinguished at depth two"},
  {id: "lexical-shadowing", phase: "FG2/FG4", cases: ["G12-shadowed"], checks: ["clients", "refusedClients"],
    counterexample: "local iter resolved as the earlier recursive field"},
  {id: "type-unfolding-origin", phase: "FG5", cases: ["G12-range"], checks: ["range", "diagnostics"],
    counterexample: "unfolding accepted or its refusal loses the responsible reference"},
];
