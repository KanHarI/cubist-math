// Independently authored from the FG0–FG5 acceptance contracts, not generated
// from the case registry. Keep an obligation when a fixture is removed: losing
// both a fixture and its manifest row must still expose the missing behavior.
// Counterexamples describe what the linked audit must distinguish; their
// semantic adequacy is established by executable controls, not these labels.
export const obligations = [
  {id: "ownership", phase: "FG1", cases: ["G1", "G1-initial", "G1-reverse", "G1-same-kind"],
    counterexample: "replaced original binding or lost original client"},
  {id: "atomic-publication", phase: "FG1", cases: ["G1", "G1-initial", "G3"],
    counterexample: "refusal alongside a published member of the refused group"},
  {id: "universe-contribution", phase: "FG3", cases: ["G2"],
    counterexample: "generated Hom omits a fixed domain's universe contribution"},
  {id: "unsupported-transport", phase: "FG2", cases: ["G3"],
    counterexample: "usable base erased or unsupported Hom/Iso family leaked"},
  {id: "match-computation", phase: "FG4", cases: ["G4", "G4-flat"],
    counterexample: "constant result or wrong clause selected"},
  {id: "lint-interface", phase: "FG5", cases: ["G5", "G5-single"],
    counterexample: "unsafe edit or suppression limited to grouped binders"},
  {id: "failed-dependency", phase: "FG1", cases: ["G6"],
    counterexample: "wrong dependency identity or re-expanded parent failure"},
  {id: "wildcard-diagnostic", phase: "FG4", cases: ["G8"],
    counterexample: "reversed endpoints or unrelated source span"},
  {id: "written-navigation", phase: "FG5", cases: ["G9"],
    counterexample: "wrong label, missing site or wrong binder target"},
  {id: "capture-origin", phase: "FG2/FG5", cases: ["G10"],
    counterexample: "empty or unrelated conflict origin"},
  {id: "helper-meaning", phase: "FG2", cases: ["G11", "G11-grouped-dependent", "G11-inherited", "G11-initial"],
    counterexample: "captured equation checks instead of the intended equation"},
  {id: "recursive-step", phase: "FG2/FG4", cases: ["G12", "G12-inherited", "G12-initial"],
    counterexample: "constant iter or a result that never takes the recursive step"},
  {id: "lexical-shadowing", phase: "FG2/FG4", cases: ["G12-shadowed"],
    counterexample: "local iter resolved as the earlier recursive field"},
  {id: "type-unfolding-origin", phase: "FG5", cases: ["G12-range"],
    counterexample: "unfolding accepted or its refusal loses the responsible reference"},
];
