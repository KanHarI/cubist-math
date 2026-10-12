// Independently authored from the FG0–FG5 acceptance contracts, not generated
// from the case registry. Keep an obligation when a fixture is removed: losing
// both a fixture and its manifest row must still expose the missing behavior.
// `checks` names the contract requirements each witness must keep; the audit
// applies every requirement's counterexamples to an accepted observation, so
// these labels name executable distinctions rather than establish them.
//
// Each witness states, as data, what its case must keep. Every expectation a
// case states must be kept by one of its witnesses, so none can be deleted,
// moved or weakened without failing validation. Names (clients, refused
// clients, absent outputs and declaration diagnostics) are kept as minimums: a
// fixture may say more about a diagnostic, such as a code its witness leaves
// free. Everything else is kept exactly: source anchors and lint rewrites,
// from which range and advice counterexamples are placed, the collision's
// binding and the failed dependency's identity. A diagnostic cause outside
// the codes that always carry one must be required here, so that weakening a
// fixture's expectation fails validation and its cause counterexamples come
// from this map rather than from the expectation under test.
const wrongEquation = {refusedClients: {wrong: {code: "E606"}}};
const recursiveResults = declarations => ({clients: [...declarations, "base", "computation", "computation2"], ...wrongEquation});
const opposedEquations = {clients: ["intended"], refusedClients: {captured: {code: "E606"}}};
const generatedInterface = {clients: ["identity", "applied", "N", "N.model", "N.fold"]};
const duplicate = {diagnostic: {name: "N", cause: {duplicate: "N"}}, clients: ["original", "independent"], symbol: "N", originalType: "Unit"};
const lawDependency = {code: "E817", cause: {operation: "op", argument: "p", law: "l"}};
const groupedAdvice = {from: "forall x, y : M. M", to: "M -> M -> M", advice: ["x", "y"].map(name =>
  ({code: "W706", declaration: "T", message: `${name} is unused in the body: take it out of the group and write M -> … for it.`}))};
const singleAdvice = {from: "forall x : M. M", to: "M -> M", advice: [
  {code: "W705", declaration: "T", message: "x is unused in the body: write M -> … instead of forall x : M. …."}]};

export const obligations = [
  {id: "ownership", phase: "FG1", checks: ["clients", "originalType", "diagnostics"],
    witnesses: {G1: duplicate, "G1-initial": duplicate, "G1-same-kind": duplicate,
      "G1-reverse": {...duplicate, clients: ["original", "constructor", "independent"], originalType: "U0"}},
    counterexample: "replaced original binding, lost original or unrelated client, or a duplicate refused for another reason"},
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
    witnesses: {G2: {
      clients: ["T.Hom", "identity", "computation", "iso", "preserves", "level",
        "identity_u1", "computation_u1", "iso_u1", "preserves_u1", "level_u1"],
      refusedClients: {lowered: {code: "E606", cause: {found: "U1", expected: "U0"}}}}},
    counterexample: "generated Hom omits a fixed domain's universe contribution or preservation field, "
      + "loses Hom/Iso identity or composition at either level, or lowers its universe"},
  {id: "unsupported-transport", phase: "FG2", checks: ["clients", "diagnostics", "outputsAbsent"],
    witnesses: {G3: {clients: ["T", "T.make", "T.op", "usable"], refusedClients: {unsupported: lawDependency, unsupported_iso: lawDependency}}},
    counterexample: "usable base erased, unsupported Hom/Iso family leaked or a Hom or Iso refusal without the dependent law"},
  {id: "match-computation", phase: "FG4", checks: ["clients", "refusedClients"],
    witnesses: {G4: {clients: ["T.value", "computation", "off_computation", "empty_computation"], ...wrongEquation},
      "G4-flat": {clients: ["T.value", "computation", "empty_computation"], ...wrongEquation}},
    counterexample: "derived match refused, constant result or wrong clause selected"},
  {id: "lint-interface", phase: "FG5", checks: ["advice", "clients"],
    witnesses: {G5: {...generatedInterface, rewrite: groupedAdvice}, "G5-single": {...generatedInterface, rewrite: singleAdvice}},
    counterexample: "unsafe edit or suppression limited to grouped binders"},
  {id: "failed-dependency", phase: "FG1", checks: ["diagnostics"],
    witnesses: {G6: {clients: ["independent"], parent: "P", child: "C", cause: "Undefined"}},
    counterexample: "wrong dependency identity, re-expanded parent failure or lost unrelated client"},
  {id: "wildcard-diagnostic", phase: "FG4", checks: ["range", "diagnostics"],
    witnesses: {G8: {diagnostic: {name: "h", code: "E606", cause: {found: "t1 = t1", expected: "t0 = t1"},
      scope: ":= match x { t0 => t0; _ => t1; };", token: "t1"}}},
    counterexample: "reversed endpoints or unrelated source span"},
  {id: "written-navigation", phase: "FG5", checks: ["links", "clients"],
    witnesses: {G9: {observations: {scope: "law l(c : M) : k(c) = op(c, c);", label: "c", sites: 4}, clients: ["meaning"]}},
    counterexample: "wrong label, missing site, wrong binder target or changed law meaning"},
  {id: "capture-origin", phase: "FG2/FG5", checks: ["range", "diagnostics"],
    witnesses: {G10: {diagnostic: {name: "T", code: "E871", cause: {helper: "k", field: "c"},
      conflict: "succ(c) => k(c)", binder: "c", binderOccurrence: 0, call: "k(c)"}}},
    counterexample: "empty or unrelated conflict origin"},
  {id: "helper-meaning", phase: "FG2", checks: ["clients", "refusedClients"],
    witnesses: {G11: opposedEquations, "G11-grouped-dependent": opposedEquations, "G11-inherited": opposedEquations, "G11-initial": opposedEquations},
    counterexample: "captured equation checks instead of the intended equation"},
  {id: "recursive-step", phase: "FG2/FG4", checks: ["clients", "refusedClients"],
    witnesses: {G12: recursiveResults(["T.iter", "T.twice"]), "G12-inherited": recursiveResults(["Child.iter", "Child.twice"]),
      "G12-initial": recursiveResults(["N", "N.model"])},
    counterexample: "recursive value refused, constant iter or a successor returning op(c) instead of using its recursive result; distinguished at depth two"},
  {id: "lexical-shadowing", phase: "FG2/FG4", checks: ["clients", "refusedClients"], witnesses: {"G12-shadowed": opposedEquations},
    counterexample: "local iter resolved as the earlier recursive field"},
  {id: "type-unfolding-origin", phase: "FG5", checks: ["range", "diagnostics"],
    witnesses: {"G12-range": {diagnostic: {name: "T", code: "E845", cause: {recursive: "iter", context: "field type"},
      scope: "law nope(n : Nat) : iter(n) = c;", token: "iter"}}},
    counterexample: "unfolding accepted or its refusal loses the responsible reference"},
];

// The conditions each contract requirement judges, stated independently of
// the contract's tables. The audit requires a counterexample that violates
// each condition alone, but deleting a condition would delete its
// counterexamples with it; this list makes that deletion fail.
export const requirementConditions = {
  clients: ["checked"],
  refusedClients: ["refused"],
  outputsAbsent: ["absent"],
  originalType: ["verified", "type"],
  advice: ["count", "codes", "declarations", "messages", "startsInTarget", "endsInTarget", "nonempty"],
  range: ["located", "startsInRegion", "endsInRegion", "coversSite"],
  links: ["present", "label", "target", "start", "end"],
  diagnostics: ["matched"],
};
