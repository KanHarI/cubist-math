// Capture-only diagnostics are observations to retire, never language
// contracts. Every replacement names its owning migration package. CB7
// removes the implementations after these semantic witnesses are active.
export const captureRefusals = [
  {code:"E801", phase:"CB2/CB3", witnesses:["imported-pattern-rename"]},
  {code:"E860", phase:"CB3", witnesses:["helper-pattern-argument"]},
  {code:"E866", phase:"CB4", witnesses:["model-shadows-theory", "model-shadows-header-global", "model-shadows-parameter-global"]},
  {code:"E869", phase:"CB4", witnesses:["initial-pattern-model"]},
  {code:"E871", phase:"CB3", witnesses:["G10"]},
];
// Source controls belong to the migration witness contract. `intended`
// removes the name collision without changing the client's meaning. A
// `captured` edit explicitly expresses the other binding structure: the
// positive and negative clients must exchange verdicts. If that structure
// is ill-typed, document why and do not pretend to have a negative client.
// Edits name the main source or an imported fixture and apply exactly once.
export const captureControls = {
  "imported-pattern-rename": {
    positive:"meaning", noCaptured:"The captured local b has type Nat, but the field b has arbitrary type M; that reading is ill-typed.",
    intended:[{module:"parent",anchor:"succ(b) =>",replacement:"succ(other) =>"}],
  },
  "helper-pattern-argument": {
    positive:"intended", negative:"captured",
    intended:[{module:"main",anchor:"box(k) =>",replacement:"box(other) =>"}],
    captured:[{module:"main",anchor:"box(k) => x;",replacement:"box(k) => k;"}],
  },
  "model-shadows-theory": {
    positive:"intended", noCaptured:"The new T is a carrier, not a universe-polymorphic theory; the captured T(U0) cannot denote a theory.",
    intended:[{module:"main",anchor:"T(U0)",replacement:"Previous(U0)"},
      {module:"prior",anchor:"theory T(",replacement:"theory Previous("}],
  },
  "model-shadows-header-global": {
    positive:"intended", negative:"captured",
    intended:[{module:"main",anchor:"T(U0, N)",replacement:"T(U0, Previous)"},
      {module:"prior",anchor:"def N :",replacement:"def Previous :"}],
    // Explicitly make c recursive: its argument is the new carrier N,
    // which is precisely the wrong reading of the imported header argument.
    captured:[{module:"main",anchor:"initial N : T(U0, N);",
      replacement:"theory Recursive(U < UU0) { M : set U; c(x : M) : M; }\ninitial N : Recursive(U0);"}],
  },
  "model-shadows-parameter-global": {
    positive:"intended", noCaptured:"The new W is an indexed type constructor; bare W cannot be the parameter's domain in place of the imported Unit type.",
    intended:[{module:"main",anchor:"A : W",replacement:"A : Previous"},
      {module:"prior",anchor:"def W :",replacement:"def Previous :"}],
  },
  "initial-pattern-model": {
    positive:"intended", noCaptured:"The captured k is a Nat pattern variable, not the model used to qualify c; that reading is ill-typed. The equation strategy also independently refuses match laws.",
    intended:[{module:"main",anchor:"succ(k) =>",replacement:"succ(other) =>"}],
  },
  G10: {
    positive:"intended", negative:"captured",
    intended:[{module:"main",anchor:"box(c) => k(zero);",replacement:"box(local_) => k(zero);"}],
    captured:[{module:"main",anchor:"box(c) => k(zero);",replacement:"box(c) => c;"}],
  },
};
// Executable occurrences are confined to the registry and the configured
// known-observation transformer. JSON snapshots are inert observations.
export const captureObservationFiles = [
  "tests/fixtures/capture-refusals.mjs",
  "tests/fixtures/frontend-invariants-baseline.mjs",
];
