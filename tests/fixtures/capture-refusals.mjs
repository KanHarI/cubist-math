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
// is ill-typed, check its ordinary refusal instead of inventing a negative.
// Edits name the main source or an imported fixture and apply exactly once.
export const captureControls = {
  "imported-pattern-rename": {
    positive:"meaning",
    intended:[{module:"parent",anchor:"succ(b) =>",replacement:"succ(other) =>"}],
    captured:{kind:"refused",module:"parent",name:"P",code:"E606",
      reason:"The captured local b has type Nat, but the field b has arbitrary type M.",
      edits:[{module:"parent",anchor:"succ(b) => a;",replacement:"succ(b) => b;"}]},
  },
  "helper-pattern-argument": {
    positive:"intended",
    intended:[{module:"main",anchor:"box(k) =>",replacement:"box(other) =>"}],
    captured:{kind:"clients",negative:"captured",edits:[{module:"main",anchor:"box(k) => x;",replacement:"box(k) => k;"}]},
  },
  "model-shadows-theory": {
    positive:"intended",
    intended:[{module:"main",anchor:"T(U0)",replacement:"Previous(U0)"},
      {module:"prior",anchor:"theory T(",replacement:"theory Previous("}],
    captured:{kind:"refused",module:"main",name:"T",code:"E850",
      reason:"The new T is a carrier, not a universe-polymorphic theory. Explicitly apply a carrier as a theory.",
      edits:[{module:"main",anchor:"initial T : T(U0);",
        replacement:"inductive Carrier : set U0 { point; }\ninitial T : Carrier(U0);"}]},
  },
  "model-shadows-header-global": {
    positive:"intended",
    intended:[{module:"main",anchor:"T(U0, N)",replacement:"T(U0, Previous)"},
      {module:"prior",anchor:"def N :",replacement:"def Previous :"}],
    // Explicitly make c recursive: its argument is the new carrier N,
    // which is precisely the wrong reading of the imported header argument.
    captured:{kind:"clients",negative:"captured",edits:[{module:"main",anchor:"initial N : T(U0, N);",
      replacement:"theory Recursive(U < UU0) { M : set U; c(x : M) : M; }\ninitial N : Recursive(U0);"}]},
  },
  "model-shadows-parameter-global": {
    positive:"intended",
    intended:[{module:"main",anchor:"A : W",replacement:"A : Previous"},
      {module:"prior",anchor:"def W :",replacement:"def Previous :"}],
    captured:{kind:"refused",module:"main",name:"W",code:"E604",
      reason:"The new W is indexed; a bare indexed type constructor cannot be the parameter's domain. State that type constructor explicitly.",
      edits:[{module:"main",anchor:"free W(A : W) : T(U0) on Unit;",
        replacement:"inductive Indexed(A : Unit) : set U0 { point; }\nfree W(A : Indexed) : T(U0) on Unit;"}]},
  },
  "initial-pattern-model": {
    positive:"intended",ordinaryRefusals:{k:"E856"},
    intended:[{module:"main",anchor:"succ(k) =>",replacement:"succ(other) =>"}],
    captured:{kind:"refused",module:"main",name:"P",code:"E343",
      reason:"The captured k is a Nat pattern variable, not the model used to qualify c. The equation strategy also independently refuses match laws.",
      edits:[{module:"main",anchor:"succ(k) => c;",replacement:"succ(k) => k.c;"}]},
  },
  G10: {
    positive:"intended",
    intended:[{module:"main",anchor:"box(c) => k(zero);",replacement:"box(local_) => k(zero);"}],
    captured:{kind:"clients",negative:"captured",edits:[{module:"main",anchor:"box(c) => k(zero);",replacement:"box(c) => c;"}]},
  },
};
// Executable occurrences are confined to the registry and the configured
// known-observation transformer. JSON snapshots are inert observations.
export const captureObservationFiles = [
  "tests/fixtures/capture-refusals.mjs",
  "tests/fixtures/frontend-invariants-baseline.mjs",
];
