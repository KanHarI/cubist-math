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
// Executable occurrences are confined to the registry and the configured
// known-observation transformer. JSON snapshots are inert observations.
export const captureObservationFiles = [
  "tests/fixtures/capture-refusals.mjs",
  "tests/fixtures/frontend-invariants-baseline.mjs",
];
