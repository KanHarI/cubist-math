export const axiomLabels = {
  lib_univalence: "Univalence",
  lib_funext: "Function extensionality",
  lib_funext_compute: "Function extensionality computation",
  lib_LEM: "Excluded middle",
  lib_AOC: "Axiom of choice",
  LEM: "Excluded middle",
  AOC: "Axiom of choice",
  lib_Trunc: "Propositional truncation",
  lib_trunc_intro: "Truncation introduction",
  lib_trunc_elim: "Truncation elimination",
  lib_trunc_is_trunc: "Truncation is a proposition",
};

// The assumptions a result relies on, by their labels (a Map, or a result's
// plain object), once each and sorted.
export function assumptionsOf(output, labels = {}) {
  const label = name => labels instanceof Map ? labels.get(name) ?? name
    : Object.hasOwn(labels, name) ? labels[name] : name;
  return [...new Set((output.axioms ?? []).map(label))].sort();
}

// One line for each checked result that relies on an assumption, naming
// every assumption it relies on, as the command line, the REPL and the
// language reference report a result.
export const assumptionLines = (outputs, labels = {}) => outputs.filter(output => output.verified !== false)
  .map(output => [output.name, assumptionsOf(output, labels)]).filter(([, used]) => used.length)
  .map(([name, used]) => `${name} assumes ${used.join(", ")}`);
