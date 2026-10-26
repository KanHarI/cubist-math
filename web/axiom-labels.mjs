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

// The line that reports a result's assumptions, as the command line, the
// REPL, the workspace's context console and the language reference show
// it: `name assumes A, B`, `assumes A, B` for a result with no name, or null
// for a result that relies on none, which is reported as nothing.
export function assumptionNote(axioms, labels = {}, subject = null) {
  const used = assumptionsOf({ axioms }, labels);
  return used.length ? `${subject ? `${subject} ` : ""}assumes ${used.join(", ")}` : null;
}

// One line for each checked declaration that relies on an assumption.
export const assumptionLines = (outputs, labels = {}) => outputs.filter(output => output.verified !== false)
  .map(output => assumptionNote(output.axioms, labels, output.name)).filter(Boolean);
