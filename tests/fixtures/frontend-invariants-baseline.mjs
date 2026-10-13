// Known defects are transformations of this configuration's desired result,
// never snapshots borrowed from another seed. Keep the actual distinctions:
// inherited field renaming also breaks named calls; a colliding lambda binder
// can refuse the child before any of its clients elaborate.
export function knownPreservation(config, desired) {
  if (config.recursive || config.paths) return undefined;
  const renamed = config.inherited && config.renamed;
  const observed = structuredClone(desired);
  if (renamed && config.binder === "point") {
    const dependents = ["intended", "named", "captured", "law_meaning", "identity", "child_selection",
      "N", "generated", "forget", "forgotten", "W", "fold_computes"];
    observed.gaps = [["main", "Child", "E801"], ...dependents.map(name => ["main", name, "E340"])];
    for (const name of Object.keys(observed.accepted)) observed.accepted[name] = false;
    observed.fields = [];
    for (const name of Object.keys(observed.artifacts)) observed.artifacts[name] = false;
    return { phase: "CB2/CB3", defect: "inherited-binder-capture-refusal", observed };
  }
  if (!config.capture) return undefined;
  const failures = renamed ? ["intended", "named", "captured", "generated"] : ["intended", "generated"];
  observed.gaps = failures.map(name => ["main", name, "E606"]);
  for (const name of failures) if (Object.hasOwn(observed.accepted, name)) observed.accepted[name] = false;
  return { phase: "CB2", defect: renamed ? "capture-and-renamed-public-parameter" : "parameter-capture", observed };
}
