// K2.5: a ledger permits only a pinned public change, never an unchecked
// declaration. Types and values include a checked hash and readable rendering.
// The labels of the legacy truncation assumptions, which K2.5 step 5 removed
// from the language: the only assumptions a pinned change may remove. The
// ledger's changes, all in retired comparisons, keep them as the record.
const LEGACY = new Set(["Truncate","TruncateIntro","TruncateProp","TruncateElim"]);
// The archive's builtin excluded middle and choice over Truncate, removed
// with it, and the library's axioms over Trunc that replace them
// (h1-truncation-migration.md, step 1). A replacement is listed explicitly,
// never inferred.
export const REPLACEMENTS = new Map([["LEM[Truncate]","LEM"],["Choice[Truncate]","Choice"]]);
const pins = ["oldPublicType","newPublicType","oldValue","newValue"];
const lists = ["hypothesesAdded","assumptionsRemoved","assumptionsRetained","extensionsAdded","extensionsRetained"];
const sorted = values => [...values].sort();
const same = (a,b) => JSON.stringify(a) === JSON.stringify(b);

// A comparison the ledger retired, when a later change invalidated its pins:
// the last revision at which it passed, and its changes as they were pinned
// then, kept as the record and not checked again.
export function retiredComparison(ledger, module) {
  return (ledger?.retired ?? []).find(record => record.comparison === module) ?? null;
}

export function validateLedger(ledger) {
  const entries = new Map();
  if (ledger === null) return entries;
  if (ledger?.version !== 2 || !Array.isArray(ledger.changes)) throw Error("A migration ledger has version 2 and a changes array, including value pins and explicit assumption replacements.");
  if (ledger.retired !== undefined && (!Array.isArray(ledger.retired) || ledger.retired.some(record =>
    !/^[A-Za-z_][A-Za-z_0-9]*$/.test(record?.comparison ?? "") || !/^[a-f0-9]{7,40}$/.test(record.lastPassing ?? "")
    || typeof record.reason !== "string" || !Array.isArray(record.changes))
    || new Set(ledger.retired.map(record => record.comparison)).size !== ledger.retired.length))
    throw Error("A retired comparison names its module, its last passing revision, the reason and its recorded changes.");
  for (const entry of ledger.changes) {
    if (!/^[A-Za-z_][A-Za-z_0-9]*$/.test(entry.module ?? "") || !/^[A-Za-z_][A-Za-z_0-9]*$/.test(entry.declaration ?? ""))
      throw Error("Every ledger change names a module and declaration.");
    const key = `${entry.module}__${entry.declaration}`;
    if (entries.has(key)) throw Error(`Duplicate ledger change: ${key}.`);
    if (retiredComparison(ledger, entry.module)) throw Error(`Ledger change ${key} belongs to the retired ${entry.module} comparison.`);
    if (![1,2,3,4,6,7].includes(entry.remedyGroup)) throw Error(`Ledger change ${key} needs an implemented remedy group of 8.4; group 5 waits for H2.`);
    for (const field of pins)
      if (!/^[a-f0-9]{40}$/.test(entry[field]?.hash ?? "") || typeof entry[field]?.text !== "string")
        throw Error(`Ledger change ${key} needs a checked hash and rendering for ${field}.`);
    for (const field of lists) {
      const values = entry[field];
      if (!Array.isArray(values) || values.some(value => typeof value !== "string") || new Set(values).size !== values.length)
        throw Error(`Ledger change ${key} needs a list without duplicates for ${field}.`);
    }
    if (!Array.isArray(entry.assumptionsReplaced) || entry.assumptionsReplaced.some(change =>
      !REPLACEMENTS.has(change?.old) || REPLACEMENTS.get(change.old) !== change.new)
      || new Set(entry.assumptionsReplaced.map(change => change.old)).size !== entry.assumptionsReplaced.length)
      throw Error(`Ledger change ${key} may replace only LEM[Truncate] and Choice[Truncate], each by the library's axiom of its name.`);
    if (entry.assumptionsRemoved.some(name => !LEGACY.has(name)))
      throw Error(`Ledger change ${key} may remove only the four legacy truncation assumptions.`);
    if (entry.extensionsAdded.some(name => name !== "H1")) throw Error(`Ledger change ${key} may add only the recorded H1 extension.`);
    entries.set(key, entry);
  }
  return entries;
}

export function ledgerMatches(entry, observed) {
  if (!entry) return "No ledger entry for this declaration.";
  for (const field of pins) {
    if (entry[field].hash !== observed[field].hash || entry[field].text !== observed[field].text)
      return `The ledger's ${field} does not match the checked change.`;
  }
  for (const field of lists) {
    const before = entry[field], after = observed[field];
    if (!same(sorted(before), sorted(after)))
      return `The ledger's ${field} does not match the checked change.`;
  }
  const replacements = changes => changes.map(({old,new:value}) => `${old}->${value}`).sort();
  if (!same(replacements(entry.assumptionsReplaced), replacements(observed.assumptionsReplaced)))
    return "The ledger's assumptionsReplaced does not match the checked change.";
  if (observed.assumptionsAdded.length) return `A migration adds assumptions: ${observed.assumptionsAdded.join(", ")}.`;
  if (observed.extensionsRemoved.length) return `A migration removes kernel extensions: ${observed.extensionsRemoved.join(", ")}.`;
  if (observed.assumptionsRemoved.some(name => !LEGACY.has(name))) return "The change removes an assumption outside the truncation policy.";
  return null;
}
