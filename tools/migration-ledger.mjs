// K2.5: a ledger permits only a pinned public change, never an unchecked
// declaration. Types include their canonical hash and a readable rendering.
const LEGACY = new Set(["Truncate","TruncateIntro","TruncateProp","TruncateElim"]);
const fields = ["oldPublicType","newPublicType","hypothesesAdded","assumptionsRemoved","assumptionsRetained",
  "extensionsAdded","extensionsRetained"];
const sorted = values => [...values].sort();
const same = (a,b) => JSON.stringify(a) === JSON.stringify(b);

export function validateLedger(ledger) {
  const entries = new Map();
  if (ledger === null) return entries;
  if (ledger?.version !== 1 || !Array.isArray(ledger.changes)) throw Error("A migration ledger has version 1 and a changes array.");
  for (const entry of ledger.changes) {
    if (!/^[A-Za-z_][A-Za-z_0-9]*$/.test(entry.module ?? "") || !/^[A-Za-z_][A-Za-z_0-9]*$/.test(entry.declaration ?? ""))
      throw Error("Every ledger change names a module and declaration.");
    const key = `${entry.module}__${entry.declaration}`;
    if (entries.has(key)) throw Error(`Duplicate ledger change: ${key}.`);
    if (![1,2,3,4,6,7].includes(entry.remedyGroup)) throw Error(`Ledger change ${key} needs an implemented remedy group of 8.4; group 5 waits for H2.`);
    for (const field of ["oldPublicType","newPublicType"])
      if (!/^[a-f0-9]{40}$/.test(entry[field]?.hash ?? "") || typeof entry[field]?.text !== "string")
        throw Error(`Ledger change ${key} needs a checked type hash and rendering for ${field}.`);
    for (const field of fields.slice(2)) {
      const values = entry[field];
      if (!Array.isArray(values) || values.some(value => typeof value !== "string") || new Set(values).size !== values.length)
        throw Error(`Ledger change ${key} needs a list without duplicates for ${field}.`);
    }
    if (entry.assumptionsRemoved.some(name => !LEGACY.has(name)))
      throw Error(`Ledger change ${key} may remove only the four legacy truncation assumptions.`);
    if (entry.extensionsAdded.some(name => name !== "H1")) throw Error(`Ledger change ${key} may add only the recorded H1 extension.`);
    entries.set(key, entry);
  }
  return entries;
}

export function ledgerMatches(entry, observed) {
  if (!entry) return "No ledger entry for this declaration.";
  for (const field of fields) {
    const before = entry[field], after = observed[field];
    if (!same(Array.isArray(before) ? sorted(before) : before, Array.isArray(after) ? sorted(after) : after))
      return `The ledger's ${field} does not match the checked change.`;
  }
  if (observed.assumptionsAdded.length) return `A migration adds assumptions: ${observed.assumptionsAdded.join(", ")}.`;
  if (observed.extensionsRemoved.length) return `A migration removes kernel extensions: ${observed.extensionsRemoved.join(", ")}.`;
  if (observed.assumptionsRemoved.some(name => !LEGACY.has(name))) return "The change removes an assumption outside the truncation policy.";
  return null;
}
