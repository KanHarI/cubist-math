import assert from "node:assert/strict";
import { createHash } from "node:crypto";

// Entry order is UTF-16 code-unit order, independent of host locale.
export const byName = ([a], [b]) => a < b ? -1 : a > b ? 1 : 0;
export const jsonDigest = value => createHash("sha256").update(JSON.stringify(value)).digest("hex");
export function hashEntries(entries) {
  const hash = createHash("sha256");
  for (const [name, bytes] of [...entries].sort(byName))
    hash.update(name).update("\0").update(bytes).update("\0");
  return hash.digest("hex");
}
export const digestFormats = {
  entries: "SHA-256 of sorted UTF-8 name NUL bytes NUL entries; UTF-16 code-unit name order",
  json: "SHA-256 of UTF-8 JSON.stringify(value), without whitespace or trailing newline",
  sourceDigest: "entries over every loaded module name and exact source",
  interfacesDigest: "entries over binding and JSON.stringify({type,axioms}); type is canonicalHasher SHA-1; axioms sorted",
  declarationFuelDigest: "json of [binding,searchFuel] pairs sorted by binding; object key order is checker serialization order",
  generatedNamesDigest: "json of sorted generated binding names",
  assumptionsDigest: "json of sorted assumption labels",
  assumptionDependenciesDigest: "json of [binding,sorted axioms] pairs sorted by binding",
  typeDigest: "canonicalHasher SHA-1 (tools/canonical-hash.mjs), alpha-invariant for bound terms and dimensions",
};

export function compactSamples(raw) {
  const workloads = {}, samples = [];
  for (const sample of raw) {
    const {name, source, declarations, verified, generatedNames, interfacesDigest, assumptions,
      sourceDigest, declarationFuel, gaps, ...measurements} = sample;
    assert.deepEqual(gaps, [], `${name}: workload must check`);
    const digests = { sourceDigest, interfacesDigest,
      declarationFuelDigest:jsonDigest([...declarationFuel].sort(byName)),
      generatedNamesDigest:jsonDigest(generatedNames), assumptionsDigest:jsonDigest(assumptions) };
    const inventory = {source, declarations, verified, generatedNames, assumptions, ...digests};
    if (workloads[name]) assert.deepEqual(inventory, workloads[name], `${name}: collection mode/repeat changed semantics or deterministic fuel`);
    else workloads[name] = inventory;
    // Retain these on every sample so artifact readers can check agreement.
    samples.push({name, ...measurements, digests, gaps});
  }
  return {workloads, samples};
}
