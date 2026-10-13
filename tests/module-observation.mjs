import assert from "node:assert/strict";
import { precondition } from "./known-defect.mjs";

// Missing local output is a semantic observation, just like a refused
// declaration. A source-position predicate distinguishes repeated names.
export function outputStatus(result, name, at = () => true) {
  return result.outputs.find(output => output.name === name && at(output))?.verified ?? null;
}

// Every semantic harness and its controls use the same boundary: failures
// in dependencies prevent the experiment; failures in this module are data.
export function observeModule(result, {name = "main", clients = []} = {}) {
  precondition(() => assert.deepEqual(result.gaps.filter(gap => gap.module !== name), [],
    `${name}: all imported fixtures must check`));
  return {
    gaps: result.gaps.map(gap => [gap.module, gap.name, gap.code]),
    clients: Object.fromEntries(clients.map(client => [client, outputStatus(result, client)])),
    assumes: result.outputs.filter(output => output.verified && output.axioms?.length).map(output => output.name),
  };
}
