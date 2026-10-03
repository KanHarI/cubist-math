import assert from "node:assert/strict";
import { proofCatalog } from "../web/proof-library.mjs";

// Follow the same topic-first route as a person using the proof browser.
export async function selectProof(page, id) {
  const proof = proofCatalog.find(item => item.id === id);
  assert.ok(proof, `Unknown proof: ${id}`);
  await page.locator("#proof-topic").selectOption(proof.topic);
  await page.locator("#proof-picker").selectOption(id);
}
