import test from "node:test";
import assert from "node:assert/strict";
import { access } from "node:fs/promises";
import { proofChoices, proofTopics, proofsInTopic } from "../web/proof-library.mjs";
import { sourceModules } from "../web/mathscript/modules.mjs";

test("every proof is reachable through exactly one nonempty browsing topic", async () => {
  assert.equal(new Set(proofChoices.map(p => p.id)).size, proofChoices.length);
  assert.equal(new Set(proofTopics.map(p => p.id)).size, proofTopics.length);
  const grouped = proofTopics.flatMap(topic => {
    const proofs = proofsInTopic(topic.id);
    assert.ok(proofs.length, topic.title);
    assert.ok(proofs.length < 40, `${topic.title} needs a smaller submenu`);
    assert.deepEqual(proofs.map(p => p.title), proofs.map(p => p.title).sort((a, b) => a.localeCompare(b)));
    return proofs.map(p => p.id);
  });
  assert.deepEqual(grouped.sort(), proofChoices.map(p => p.id).sort());
  for (const source of sourceModules) assert.ok(proofChoices.some(p => p.id === source), source);
  await Promise.all(proofChoices.map(p => access(new URL(`../web/proofs/${p.file ?? p.id + ".proof"}`, import.meta.url))));
});
