import test from "node:test";
import assert from "node:assert/strict";
import { access, readFile } from "node:fs/promises";
import { proofCatalog, proofTopics, proofsInTopic } from "../web/proof-library.mjs";
import { archiveModules } from "../web/cubist/modules.mjs";
import { parse } from "../web/cubist/parser.mjs";

test("every bundled import is available to the browser worker", async () => {
  const available = new Set(archiveModules);
  await Promise.all([...available].map(async name => {
    const source = await readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
    for (const dependency of parse(source).imports) {
      assert.ok(available.has(dependency), `${name} imports unregistered module ${dependency}`);
    }
  }));
});

test("every proof is reachable through exactly one nonempty browsing topic", async () => {
  assert.equal(new Set(proofCatalog.map(p => p.id)).size, proofCatalog.length);
  assert.equal(new Set(proofTopics.map(p => p.id)).size, proofTopics.length);
  const grouped = proofTopics.flatMap(topic => {
    const proofs = proofsInTopic(topic.id);
    assert.ok(proofs.length, topic.title);
    assert.ok(proofs.length < 40, `${topic.title} needs a smaller submenu`);
    assert.deepEqual(proofs.map(p => p.title), proofs.map(p => p.title).sort((a, b) => a.localeCompare(b)));
    return proofs.map(p => p.id);
  });
  assert.deepEqual(grouped.sort(), proofCatalog.map(p => p.id).sort());
  // The catalog names each archive module once, and no other.
  assert.deepEqual(proofCatalog.map(p => p.id).sort(), [...archiveModules].sort());
  await Promise.all(proofCatalog.map(p => access(new URL(`../archive/first-library/${p.id}.cubist`, import.meta.url))));
});
