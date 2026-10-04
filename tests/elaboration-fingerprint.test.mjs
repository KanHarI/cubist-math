import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { compareFingerprints, elaborationFingerprint } from "../tools/elaboration-fingerprint.mjs";

// The fixture is cubist-tests/fingerprint_fixture.cubist.
const fixture = await readFile(new URL("../cubist-tests/fingerprint_fixture.cubist", import.meta.url), "utf8");
const fingerprint = source => elaborationFingerprint({ modules: ["fingerprint_fixture"],
  readSource: async name => { if (name !== "fingerprint_fixture") throw Error(`Unexpected import: ${name}`); return source; } });

test("elaboration fingerprints are stable and record checked terms and inspector records", async () => {
  const [first, second] = [await fingerprint(fixture), await fingerprint(fixture)];
  assert.deepEqual(compareFingerprints(first, second), []);
  assert.equal(first.declarations.fingerprint_fixture__two.status, "checked-native-cubical");
  // A universe-generic definition is one checked declaration (G0).
  assert.equal(first.declarations.fingerprint_fixture__mirror.status, "checked-native-cubical");
  assert.ok(first.declarations.fingerprint_fixture__mirror.term);
  assert.ok(Object.values(first.references).some(item => item.node.role === "rewrite witness"));
});

test("elaboration fingerprints detect a changed proof term and a changed source site", async () => {
  const before = await fingerprint(fixture);
  const changed = compareFingerprints(before, await fingerprint(fixture.replace("exact q;", "exact trans(q, refl(x));")));
  assert.ok(changed.some(line => line.startsWith("fingerprint.declarations.fingerprint_fixture__moved.term:")));
  const moved = compareFingerprints(before, await fingerprint(`\n${fixture}`));
  assert.ok(moved.some(line => line.startsWith("fingerprint.references.")));
});
