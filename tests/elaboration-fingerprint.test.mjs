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

// An axiom has no definition; its fingerprint pins the statement it assumes.
test("elaboration fingerprints pin an axiom's assumed statement", async () => {
  const before = await fingerprint("def A := axiom Unit;\ndef use_ := A;\n");
  assert.ok(before.declarations.fingerprint_fixture__A.type);
  const changed = compareFingerprints(before, await fingerprint("def A := axiom Unit -> Unit;\ndef use_ := A;\n"));
  assert.ok(changed.some(line => line.startsWith("fingerprint.declarations.fingerprint_fixture__A.type:")), changed.join("\n"));
});

test("a compiled match names its generated binders alike in every elaboration", async () => {
  // Several values make a compiled match (web/translator/patterns.mjs), whose
  // generated names are numbered within the match, not across elaborations.
  const source = "inductive N { zero; succ(n : N); }\n"
    + "def both(x, y : N) : N := match x, y { zero, _ => zero; succ(a), zero => a; succ(a), succ(b) => b; };\n";
  const once = () => elaborationFingerprint({ modules: ["compiled_match"],
    readSource: async name => { if (name !== "compiled_match") throw Error(`Unexpected import: ${name}`); return source; } });
  const [first, second] = [await once(), await once()];
  assert.equal(first.declarations.compiled_match__both.status, "checked-native-cubical");
  assert.deepEqual(compareFingerprints(first, second), []);
});

// An unavailable module is a failed experiment, not a smaller fingerprint.
// Ordinary declaration refusals still belong in a comparison's observations.
test("fingerprints refuse missing entry/transitive imports but retain declaration refusals", async () => {
  await assert.rejects(elaborationFingerprint({ modules: ["missing"],
    readSource: async () => { throw Error("entry unavailable"); } }), /incomplete import graph: missing: entry unavailable/);
  await assert.rejects(fingerprint("import absent; def independent : Unit := tt;"), /incomplete import graph: absent:/);
  const refused = await fingerprint("def wrong : Void := tt;");
  assert.equal(refused.declarations.fingerprint_fixture__wrong.status, "not-translated");
  assert.equal(refused.gaps[0].name, "wrong");
});
