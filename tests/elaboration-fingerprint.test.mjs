import test from "node:test";
import assert from "node:assert/strict";
import { compareFingerprints, elaborationFingerprint } from "../tools/elaboration-fingerprint.mjs";

const fixture = `def two : succ(1) = 2 {
  rfl;
}
def moved(x, y : Nat, p : x = y, q : y = x) : x = x {
  rw [p];
  exact q;
}
def mirror(U : Universe, A : U, x, y : A, p : x = y) : y = x {
  exact path(fun (i : Interval) => A, fun (i : Interval) => at(p, flip(i)));
}
def mirror_nat := mirror(U0, Nat);
`;
const fingerprint = source => elaborationFingerprint({ modules: ["fingerprint_fixture"],
  readSource: async name => { if (name !== "fingerprint_fixture") throw Error(`Unexpected import: ${name}`); return source; } });

test("elaboration fingerprints are stable and record checked terms, inspector records and template links", async () => {
  const [first, second] = [await fingerprint(fixture), await fingerprint(fixture)];
  assert.deepEqual(compareFingerprints(first, second), []);
  assert.equal(first.declarations.fingerprint_fixture__two.status, "checked-native-cubical");
  assert.match(first.declarations.fingerprint_fixture__mirror.reason, /^Universe schema/);
  assert.ok(first.definitions.fingerprint_fixture__mirror__U0);
  assert.ok(first.inspections.fingerprint_fixture__mirror.type);
  assert.ok(Object.values(first.references).some(item => item.node.role === "rewrite witness"));
  assert.ok(first.links.fingerprint_fixture.some(link => link.template === "mirror"));
});

test("elaboration fingerprints detect a changed proof term and a changed source site", async () => {
  const before = await fingerprint(fixture);
  const changed = compareFingerprints(before, await fingerprint(fixture.replace("exact q;", "exact trans(q, refl(x));")));
  assert.ok(changed.some(line => line.startsWith("fingerprint.declarations.fingerprint_fixture__moved.term:")));
  const moved = compareFingerprints(before, await fingerprint(`\n${fixture}`));
  assert.ok(moved.some(line => line.startsWith("fingerprint.references.")));
});
