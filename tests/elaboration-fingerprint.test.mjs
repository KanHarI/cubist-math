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
def mirror(U < UU0, A : U, x, y : A, p : x = y) : y = x {
  exact path(fun (i : Interval) => A, fun (i : Interval) => at(p, flip(i)));
}
def mirror_nat := mirror(U0, Nat);
`;
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
