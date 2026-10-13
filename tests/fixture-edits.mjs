import assert from "node:assert/strict";
import { precondition } from "./known-defect.mjs";

// A source control must apply its intended edit. A missing/duplicated site
// is a broken fixture, never a passing copy of the unedited source.
export function editedFixture(source, {anchor, replacement}, id = "fixture") {
  precondition(() => {
    assert.ok(anchor && typeof source === "string" && source.split(anchor).length === 2,
      `${id}: probe anchor must occur exactly once`);
    assert.equal(typeof replacement,"string",`${id}: probe replacement must be source text`);
    assert.notEqual(replacement,anchor,`${id}: probe edit must change the source`);
  });
  return source.replace(anchor, replacement);
}
