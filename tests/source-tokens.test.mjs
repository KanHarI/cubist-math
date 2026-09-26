import test from "node:test";
import assert from "node:assert/strict";
import { numeralExpansion, tokenStyle } from "../web/source-tokens.mjs";

test("numerals from 1 are notation for successors; 0 is the constructor itself", () => {
  assert.equal(numeralExpansion("3"), "succ(succ(succ(0)))");
  assert.equal(numeralExpansion("0"), null);
  assert.equal(numeralExpansion("257"), null);
  assert.equal(tokenStyle("3", numeralExpansion("3")), "macro");
  assert.equal(tokenStyle("0", numeralExpansion("0")), "");
  // A link whose expansion is the token itself is not notation either.
  assert.equal(tokenStyle("0", "0"), "");
  assert.equal(tokenStyle("(", "(1, (2, 3))"), "macro");
  assert.equal(tokenStyle("exact", null), "keyword");
});
