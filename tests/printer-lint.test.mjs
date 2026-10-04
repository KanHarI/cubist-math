import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { lint } from "../web/cubist/lint.mjs";
import { checkTestModule } from "./check-program.mjs";

// What the printer shows is source the linter accepts: each print of
// cubist-tests/printer_lint.cubist, whose comments state what it shows
// (tests/cubist-tests.test.mjs), lints clean as a definition's value.
test("printed terms and types pass the linter", async t => {
  const { result } = await checkTestModule(t, "printer_lint");
  assert.equal(result.prints.length, 20);
  for (const { name, text } of result.prints) {
    const warnings = lint(`def shown := ${text};`).map(warning => warning.message);
    assert.deepEqual(warnings, [], `${name} printed ${text}`);
  }
});
