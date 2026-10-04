import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { cubistTestModules } from "../web/cubist/modules.mjs";

// The Cubist tests under cubist-tests/: every module is listed, so that the
// workspace opens it, and the README's table names each one.
test("every Cubist test module is listed, and the README names it", async () => {
  const files = (await readdir(new URL("../cubist-tests/", import.meta.url))).filter(name => name.endsWith(".cubist"))
    .map(name => name.slice(0, -".cubist".length)).sort();
  assert.deepEqual(files, [...cubistTestModules].sort());
  const readme = await readFile(new URL("../cubist-tests/README.md", import.meta.url), "utf8");
  for (const name of cubistTestModules) assert.ok(readme.includes(`[\`${name}\`](${name}.cubist)`), name);
});
