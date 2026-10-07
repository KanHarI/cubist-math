import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import { archiveModules, cubistTestModules, libraryModules } from "../web/cubist/modules.mjs";
import { inlined, stated, stripped } from "../tools/inline-errors.mjs";
import { SHARDS } from "./cubist-tests-inlined.mjs";

// The Cubist tests under cubist-tests/: every module is listed, so that the
// workspace opens it, and the README's table names each one.
test("every Cubist test module is listed, and the README names it", async () => {
  const files = (await readdir(new URL("../cubist-tests/", import.meta.url))).filter(name => name.endsWith(".cubist"))
    .map(name => name.slice(0, -".cubist".length)).sort();
  assert.deepEqual(files, [...cubistTestModules].sort());
  const readme = await readFile(new URL("../cubist-tests/README.md", import.meta.url), "utf8");
  for (const name of cubistTestModules) assert.ok(readme.includes(`[\`${name}\`](${name}.cubist)`), name);
});

// A test module's name is its own: one shared with a library or archive
// module would stand for it in the imports of the other test modules.
test("no Cubist test module shares its name with a library or archive module", () => {
  const shadowed = cubistTestModules.filter(name => libraryModules.includes(name) || archiveModules.includes(name));
  assert.deepEqual(shadowed, []);
});

// Each module's inlined errors, warnings and outputs are checked in
// tests/cubist-tests-inlined-*.test.mjs, its modules shared among them: one
// file for each share, so that every module is checked.
test("each share of the Cubist test modules has its test file", async () => {
  const files = (await readdir(new URL("./", import.meta.url))).filter(name => /^cubist-tests-inlined-\d+\.test\.mjs$/.test(name)).sort();
  assert.deepEqual(files, Array.from({ length: SHARDS }, (_, k) => `cubist-tests-inlined-${k + 1}.test.mjs`).sort());
  for (const [k, file] of files.entries())
    assert.match(await readFile(new URL(file, import.meta.url), "utf8"), new RegExp(`inlinedShard\\(${Number(file.match(/\d+/)[0]) - 1}\\)`), file);
});

test("checked comments are written above their line, wrapped, and read back", () => {
  const source = "// A note.\ndef wrong := 1;\nprint(typeof(2));\n";
  const long = `E606: ${"word ".repeat(40).trim()}`;
  const items = [{ line: 1, label: "Error", text: long }, { line: 1, label: "Warning", text: "W703: k is unused." },
    { line: 2, label: "Output", text: "Nat" }];
  const text = inlined(source, items);
  assert.ok(text.split("\n").every(line => line.length <= 100));
  assert.match(text, /^\/\/ A note\.\n\/\/ Error: E606: word/);
  assert.match(text, /\n\/\/ Output: Nat\nprint\(typeof\(2\)\);\n$/);
  // Read back, each is at its line in the commented text.
  const lines = text.split("\n"), at = { 1: lines.indexOf("def wrong := 1;"), 2: lines.indexOf("print(typeof(2));") };
  assert.deepEqual(stated(text), items.map(item => ({ ...item, line: at[item.line] })));
  assert.equal(stripped(text), source);
});
