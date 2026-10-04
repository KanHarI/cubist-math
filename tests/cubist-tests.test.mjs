import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { archiveModules, cubistTestModules, libraryModules } from "../web/cubist/modules.mjs";
import { checkedModule, inlined, reported, stated, stripped } from "../tools/inline-errors.mjs";

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

// Each module's comments state every error and warning its check reports,
// each above the declaration or directive it belongs to, and nothing else:
// tools/inline-errors.mjs --write writes them.
test("each Cubist test module's inlined errors and warnings are the checker's", async () => {
  const module = await createCubical();
  for (const name of cubistTestModules) {
    const { source, result } = await checkedModule(name, module);
    assert.ok(result.outputs.length || result.evaluations.length, `${name} declares nothing`);
    const diagnostics = reported(source, result, name);
    assert.deepEqual(stated(source), diagnostics,
      `${name}: its diagnostic comments differ from the check; run node tools/inline-errors.mjs --write ${name}`);
    // Each has a code (web/diagnostics.mjs): one without is a message the
    // registry missed.
    for (const { text } of diagnostics) assert.match(text, /^[EKW]\d{3}: /, `${name}: no code for "${text}"`);
  }
});

test("diagnostic comments are written above their line, wrapped, and read back", () => {
  const source = "// A note.\ndef wrong := 1;\ndef right := 2;\n";
  const long = `E606: ${"word ".repeat(40).trim()}`;
  const items = [{ line: 1, label: "Error", text: long }, { line: 1, label: "Warning", text: "W703: k is unused." }];
  const text = inlined(source, items);
  assert.ok(text.split("\n").every(line => line.length <= 100));
  assert.match(text, /^\/\/ A note\.\n\/\/ Error: E606: word/);
  // Read back, each is at the declaration's line in the commented text.
  const line = text.split("\n").indexOf("def wrong := 1;");
  assert.deepEqual(stated(text), items.map(item => ({ ...item, line })));
  assert.equal(stripped(text), source);
});
