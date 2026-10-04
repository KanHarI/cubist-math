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
// and what each print directive shows, each above the declaration or
// directive it belongs to, and nothing else: tools/inline-errors.mjs --write
// writes them.
test("each Cubist test module's inlined errors, warnings and outputs are the checker's", async () => {
  const module = await createCubical();
  for (const name of cubistTestModules) {
    const { source, result } = await checkedModule(name, module);
    assert.ok(result.outputs.length || result.evaluations.length || result.prints.length, `${name} declares nothing`);
    const items = reported(source, result, name);
    assert.deepEqual(stated(source), items,
      `${name}: its checked comments differ from the check; run node tools/inline-errors.mjs --write ${name}`);
    // Each diagnostic has a code (web/diagnostics.mjs): one without is a
    // message the registry missed.
    for (const { label, text } of items)
      if (label !== "Output") assert.match(text, /^[EKW]\d{3}: /, `${name}: no code for "${text}"`);
  }
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
