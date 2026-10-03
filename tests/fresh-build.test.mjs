// Every test file that loads web/dist imports tests/fresh-build.mjs first, so
// that it refuses a stale build even when run on its own, without
// tools/test.mjs. A file loads web/dist when a module it imports, through
// relative imports, lies there, or when it names ../web/dist/ itself, as a
// child script it runs does.
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));
const dist = join(root, "web/dist/");
const specifiers = source => [...source.matchAll(/(?:\bfrom\s*|\bimport\s*\(?\s*)["'`]([^"'`$]+)["'`]/g)].map(match => match[1]);

// The chain of imports from a file to a module in web/dist, or null.
function chainToDist(file, seen = new Set()) {
  if (file.startsWith(dist)) return [file];
  if (seen.has(file)) return null;
  seen.add(file);
  let source;
  try { source = readFileSync(file, "utf8"); } catch { return null; }
  for (const specifier of specifiers(source).filter(specifier => specifier.startsWith("."))) {
    const chain = chainToDist(resolve(dirname(file), specifier), seen);
    if (chain) return [file, ...chain];
  }
  return null;
}

// This file names web/dist only to look for it, and loads no build.
const testFiles = ["tests", "tests/translator"].flatMap(directory => readdirSync(join(root, directory))
  .filter(name => name.endsWith(".test.mjs")).map(name => join(root, directory, name)))
  .filter(file => file !== fileURLToPath(import.meta.url));
const loadsDist = file => chainToDist(file) !== null || /\.\.\/web\/dist\//.test(readFileSync(file, "utf8"));
const firstImport = file => specifiers(readFileSync(file, "utf8"))[0];

test("the analysis finds web/dist through direct imports, other modules and child scripts", () => {
  for (const name of ["tests/inductive-declarations.test.mjs", "tests/corpus.test.mjs", "tests/translator/translation.test.mjs"])
    assert.ok(chainToDist(join(root, name)), name);
  assert.ok(loadsDist(join(root, "tests/proof-ergonomics.test.mjs")));
  assert.ok(!loadsDist(join(root, "tests/build-stamp.test.mjs")), "the stamp's own tests load no build");
  // The translator is source in web/translator, not a build: its tests that
  // do not run the kernel load none.
  assert.ok(!loadsDist(join(root, "tests/display-names.test.mjs")), "the display's naming rules load no build");
  assert.ok(testFiles.filter(loadsDist).length >= 50, "most test files load web/dist");
});

test("every test file that loads web/dist checks the build first", () => {
  const missing = testFiles.filter(loadsDist).filter(file => {
    const expected = relative(dirname(file), join(root, "tests/fresh-build.mjs")).replace(/^(?!\.)/, "./");
    return firstImport(file) !== expected;
  });
  assert.deepEqual(missing.map(file => relative(root, file)), [],
    "Import tests/fresh-build.mjs first in these files.");
});
