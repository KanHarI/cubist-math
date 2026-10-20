// The kernel guide and the kernel chapters of the language reference are
// references: every kernel identifier they name in code spans must exist in
// kernel/, so a renamed or invented function, field or constant fails here
// instead of misleading a reader.
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));
const sources = ["kernel/include", "kernel/src"].flatMap(directory =>
  readdirSync(join(root, directory)).filter(name => /\.[ch]$/.test(name))
    .map(name => readFileSync(join(root, directory, name), "utf8"))).join("\n");
const defined = new Set(sources.match(/\b(?:cc|ck|CC)_[A-Za-z0-9_]+/g));

const identifiers = spans => new Set(spans.flatMap(span => span.match(/\b(?:cc|ck|CC)_[A-Za-z0-9_]+/g) ?? [])
  // A family named by its prefix, as `cc_instr_…`, is not one identifier.
  .filter(name => !name.endsWith("_")));

test("every kernel identifier the guide names in code exists in kernel/", () => {
  const guide = readFileSync(join(root, "docs/guides/kernel.md"), "utf8");
  const named = identifiers([...guide.matchAll(/`([^`\n]+)`/g)].map(match => match[1]));
  assert.ok(named.size > 100, `only ${named.size} identifiers found; the extraction is broken`);
  assert.deepEqual([...named].filter(name => !defined.has(name)).sort(), []);
});

test("every kernel identifier the kernel chapters name in code exists in kernel/", () => {
  const chapters = readdirSync(join(root, "web/reference")).filter(name => /^kernel-.*\.html$/.test(name)).sort();
  assert.equal(chapters.length, 4, "the four kernel chapters");
  const decode = text => text.replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");
  let total = 0;
  for (const chapter of chapters) {
    const page = readFileSync(join(root, "web/reference", chapter), "utf8");
    const named = identifiers([...page.matchAll(/<code>([^<]*)<\/code>/g)].map(match => decode(match[1])));
    total += named.size;
    assert.deepEqual([...named].filter(name => !defined.has(name)).sort(), [], chapter);
  }
  assert.ok(total > 60, `only ${total} identifiers found in the chapters; the extraction is broken`);
});
