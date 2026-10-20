// The kernel guide is a reference: every kernel identifier it names in code
// spans must exist in kernel/, so a renamed or invented function, field or
// constant fails here instead of misleading a reader.
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

test("every kernel identifier the guide names in code exists in kernel/", () => {
  const guide = readFileSync(join(root, "docs/guides/kernel.md"), "utf8");
  const named = new Set([...guide.matchAll(/`([^`\n]+)`/g)]
    .flatMap(match => match[1].match(/\b(?:cc|ck|CC)_[A-Za-z0-9_]+/g) ?? []));
  assert.ok(named.size > 100, `only ${named.size} identifiers found; the extraction is broken`);
  assert.deepEqual([...named].filter(name => !defined.has(name)).sort(), []);
});
