// Every .cubist source is kept formatted (tools/format-cubist.mjs): a pull
// request that changes one leaves it as the formatter writes it. Run
// npm run format:cubist to format them all.
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { relative } from "node:path";
import { fileURLToPath } from "node:url";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { cubistSources } from "../tools/cubist-sources.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));

test("every .cubist source is formatted", () => {
  const sources = cubistSources();
  assert.ok(sources.length > 100, "git lists the repository's .cubist sources");
  const unformatted = sources.filter(path => {
    const source = readFileSync(path, "utf8");
    return formatCubist(source) !== source;
  }).map(path => relative(root, path));
  assert.deepEqual(unformatted, [], "run npm run format:cubist to format these");
});
