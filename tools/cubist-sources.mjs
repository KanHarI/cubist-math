// Every .cubist source git tracks, as absolute paths, sorted: the sources
// the formatter keeps formatted (tools/format-cubist.mjs and
// tests/formatting.test.mjs).
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));

export function cubistSources() {
  return execFileSync("git", ["ls-files", "-z", "--", "*.cubist"], { cwd: root, encoding: "utf8" })
    .split("\0").filter(Boolean).sort().map(path => root + path);
}
