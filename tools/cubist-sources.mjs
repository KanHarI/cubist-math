// Every .cubist source in the working tree that git does not ignore, as
// absolute paths, sorted: the sources the formatter keeps formatted
// (tools/format-cubist.mjs and tests/formatting.test.mjs). A new source
// counts before it is added; a tracked one deleted from the tree does not.
import { execFileSync } from "node:child_process";
import { existsSync } from "node:fs";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));

export function cubistSources() {
  const listed = execFileSync("git", ["ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.cubist"],
    { cwd: root, encoding: "utf8" }).split("\0").filter(Boolean);
  return [...new Set(listed)].sort().map(path => root + path).filter(path => existsSync(path));
}
