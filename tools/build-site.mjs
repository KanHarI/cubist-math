// Assemble the same static application used locally, without a runtime server.
// Only web/, the libraries (library/ and archive/) and public documentation enter the Pages artifact.
import { createHash } from "node:crypto";
import { cp, mkdir, readdir, readFile, rm, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { join, relative } from "node:path";

const root = fileURLToPath(new URL("../", import.meta.url));
const output = join(root, "build/site");
async function files(directory) {
  const result = [];
  for (const entry of await readdir(directory, { withFileTypes: true })) {
    const path = join(directory, entry.name);
    if (entry.isDirectory()) result.push(...await files(path));
    else if (entry.isFile() && entry.name !== ".DS_Store") result.push(path);
  }
  return result.sort();
}
// Hash filenames as well as bytes so renames/removals also invalidate imports.
const digest = createHash("sha256");
for (const path of [...await files(join(root, "web")), ...await files(join(root, "archive")), ...await files(join(root, "library")), ...await files(join(root, "docs"))]) {
  digest.update(relative(root, path));
  digest.update("\0");
  digest.update(await readFile(path));
}
const version = digest.digest("hex");
await rm(output, { recursive: true, force: true });
await mkdir(output, { recursive: true });
await cp(join(root, "web"), output, { recursive: true, filter: path => !path.endsWith(".DS_Store") });
await cp(join(root, "archive"), join(output, "archive"), { recursive: true, filter: path => !path.endsWith(".DS_Store") });
await cp(join(root, "library"), join(output, "library"), { recursive: true, filter: path => !path.endsWith(".DS_Store") });
await cp(join(root, "docs"), join(output, "docs"), { recursive: true });
for (const path of await files(output)) {
  if (path.endsWith(".mjs")) {
    let source = await readFile(path, "utf8");
    // Static imports, dynamic imports, and workers use the same build version.
    source = source.replace(
      /(\bfrom\s*|\bimport\s*(?:\(\s*)?)(["'])(\.\.?\/[^"'?]+\.mjs)\2/g,
      (_, prefix, quote, name) => `${prefix}${quote}${name}?version=${version}${quote}`,
    );
    // This also versions Emscripten's WASM URL, whose bytes must match its loader.
    source = source.replace(
      /(\bnew URL\(\s*)(["'])([^"'?]+\.(?:mjs|wasm))\2/g,
      (_, prefix, quote, name) => `${prefix}${quote}${name}?version=${version}${quote}`,
    );
    await writeFile(path, source);
  } else if (path.endsWith(".html")) {
    const source = (await readFile(path, "utf8")).replace(
      /\b(src|href)="([^"?:]+\.(?:mjs|css))"/g,
      (_, attribute, name) => `${attribute}="${name}?version=${version}"`,
    );
    await writeFile(path, source);
  }
}
await writeFile(join(output, "mathscript-version"), JSON.stringify({ version }) + "\n");
await writeFile(join(output, ".nojekyll"), "");
console.log(`Built build/site (${version.slice(0, 12)}).`);
