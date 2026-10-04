// The index of every Cubist source the site publishes, for the Files page
// (web/files.html): each .cubist file under library/, archive/, cubist-tests/
// and docs/, by its path from the repository root, with a one-line summary.
//
//   node tools/cubist-files.mjs           write web/cubist-files.json
//   node tools/cubist-files.mjs --check   exit with status 1 when it is stale
//
// A summary is the module's row in its root's README where the root has one
// (library/, cubist-tests/), the proof catalog's title for an archive proof
// (web/proof-library.mjs), and otherwise the first sentence of the file's
// first comment. tests/cubist-files.test.mjs checks the index is current.
import { readFile, readdir, writeFile } from "node:fs/promises";
import { join, relative } from "node:path";
import { fileURLToPath } from "node:url";
import { proofCatalog } from "../web/proof-library.mjs";

const repository = fileURLToPath(new URL("../", import.meta.url));
export const indexPath = join(repository, "web/cubist-files.json");

// The roots, in the order the Files page lists them.
export const roots = [
  { path: "library", title: "Library",
    description: "The rebuilt library. Its modules come first wherever a source imports by name." },
  { path: "cubist-tests", title: "Cubist tests",
    description: "The Cubist sources the test suite checks. Each states its errors, warnings and outputs in comments." },
  { path: "archive", title: "Archive",
    description: "The first library, kept unchanged. Its modules import only from the archive." },
  { path: "docs", title: "Documentation examples",
    description: "The examples the documentation discusses, as files." },
];

async function cubistFiles(directory) {
  const found = [];
  for (const entry of await readdir(directory, { withFileTypes: true })) {
    const path = join(directory, entry.name);
    if (entry.isDirectory()) found.push(...await cubistFiles(path));
    else if (entry.isFile() && entry.name.endsWith(".cubist")) found.push(path);
  }
  return found;
}

// A README's module rows: | [`name`](name.cubist) | description | ….
async function readmeRows(root) {
  let text;
  try { text = await readFile(join(repository, root, "README.md"), "utf8"); } catch { return new Map(); }
  return new Map([...text.matchAll(/^\| \[`(\w+)`\]\(\1\.cubist\) \| (.*?) \|/gm)].map(([, name, cells]) => [name, cells.trim()]));
}

// The first sentence of a source's first comment, at most a line's length.
export function firstSentence(source) {
  const lines = source.split("\n");
  const start = lines.findIndex(line => line.startsWith("//"));
  if (start < 0) return "";
  let text = "";
  for (let i = start; i < lines.length && lines[i].startsWith("//"); i++) text += ` ${lines[i].replace(/^\/\/\s?/, "")}`;
  text = text.replace(/\s+/g, " ").trim();
  const end = text.search(/\.(\s|$)/);
  const sentence = end >= 0 ? text.slice(0, end + 1) : text;
  return sentence.length > 200 ? `${sentence.slice(0, 199)}…` : sentence;
}

export async function cubistIndex() {
  const titles = new Map(proofCatalog.map(entry => [entry.id, entry.title]));
  const files = [];
  for (const root of roots) {
    const rows = await readmeRows(root.path);
    for (const path of await cubistFiles(join(repository, root.path))) {
      const relativePath = relative(repository, path).split("\\").join("/");
      const name = relativePath.split("/").at(-1).slice(0, -".cubist".length);
      const summary = rows.get(name) ?? (root.path === "archive" ? titles.get(name) : null)
        ?? firstSentence(await readFile(path, "utf8"));
      files.push({ path: relativePath, summary });
    }
  }
  files.sort((a, b) => a.path.localeCompare(b.path));
  return { roots, files };
}

export const indexText = index => `${JSON.stringify(index, null, 1)}\n`;

if (process.argv[1]?.endsWith("cubist-files.mjs")) {
  const text = indexText(await cubistIndex());
  if (process.argv.includes("--check")) {
    let current = "";
    try { current = await readFile(indexPath, "utf8"); } catch {}
    if (current !== text) {
      console.log("web/cubist-files.json is stale: run npm run files:index.");
      process.exitCode = 1;
    }
  } else {
    await writeFile(indexPath, text);
    const { files } = JSON.parse(text);
    console.log(`Wrote web/cubist-files.json: ${files.length} files.`);
  }
}
