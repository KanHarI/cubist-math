import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { cubistIndex, firstSentence, indexPath, indexText } from "../tools/cubist-files.mjs";
import { archiveModules, cubistTestModules, libraryModules } from "../web/cubist/modules.mjs";

// The Files page (web/files.html) lists web/cubist-files.json: every Cubist
// source the site publishes, each opening in the workspace by its path.
test("the file index lists every Cubist source the site publishes, with a summary", async () => {
  assert.equal(await readFile(indexPath, "utf8"), indexText(await cubistIndex()),
    "web/cubist-files.json is stale: run npm run files:index");
  const { files } = JSON.parse(await readFile(indexPath, "utf8"));
  for (const { path, summary } of files) assert.ok(summary, `${path} has a summary`);
});

// proof.mjs opens ?file=path as the module of its root, or, under docs/, as
// a source checked by the name its file gives.
test("every indexed file opens in the workspace by its path", async () => {
  const { roots, files } = JSON.parse(await readFile(indexPath, "utf8"));
  const lists = { library: libraryModules, "cubist-tests": cubistTestModules, archive: archiveModules };
  for (const { path } of files) {
    const root = path.split("/")[0], name = path.split("/").at(-1).replace(/\.cubist$/, "");
    assert.ok(roots.some(item => item.path === root), `${path} is under a listed root`);
    if (root === "docs") assert.match(path, /^docs\/(?:[\w-]+\/)*[\w-]+\.cubist$/, path);
    else {
      assert.equal(path, root === "archive" ? `archive/first-library/${name}.cubist` : `${root}/${name}.cubist`, path);
      assert.ok(lists[root].includes(name), `${name} is a listed module of ${root}`);
    }
  }
});

test("a summary is a file's first sentence, at most a line", () => {
  assert.equal(firstSentence("import a;\n\n// One. Two.\n// Three.\ndef x := 0;"), "One.");
  assert.equal(firstSentence("// The circle (see 3.2; 4.1): a type.\n// More."), "The circle (see 3.2; 4.1): a type.");
  assert.equal(firstSentence("def x := 0;"), "");
  assert.ok(firstSentence(`// ${"word ".repeat(80)}`).length <= 200);
});
