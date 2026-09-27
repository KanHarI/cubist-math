import test from "node:test";
import assert from "node:assert/strict";
import { readFile, readdir, access } from "node:fs/promises";
import { dirname, join, normalize } from "node:path";
import { fileURLToPath } from "node:url";
import { decode, referenceExamples, statedErrors } from "./reference-pages.mjs";

// The language reference is an index page plus one page per chapter. These
// tests keep its navigation consistent and every link and anchor working.
const web = fileURLToPath(new URL("../web/", import.meta.url));
const repository = fileURLToPath(new URL("../", import.meta.url));
const read = path => readFile(join(web, path), "utf8");
const ids = html => new Set([...html.matchAll(/\sid="([^"]+)"/g)].map(([, id]) => id));
const hrefs = html => [...html.matchAll(/\shref="([^"]+)"/g)].map(([, href]) => href.replace(/&amp;/g, "&"));
const chapterFiles = async () => (await readdir(join(web, "reference"))).filter(name => name.endsWith(".html"));
const indexOrder = index => [...index.matchAll(/<li><a href="reference\/([a-z-]+)\.html">/g)].map(([, file]) => `${file}.html`);

test("every chapter is listed once, in the same order, on the index and on each chapter", async () => {
  const index = await read("language.html"), order = indexOrder(index);
  assert.deepEqual([...order].sort(), (await chapterFiles()).sort(), "the index lists exactly the chapter pages");
  for (const [position, file] of order.entries()) {
    const page = await read(`reference/${file}`);
    const listed = [...page.slice(page.indexOf('<ol class="chapters">'), page.indexOf("</ol>", page.indexOf('<ol class="chapters">')))
      .matchAll(/<a href="([a-z-]+\.html)"/g)].map(([, href]) => href);
    assert.deepEqual(listed, order, `${file} lists the chapters in index order`);
    assert.match(page, new RegExp(`<li class="current"><a href="${file}" aria-current="page">`), `${file} marks itself current`);
    assert.match(page, new RegExp(`CHAPTER ${position + 1}</p>`), `${file} is chapter ${position + 1}`);
    const pager = page.slice(page.indexOf('<nav class="pager"'));
    const previous = pager.match(/class="previous" href="([^"]+)"/)?.[1], next = pager.match(/class="next" href="([^"]+)"/)?.[1];
    assert.equal(previous, order[position - 1], `${file} links back to the previous chapter`);
    assert.equal(next, order[position + 1], `${file} links on to the next chapter`);
  }
});

test("every link in the reference and the quick reference resolves, including its anchor", async () => {
  const pages = ["language.html", "proof.html", ...(await chapterFiles()).map(file => `reference/${file}`)];
  const cache = new Map(), problems = [];
  const idsOf = async path => {
    if (!cache.has(path)) cache.set(path, ids(await read(path)));
    return cache.get(path);
  };
  for (const page of pages) {
    for (const href of hrefs(await read(page))) {
      if (/^(https?:|mailto:)/.test(href)) continue;
      const [target, anchor] = href.split("#");
      const path = target ? normalize(join(dirname(page), target.split("?")[0])) : page;
      if (path.startsWith("..")) continue; // Links outside web/, such as the repository.
      // The site serves the documentation and the archived library from the repository root.
      const root = /^(docs|archive)\//.test(path) ? repository : web;
      try { await access(join(root, path)); } catch { problems.push(`${page}: ${href} (no file ${path})`); continue; }
      if (anchor && path.endsWith(".html") && !(await idsOf(path)).has(anchor))
        problems.push(`${page}: ${href} (no id ${anchor} in ${path})`);
    }
  }
  assert.deepEqual(problems, []);
});

test("anchors of the former single-page reference redirect to their chapters", async () => {
  const index = await read("language.html");
  const moved = JSON.parse(index.match(/const moved = (\{[\s\S]*?\});/)[1]);
  // Links to these sections of the old page may exist outside this repository.
  const formerAnchors = ["first-proof", "files", "declarations", "types", "expressions", "w-types", "blocks",
    "induction", "paths", "equational", "rfl", "calc", "rw", "simp", "simpa", "simp-types", "simp-registration",
    "simp-conditional", "cubical", "cubical-shorthand", "dependent-paths", "ext", "suspensions", "axioms",
    "conversion", "computability", "computable", "evaluate", "inspection", "errors"];
  assert.deepEqual(Object.keys(moved).sort(), [...formerAnchors].sort());
  for (const [anchor, target] of Object.entries(moved)) {
    const [path, id] = target.split("#");
    assert.ok(ids(await read(path)).has(id), `${anchor} redirects to ${target}, which exists`);
  }
});

test("the error chapter catalogues exactly the errors that the examples show", async () => {
  const catalogue = [...(await read("reference/errors.html")).matchAll(/data-message="([^"]*)"/g)].map(([, message]) => decode(message));
  const stated = new Set();
  for (const page of ["language.html", ...(await chapterFiles()).map(file => `reference/${file}`)])
    for (const example of referenceExamples(page, await read(page)))
      if (example.attrs["data-check"] === "reject") for (const error of statedErrors(example.text)) stated.add(error);
  // Each catalogued message is shown by a checked example, and each shown error is catalogued.
  const unshown = catalogue.filter(message => ![...stated].some(error => error.includes(message)));
  const uncatalogued = [...stated].filter(error => !catalogue.some(message => error.includes(message)));
  assert.deepEqual({ unshown, uncatalogued }, { unshown: [], uncatalogued: [] });
});
