// The Files page: every Cubist source the site publishes, by folder, from
// cubist-files.json (written by tools/cubist-files.mjs). Selecting a file
// shows its source here; the workspace opens it by its path (?file=).
import { tokenPattern, tokenStyle, numeralAt } from "./source-tokens.mjs";
import { loadFileIndex, renderFileTree, filterTree, summaryNodes } from "./file-tree.mjs";

const $ = id => document.getElementById(id);
const index = await loadFileIndex();
const tree = renderFileTree($("tree"), index, {
  href: path => `files.html?path=${encodeURIComponent(path)}`,
  onSelect: path => select(path, true),
});
filterTree(tree, $("file-filter"), $("file-count"), index.files.length);
let selected = null;

const element = (tag, className, text) => {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
};

// A file's source, highlighted as the workspace highlights it.
function highlighted(source) {
  const fragment = document.createDocumentFragment();
  for (const match of source.matchAll(tokenPattern)) {
    const [text] = match, start = match.index;
    const style = text.startsWith("//") ? "comment" : tokenStyle(text, numeralAt(source, start, text));
    fragment.append(style ? element("span", style, text) : document.createTextNode(text));
  }
  return fragment;
}

async function select(path, remember) {
  if (!tree.summaries.has(path)) return;
  selected = path;
  tree.select(path);
  if (remember) history.pushState({ path }, "", `files.html?path=${encodeURIComponent(path)}`);
  $("file-empty").hidden = true;
  $("file-details").hidden = false;
  $("file-path").textContent = path.split("/").slice(0, -1).join("/") + "/";
  $("file-name").textContent = path.split("/").at(-1);
  $("file-summary").replaceChildren(...summaryNodes(tree.summaries.get(path) ?? ""));
  $("file-open").href = `proof.html?file=${encodeURIComponent(path)}`;
  $("file-raw").href = path;
  $("file-source").replaceChildren(document.createTextNode("Loading…"));
  try {
    const response = await fetch(path, { cache: "no-store" });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const source = await response.text();
    if (selected === path) $("file-source").replaceChildren(highlighted(source));
  } catch (error) {
    if (selected === path) $("file-source").replaceChildren(document.createTextNode(`Could not load ${path}: ${error.message}`));
  }
}

addEventListener("popstate", () => {
  const path = new URLSearchParams(location.search).get("path");
  if (path) select(path, false);
});
const initial = new URLSearchParams(location.search).get("path");
if (initial) select(initial, false);
