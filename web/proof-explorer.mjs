// The proof workspace's explorer: every Cubist source the site publishes, by
// folder (file-tree.mjs), beside the workspace. A file opens in the workspace
// by its path (?file=), and the source open now is marked current. Whether
// the explorer is open is kept per browser (proof.html reads it before the
// page paints); its filter and its open folders are kept per tab, so they
// stay as they were while files open one after another.
import { loadFileIndex, renderFileTree, filterTree } from "./file-tree.mjs";

const openKey = "cubist.explorer.open", filterKey = "cubist.explorer.filter", foldersKey = "cubist.explorer.folders";
const read = (storage, key) => { try { return storage.getItem(key); } catch { return null; } };
const write = (storage, key, value) => { try { storage.setItem(key, value); } catch { /* Storage is a convenience. */ } };

// `current`: the open source's path from the site's root, or null.
export async function showExplorer(current) {
  const $ = id => document.getElementById(id);
  const explorer = $("explorer"), toggle = $("explorer-toggle"), body = $("explorer-body");
  const show = open => {
    explorer.classList.toggle("collapsed", !open);
    toggle.setAttribute("aria-expanded", String(open));
    toggle.title = open ? "Hide the files" : "Show the files";
  };
  // The current file, in the middle of the explorer's scrolled list.
  const reveal = () => {
    const link = $("explorer-tree").querySelector("a[aria-current]");
    if (link && !explorer.classList.contains("collapsed"))
      body.scrollTop += link.getBoundingClientRect().top - body.getBoundingClientRect().top - body.clientHeight / 2;
  };
  show(!explorer.classList.contains("collapsed"));
  toggle.onclick = () => {
    const open = explorer.classList.contains("collapsed");
    show(open);
    write(localStorage, openKey, String(open));
    if (open) reveal();
  };

  const index = await loadFileIndex();
  const tree = renderFileTree($("explorer-tree"), index, { href: path => `proof.html?file=${encodeURIComponent(path)}` });
  let opened = [];
  try { opened = JSON.parse(read(sessionStorage, foldersKey) ?? "[]"); } catch { /* A fresh tab's folders start closed. */ }
  for (const details of $("explorer-tree").querySelectorAll("details.folder"))
    if (opened.includes(details.dataset.path)) details.open = true;
  $("explorer-filter").value = read(sessionStorage, filterKey) ?? "";
  $("explorer-filter").addEventListener("input", () => write(sessionStorage, filterKey, $("explorer-filter").value));
  filterTree(tree, $("explorer-filter"), $("explorer-count"), index.files.length);
  if (current) tree.select(current, { scroll: false });
  // A folder's toggle event does not bubble; it is caught on its way down.
  $("explorer-tree").addEventListener("toggle", () => write(sessionStorage, foldersKey, JSON.stringify(
    [...$("explorer-tree").querySelectorAll("details.folder[open]")].map(details => details.dataset.path))), true);
  reveal();
}
