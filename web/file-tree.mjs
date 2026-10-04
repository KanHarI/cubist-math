// The folder tree of the Cubist sources the site publishes, from
// cubist-files.json (written by tools/cubist-files.mjs): the Files page shows
// it beside the selected file, and the proof workspace in its explorer.

export async function loadFileIndex() {
  const response = await fetch(new URL("cubist-files.json", import.meta.url), { cache: "no-store" });
  if (!response.ok) throw new Error(`Could not load the file index: HTTP ${response.status}`);
  return response.json();
}

const element = (tag, className, text) => {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
};

// A summary's Markdown, as the READMEs write it: `code` spans, and links
// whose text is kept.
export function summaryNodes(text) {
  const nodes = [];
  for (const part of text.replace(/\[([^\]]+)\]\([^)]+\)/g, "$1").split(/(`[^`]+`)/)) {
    if (!part) continue;
    nodes.push(part.startsWith("`") ? element("code", "", part.slice(1, -1)) : document.createTextNode(part));
  }
  return nodes;
}

// The tree of `index` in `container`: each root, its folders and its files,
// each file a link to href(path). onSelect(path, event), when given, is
// called on a plain click instead of following the link. Returns the tree's
// controls: select(path) marks a file current and opens the folders around
// it, filter(text) shows the files whose path contains the text.
export function renderFileTree(container, index, { href, onSelect = null }) {
  const summaries = new Map(index.files.map(file => [file.path, file.summary]));
  const root = { folders: new Map(), files: [] };
  for (const { path } of index.files) {
    let folder = root;
    for (const part of path.split("/").slice(0, -1)) {
      if (!folder.folders.has(part)) folder.folders.set(part, { folders: new Map(), files: [] });
      folder = folder.folders.get(part);
    }
    folder.files.push(path);
  }
  const count = folder => folder.files.length + [...folder.folders.values()].reduce((sum, inner) => sum + count(inner), 0);
  const folderNode = (name, folder, path, described) => {
    const details = element("details", "folder");
    details.dataset.path = path;
    const summary = element("summary");
    summary.append(element("span", "folder-name", described?.title ?? `${name}/`), element("span", "folder-count", String(count(folder))));
    details.append(summary);
    if (described) details.append(element("p", "folder-description", described.description));
    const list = element("ul");
    for (const [inner, child] of [...folder.folders].sort(([a], [b]) => a.localeCompare(b)))
      list.appendChild(element("li")).append(folderNode(inner, child, `${path}/${inner}`));
    for (const file of folder.files) {
      // A long name breaks after an underscore, between its words.
      const link = list.appendChild(element("li", "file")).appendChild(element("a"));
      for (const [i, word] of file.split("/").at(-1).replace(/\.cubist$/, "").split(/(?<=_)/).entries())
        link.append(...(i ? [element("wbr"), word] : [word]));
      link.href = href(file);
      link.dataset.path = file;
      link.title = summaries.get(file) ?? "";
      if (onSelect) link.onclick = event => {
        if (event.metaKey || event.ctrlKey || event.shiftKey || event.button) return;
        event.preventDefault();
        onSelect(file, event);
      };
    }
    details.append(list);
    return details;
  };
  for (const described of index.roots)
    if (root.folders.has(described.path)) container.append(folderNode(described.path, root.folders.get(described.path), described.path, described));
  const folders = () => [...container.querySelectorAll("details.folder")];
  return {
    summaries,
    select(path, { scroll = true } = {}) {
      for (const link of container.querySelectorAll("a[aria-current]")) link.removeAttribute("aria-current");
      const link = container.querySelector(`a[data-path="${CSS.escape(path)}"]`);
      if (!link) return null;
      link.setAttribute("aria-current", "page");
      for (const details of folders()) if (path.startsWith(`${details.dataset.path}/`)) details.open = true;
      if (scroll) link.scrollIntoView({ block: "nearest" });
      return link;
    },
    filter(text) {
      text = text.trim().toLowerCase();
      let shown = 0;
      for (const item of container.querySelectorAll("li.file")) {
        item.hidden = !!text && !item.firstChild.dataset.path.toLowerCase().includes(text);
        if (!item.hidden) shown++;
      }
      for (const details of folders().reverse()) {
        const visible = [...details.querySelectorAll("li.file")].some(item => !item.hidden);
        details.hidden = !visible;
        if (text) details.open = visible;
      }
      return shown;
    },
  };
}

// A filter box for a tree, with the count of the files it shows.
export function filterTree(tree, input, counter, total) {
  const update = () => {
    const text = input.value.trim(), shown = tree.filter(text);
    counter.textContent = text ? `${shown} of ${total} files` : `${total} files`;
  };
  input.addEventListener("input", update);
  update();
}
