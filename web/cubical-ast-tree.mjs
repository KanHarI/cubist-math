// A bounded native tree: one level per request, with occurrence paths rather
// than handle identities. No literal sugar or definition-body expansion.
export function renderNativeTree(container, tree, { path, load, select }) {
  const doc = container.ownerDocument;
  const branch = (node, role, path, children = null) => {
    const item = doc.createElement("li"), hasChildren = node.operands.some(operand => operand.handle);
    const details = hasChildren ? doc.createElement("details") : null;
    const line = doc.createElement(hasChildren ? "summary" : "div");
    line.className = "native-tree-node"; line.dataset.path = JSON.stringify(path);
    const label = doc.createElement("span");
    label.textContent = `${role ? role + ": " : ""}${node.mnemonic} · %${node.id} · payload=${node.payload}`
      + (node.annotation ? ` · ${node.annotation}` : "");
    const focus = doc.createElement("button");
    focus.textContent = "Select"; focus.title = "Select this occurrence for a kernel operation";
    focus.onclick = event => { event.preventDefault(); event.stopPropagation(); select(path); };
    line.append(label, focus);
    if (!details) { item.append(line); return item; }
    const list = doc.createElement("ul");
    let loaded = false, loading = false;
    const show = children => {
      list.replaceChildren(...children.flatMap((child, index) =>
        child ? [branch(child, node.operands[index].label, [...path, index])] : []));
      loaded = true;
    };
    details.append(line, list); item.append(details);
    if (children) { show(children); details.open = true; }
    details.ontoggle = async () => {
      if (!details.open || loaded || loading) return;
      loading = true; list.textContent = "Loading native operands…";
      try { show((await load(path)).children); }
      catch (error) { list.textContent = `${error.message} Close and reopen this branch to retry.`; }
      finally { loading = false; }
    };
    return item;
  };
  const list = doc.createElement("ul");
  list.className = "native-tree";
  list.append(branch(tree.root, "", path, tree.children));
  container.replaceChildren(list);
}
