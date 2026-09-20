import proofs from "./proofs/catalogue.mjs";
import { readWorkbenchTransfer, removeWorkbenchTransfer } from "./workbench-transfer.mjs";
import { validatedProofURL } from "./proof-navigation.mjs";
import {
  layout,
  roles,
  pathFromNames,
  pathFromMarked,
  atPath,
} from "./expressions.mjs";
const $ = (id) => document.getElementById(id);
function setProofReturn(value) {
  const address = value && validatedProofURL(value);
  $("back-mathscript").hidden = !address;
  if (address) $("back-mathscript").href = address;
}
setProofReturn(history.state?.proofReturn);
let worker,
  sequence = 0,
  state,
  metadata = [],
  active = null,
  view = null,
  selection = null,
  draft = null;
let expandedSides = [];
const pending = new Map();
const navigation = [];
function error(e) {
  $("error").hidden = false;
  $("error").textContent = e.message || String(e);
}
function clearError() {
  $("error").hidden = true;
}
function updateBusy() {
  document.body.classList.toggle("busy", pending.size > 0);
  $("status").textContent = pending.size ? "Checking…" : "WASM ready";
}
function request(command, args = {}) {
  clearError();
  if (command.startsWith("preview")) {
    draft = null;
    $("preview").hidden = true;
  }
  const id = ++sequence;
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      failWorker(
        new Error(
          "Operation timed out. Reset the example to restart the worker.",
        ),
      );
    }, 30000);
    pending.set(id, { resolve, reject, timer });
    updateBusy();
    worker.postMessage({ id, command, args });
  });
}
function failWorker(e) {
  worker.terminate();
  for (const p of pending.values()) {
    clearTimeout(p.timer);
    p.reject(e);
  }
  pending.clear();
  $("status").textContent = "Worker stopped";
  error(e);
}
function start() {
  worker = new Worker(new URL("./worker.mjs", import.meta.url), {
    type: "module",
  });
  worker.onerror = (e) =>
    failWorker(
      new Error(
        e.message || "Unable to start the WASM worker. Build with make wasm.",
      ),
    );
  worker.onmessage = async ({ data }) => {
    if (data.ready) {
      metadata = data.metadata;
      state = data.state;
      renderState();
      try {
        const transfer = new URLSearchParams(location.search).get("transfer");
        if (transfer) {
          const payload = await readWorkbenchTransfer(transfer);
          if (!payload.selection || !["expression", "type"].includes(payload.selection.side))
            throw new Error("Invalid expression transfer selection");
          await move("import", { document: payload.document, adoptPolicy: true });
          await choose(payload.selection.name);
          selection = { side: payload.selection.side, path: [] };
          await removeWorkbenchTransfer(transfer);
          const address = new URL(location.href);
          address.searchParams.delete("transfer");
          const proofReturn = payload.proofReturn && validatedProofURL(payload.proofReturn);
          history.replaceState({ proofReturn }, "", address);
          setProofReturn(proofReturn);
        } else {
          await choose("nested");
          selection = { side: "expression", path: [1] };
        }
        renderInspector();
      } catch (e) {
        error(e);
      }
      return;
    }
    const p = pending.get(data.id);
    if (!p) return;
    pending.delete(data.id);
    clearTimeout(p.timer);
    updateBusy();
    if (data.error) {
      const e = new Error(data.error.message);
      e.details = data.error.details;
      p.reject(e);
    } else p.resolve(data.result);
  };
}
function option(select, value, label) {
  const o = document.createElement("option");
  o.value = value;
  o.textContent = label;
  select.append(o);
}
function fillBindings(select, kind, optional = false) {
  const old = select.value;
  select.replaceChildren();
  if (optional) option(select, "_", "— none —");
  for (const b of state.bindings.filter(
    (b) => b.kind === kind && (!b.hidden || $("show-intermediate").checked),
  ))
    option(select, b.name, b.name);
  if ([...select.options].some((o) => o.value === old)) select.value = old;
}
function renderState() {
  $("axioms").checked = state.allowAxioms;
  const visible = state.bindings.filter(
    (b) => !b.hidden || b.name === active || $("show-intermediate").checked,
  );
  const filter = $("filter").value.toLowerCase();
  const listed = visible.filter(
    (b) => b.name === active || b.name.toLowerCase().includes(filter),
  );
  $("object-count").textContent =
    `${listed.length.toLocaleString()} / ${state.bindings.length.toLocaleString()}`;
  $("object-count").title = "Displayed objects / all loaded proof steps";
  const hidden = state.bindings.length - visible.length;
  $("loaded-steps").textContent =
    `All ${state.bindings.length.toLocaleString()} steps loaded.${hidden ? ` ${hidden.toLocaleString()} intermediate steps hidden.` : ""}`;
  $("objects").replaceChildren();
  for (const b of listed) {
    const button = document.createElement("button");
    button.className = "object" + (b.name === active ? " active" : "");
    button.dataset.name = b.name;
    button.append(document.createTextNode(b.name));
    const small = document.createElement("small");
    small.textContent = b.axiom
      ? "AXIOM"
      : b.kind === "context"
        ? "ASSUMPTION"
        : "JUDGEMENT";
    button.append(small);
    button.onclick = () => choose(b.name).catch(error);
    $("objects").append(button);
  }
  $("history").replaceChildren();
  for (const r of state.history) {
    const b = document.createElement("button");
    b.className = "history-item" + (r.id === state.revision ? " active" : "");
    const n = document.createElement("span");
    n.textContent = `${r.id} ← ${r.parent ?? "–"}`;
    b.append(n, document.createTextNode(r.title));
    b.onclick = () => move("checkout", { revision: r.id }).catch(error);
    $("history").append(b);
  }
  $("source").textContent = state.source || "# Empty proof";
  $("stats").replaceChildren();
  for (const [key, value] of Object.entries(state.stats)) {
    const dt = document.createElement("dt"),
      dd = document.createElement("dd");
    dt.textContent = key;
    dd.textContent =
      key === "bytes"
        ? `${(value / 1048576).toFixed(2)} MiB`
        : value.toLocaleString();
    $("stats").append(dt, dd);
  }
  const old = $("opcode").value;
  $("opcode").replaceChildren();
  for (const m of metadata) option($("opcode"), m.name, m.name);
  if (old) $("opcode").value = old;
  else $("opcode").value = "PiElim";
  renderOperands();
  fillBindings($("witness"), "judgement");
  fillBindings($("proposition"), "judgement");
  fillBindings($("proof"), "judgement");
  $("undo").disabled = state.revision === 0;
  updateBusy();
}
async function choose(name, navigating = false, expand = []) {
  if (!navigating) navigation.length = 0;
  active = name;
  selection = null;
  const inspected = await request("inspect", { name, expand });
  if (active !== name) return;
  view = inspected;
  expandedSides = [...expand];
  renderState();
  renderInspector();
}
async function expandView(side, expand = true) {
  const name = active;
  const sides = expandedSides.filter((s) => s !== side);
  if (expand) sides.push(side);
  const inspected = await request("inspect", { name, expand: sides });
  if (active !== name) return;
  view = inspected;
  expandedSides = sides;
  // Collapsing may hide the previously selected occurrence.
  if (!expand && selection?.side === side) selection = null;
  renderInspector();
}
function navigate(name) {
  navigation.push({
    name: active,
    selection,
    expandedSides: [...expandedSides],
  });
  return choose(name, true).then(() => $("active-name").focus());
}
function objectLink(name) {
  const button = document.createElement("button");
  button.textContent = name;
  button.onclick = () => navigate(name).catch(error);
  return button;
}
function renderDerivation() {
  $("checked-judgement").replaceChildren();
  $("checked-judgement").hidden = !view?.propositions.length;
  for (const proposition of view?.propositions || []) {
    const line = document.createElement("div");
    line.append(
      "Verified closed judgement: ",
      document.createTextNode(`${active} : `),
      objectLink(proposition),
    );
    $("checked-judgement").append(line);
  }
  $("inference").replaceChildren();
  const step = view?.inference;
  if (!step) return;
  $("inference").append(document.createTextNode(`Inferred by ${step.op}`));
  const inputs = [...step.args, step.context, ...step.free].filter(Boolean);
  if (inputs.length) {
    $("inference").append(document.createTextNode(" from "));
    inputs.forEach((name, i) => {
      if (i) $("inference").append(document.createTextNode(", "));
      $("inference").append(objectLink(name));
    });
  }
}
function renderTree(container, tree, side) {
  container.replaceChildren();
  if (!tree) {
    container.textContent = "—";
    return;
  }
  const { text, spans } = layout(tree, view.contextNames, view.referenceNames),
    byPath = new Map(spans.map((s) => [JSON.stringify(s.path), s]));
  function build(path) {
    const range = byPath.get(JSON.stringify(path)),
      n = range.node,
      el = document.createElement("span");
    el.className = "term";
    el.tabIndex = 0;
    el.setAttribute("role", "button");
    el.dataset.side = side;
    el.dataset.path = path.join(".");
    el.title = `${n.kind} #${n.parameter} · ${side}${path.map((i) => "." + i).join("")}`;
    const declaration = view.declarations[n.id];
    const target = declaration !== active ? declaration : null;
    if (target) {
      el.classList.add("reference");
      el.dataset.declaration = target;
      el.setAttribute("role", "link");
      el.title = `Open ${n.kind === "Axiom" ? "axiom declaration" : "definition"}: ${target}. Shift-click to select.`;
    }
    if (n.truncated) {
      el.classList.add("truncated");
      el.title = `Show full ${side}; omitted here for readability, fully checked by the kernel.`;
    }
    el.setAttribute("aria-label", el.title);
    if (
      selection?.side === side &&
      JSON.stringify(selection.path) === JSON.stringify(path)
    )
      el.classList.add("selected");
    let cursor = range.start;
    for (let i = 0; i < n.children.length; i++) {
      const child = byPath.get(JSON.stringify([...path, i]));
      el.append(
        document.createTextNode(text.slice(cursor, child.start)),
        build([...path, i]),
      );
      cursor = child.end;
    }
    el.append(document.createTextNode(text.slice(cursor, range.end)));
    const select = (e) => {
      e.stopPropagation();
      if (n.truncated) {
        error(
          new Error("This view is truncated. Select an enclosing subtree."),
        );
        return;
      }
      selection = { side, path };
      renderInspector();
      document.querySelector(".term.selected")?.focus({ preventScroll: true });
    };
    const activate = (e) => {
      if (n.truncated) {
        e.stopPropagation();
        expandView(side).catch(error);
      } else if (target && !e.shiftKey) {
        e.stopPropagation();
        navigate(target).catch(error);
      } else select(e);
    };
    el.onclick = activate;
    el.onkeydown = (e) => {
      if (e.key === "Enter" || e.key === " ") {
        e.preventDefault();
        activate(e);
      }
    };
    return el;
  }
  container.append(build([]));
}
function renderInspector() {
  $("back-reference").hidden = navigation.length === 0;
  renderDerivation();
  for (const side of ["expression", "type"]) {
    const tree = view?.[side];
    const truncated = (n) => n && (n.truncated || n.children.some(truncated));
    const omitted = truncated(tree);
    $(side + "-limit").textContent = omitted
      ? `Abbreviated view of ${tree.size.toLocaleString()} nodes. … hides display content, not unchecked proof steps.`
      : "";
    $("expand-" + side).hidden = !omitted && !expandedSides.includes(side);
    $("expand-" + side).textContent = expandedSides.includes(side)
      ? `Collapse ${side}`
      : `Show full ${side}`;
  }
  if (!view) {
    $("active-name").textContent = "Choose an object";
    $("expression").replaceChildren();
    $("type").replaceChildren();
    $("kernel-context").replaceChildren();
    return;
  }
  $("active-name").textContent = view.displayNames?.[active] ?? active;
  $("active-name").dataset.binding = active;
  $("active-name").title = active;
  $("clear").disabled = !selection && !view.focus?.side;
  $("clear").title = view.focus?.side
    ? "Preview the kernel UnHigh operation on this focused judgement"
    : "Clear the selected highlight without changing the checked term";
  $("object-kind").textContent = view.axiom ? "explicit axiom" : view.kind;
  renderTree($("expression"), view.expression, "expression");
  renderTree($("type"), view.type, "type");
  $("kernel-context").replaceChildren();
  if (!view.context?.length) $("kernel-context").textContent = "Empty context";
  for (const entry of view.context ?? []) {
    const row = document.createElement("div");
    row.dataset.name = entry.name;
    const name = document.createElement("button");
    name.className = "reference";
    name.textContent = entry.name;
    name.title = `Context ${entry.id} · ${entry.binding}`;
    name.onclick = () => navigate(entry.binding).catch(error);
    const type = document.createElement("span");
    const rendered = layout(entry.type, view.contextNames, view.referenceNames);
    let cursor = 0;
    for (const span of rendered.spans.filter(span => !span.node.children.length).sort((a, b) => a.start - b.start)) {
      const node = span.node;
      const target = ["CRef", "UCRef"].includes(node.kind)
        ? view.context.find(row => row.id === node.parameter)?.binding : view.declarations[node.id];
      if (!target) continue;
      const link = objectLink(target);
      link.className = "reference";
      link.textContent = rendered.text.slice(span.start, span.end);
      link.dataset.declaration = target;
      link.title = `Inspect ${target}`;
      type.append(document.createTextNode(rendered.text.slice(cursor, span.start)), link);
      cursor = span.end;
    }
    type.append(document.createTextNode(rendered.text.slice(cursor)));
    row.append(name, document.createTextNode(" : "), type);
    $("kernel-context").append(row);
  }
  $("used-axioms").replaceChildren();
  if (!view.axioms.length) $("used-axioms").textContent = "None";
  for (const [index, name] of view.axioms.entries()) {
    if (index) $("used-axioms").append(document.createTextNode(", "));
    const button = document.createElement("button");
    button.textContent = view.displayNames?.[name] ?? name;
    button.title = name;
    button.onclick = () => navigate(name).catch(error);
    $("used-axioms").append(button);
  }
  $("assumptions").textContent =
    view.assumptions.map((c) => view.contextNames[c.id] ?? c.names.join(" / ") ?? `c${c.id}`).join(", ") ||
    "None — closed";
  let selected = null;
  if (selection) selected = atPath(view[selection.side], selection.path);
  $("selection-label").textContent = selection
    ? `${selection.side}${selection.path.map((i) => "." + i).join("")}`
    : "No selection";
  $("selected-kind").textContent = selected
    ? `${selected.kind} · ${selected.size ?? "?"} tree nodes`
    : "Select part of an expression or its type.";
  const usable = selected && view.kind === "judgement";
  $("reduce").disabled = !usable || !selected.reducible;
  $("pass").disabled = !usable;
  $("unfold").disabled = !usable || !selected.unfoldable;
  $("rewrite").disabled = !usable;
  $("parent").disabled = !selection?.path.length;
}
function renderOperands() {
  const m = metadata.find((m) => m.name === $("opcode").value);
  $("operands").replaceChildren();
  if (!m) return;
  const add = (id, label, kind, optional) => {
    const l = document.createElement("label");
    l.htmlFor = id;
    l.textContent = label;
    const s = document.createElement("select");
    s.id = id;
    fillBindings(s, kind, optional);
    $("operands").append(l, s);
  };
  for (let i = 0; i < m.judgements; i++)
    add(`premise-${i}`, `Premise ${i + 1}`, "judgement", false);
  if (m.context) add("context-arg", "Injected context", "context", false);
  for (let i = 0; i < m.free; i++)
    add(
      `free-${i}`,
      m.name === "CtxExt"
        ? "Previous context (counter)"
        : `Optional context ${i + 1}`,
      "context",
      true,
    );
}
function showPreview(p) {
  draft = p;
  $("preview").hidden = false;
  $("preview-result").textContent = layout(
    p.result.expression || p.result.type,
    p.result.contextNames,
    p.result.referenceNames,
  ).text;
  $("preview-type").textContent =
    "Type: " + layout(p.result.type, p.result.contextNames, p.result.referenceNames).text;
  $("preview-code").textContent = p.source;
  $("preview-time").textContent =
    `${p.milliseconds.toFixed(1)} ms including replay`;
  $("preview").scrollIntoView({ block: "nearest", behavior: "smooth" });
}
async function focused(operation) {
  if (!selection) throw new Error("Select a subexpression.");
  showPreview(
    await request("previewFocus", {
      name: active,
      ...selection,
      operation,
      witness: $("witness").value,
      resultName: $("result-name").value.trim(),
    }),
  );
}
async function move(command, args = {}) {
  state = await request(command, args);
  navigation.length = 0;
  $("verification").textContent = "";
  draft = null;
  $("preview").hidden = true;
  renderState();
  const name = state.bindings.filter((b) => !b.hidden).at(-1)?.name;
  if (name) await choose(name);
  else {
    active = null;
    view = null;
    selection = null;
    renderInspector();
  }
}
function bind(id, fn) {
  $(id).onclick = () => Promise.resolve().then(fn).catch(error);
}
bind("back-reference", async () => {
  const previous = navigation.pop();
  if (!previous) return;
  await choose(previous.name, true, previous.expandedSides);
  selection = previous.selection;
  renderInspector();
  $("active-name").focus();
});
for (const side of ["expression", "type"])
  bind("expand-" + side, () => expandView(side, !expandedSides.includes(side)));
bind("reduce", () => focused("BetaReducePointed"));
bind("pass", () => focused("BetaReduceGrossKnuth"));
bind("unfold", () => focused("DefReducePointed"));
bind("rewrite", () => focused("HighSubs"));
bind("accept", async () => {
  const name = draft.result.name;
  await move("accept", { token: draft.token });
  await choose(name);
  $("result-name").value = name + "_next";
});
bind("reject", async () => {
  await request("discard");
  draft = null;
  $("preview").hidden = true;
});
bind("undo", () => move("undo"));
bind("clear", async () => {
  if (view?.focus?.side) {
    showPreview(await request("previewFocus", { name: active, operation: "UnHigh",
      resultName: $("result-name").value.trim() || "unhighlighted" }));
    return;
  }
  selection = null;
  renderInspector();
});
bind("parent", () => {
  selection.path = selection.path.slice(0, -1);
  renderInspector();
});
bind("select-path", () => {
  if (!view) throw new Error("Choose an object.");
  const [head, ...parts] = $("path").value.trim().split(".");
  if (!["expr", "expression", "type"].includes(head))
    throw new Error("Start a path with expr or type.");
  const side = head === "type" ? "type" : "expression";
  selection = { side, path: pathFromNames(view[side], parts) };
  renderInspector();
});
bind("copy-mark", () => {
  $("marked").value = layout(
    view[$("mark-side").value],
    view.contextNames,
    view.referenceNames,
  ).text;
});
bind("select-mark", () => {
  const side = $("mark-side").value;
  selection = {
    side,
    path: pathFromMarked(view[side], $("marked").value, view.contextNames, view.referenceNames),
  };
  renderInspector();
});
bind("preview-code-button", async () =>
  showPreview(await request("previewSource", { source: $("code").value })),
);
bind("preview-op", async () => {
  const m = metadata.find((m) => m.name === $("opcode").value);
  const args = Array.from(
    { length: m.judgements },
    (_, i) => $(`premise-${i}`).value,
  );
  const options = [];
  if (m.context) options.push(`context: ${$("context-arg").value}`);
  if (m.free)
    options.push(
      `free: [${Array.from({ length: m.free }, (_, i) => $(`free-${i}`).value).join(", ")}]`,
    );
  showPreview(
    await request("previewSource", {
      source: `${$("result-name").value.trim()} = kernel.${m.name}(${args.join(", ")}${options.length ? "; " + options.join(", ") : ""})`,
    }),
  );
});
bind("verify", async () => {
  $("verification").textContent = (await request("verify", {
    proposition: $("proposition").value,
    proof: $("proof").value,
  }))
    ? "Verified closed proof."
    : "Not a closed proof of this proposition.";
});
bind("save", async () => {
  const data = await request("export"),
    url = URL.createObjectURL(
      new Blob([JSON.stringify(data, null, 2)], { type: "application/json" }),
    );
  const a = document.createElement("a");
  a.href = url;
  a.download = "proof.thth.json";
  a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
});
bind("load", () => $("file").click());
$("file").onchange = async () => {
  try {
    const file = $("file").files[0];
    if (!file) return;
    if (file.size > 32000000)
      throw new Error("Proof files must be at most 32 MB.");
    await move("import", { document: JSON.parse(await file.text()) });
  } catch (e) {
    error(e);
  } finally {
    $("file").value = "";
  }
};
bind("reset", () => {
  navigation.length = 0;
  worker.terminate();
  for (const p of pending.values()) {
    clearTimeout(p.timer);
    p.reject(new Error("Worker reset."));
  }
  pending.clear();
  draft = null;
  selection = null;
  view = null;
  $("preview").hidden = true;
  $("status").textContent = "Loading WASM…";
  start();
});
$("axioms").onchange = async () => {
  try {
    await move("policy", { allowAxioms: $("axioms").checked });
  } catch (e) {
    $("axioms").checked = state.allowAxioms;
    error(e);
  }
};
$("opcode").onchange = renderOperands;
$("filter").oninput = () => state && renderState();
$("show-intermediate").onchange = () => state && renderState();
for (const p of proofs)
  option(
    $("bundled-proof"),
    p.id,
    `${p.title} · axioms ${p.allowAxioms ? "on" : "off"}`,
  );
$("bundled-proof").value = "prelude_library";
bind("open-bundled", async () => {
  const entry = proofs.find((p) => p.id === $("bundled-proof").value);
  const response = await fetch(
    new URL(`./proofs/${entry.file}`, import.meta.url),
  );
  if (!response.ok) throw new Error("Unable to load bundled proof.");
  $("filter").value = "";
  await move("import", { document: await response.json(), adoptPolicy: true });
  await choose(entry.exports.at(-1));
  if (entry.verify) {
    $("proposition").value = entry.verify[0];
    $("proof").value = entry.verify[1];
    $("verification").textContent = (await request("verify", {
      proposition: entry.verify[0],
      proof: entry.verify[1],
    }))
      ? "Verified closed proof."
      : "Not verified.";
  } else $("verification").textContent = "";
});
start();
