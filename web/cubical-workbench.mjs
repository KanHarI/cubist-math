import { splitInspectionContext } from "./cubical-context.mjs";
import { foldedInspection } from "./cubical-inspection.mjs";
import { WorkerRequests } from "./worker-requests.mjs";
import { readWorkbenchTransfer } from "./workbench-transfer.mjs";
import { cubicalMathTree } from "./cubical-notation.mjs";
import { boundedSyntaxJson, syntaxDisplayLimitMessage } from "./cubical-json.mjs";
import { renderMathNotation } from "./math-notation.mjs";
import { reductionRule, termAtPath } from "./cubical-reduction.mjs";
import { assemblyText, renderAssembly, opcodeName } from "./cubical-assembly.mjs";
import { renderJudgementGraph } from "./cubical-graph-view.mjs";
import { renderNativeTree } from "./cubical-ast-tree.mjs";
import { WorkbenchTrace, traceAttempt, traceError } from "./cubical-workbench-trace.mjs";
const $ = id => document.getElementById(id), history = [];
const trace = new WorkbenchTrace();
trace.metadata.page = location.href;
// Best-effort server provenance, not a new kernel operation or a load gate.
fetch("./dist/build-stamp.json", { cache: "no-store" }).then(response => response.ok ? response.json() : null)
  .then(stamp => { if (stamp?.kernel) trace.metadata.reportedBuild = {
    sources: stamp.kernel.sources, outputs: stamp.kernel.outputs,
  }; }).catch(() => {});
let view, checked, selected, state, busy = 0, workerFailure = null, reductionMode = null, reductionLimit = 5000;
const requests = new WorkerRequests(new Worker("./cubical-workbench-worker.mjs", { type: "module" }), { onError: workerStopped });
let assemblyLimit = 400, assemblyView = null, listing = null, assemblyFocus = [], expandedDefinitions = new Set();
let kernelPath = [];
let occurrence = null;
let treeKey = null;
const enableReductions = enabled => document.querySelectorAll("[data-reduction]").forEach(button => { button.disabled = !enabled; });
function availability() {
  const blocked = !!busy || !!workerFailure;
  document.body.dataset.busy = String(!!busy);
  document.body.setAttribute("aria-busy", String(!!busy));
  $("kernel-controls").disabled = blocked || !checked;
  $("workbench-view").disabled = blocked;
  $("back").disabled = blocked || !history.length;
  $("check").disabled = blocked || !view || $("syntax").value === syntaxDisplayLimitMessage;
  $("syntax").disabled = blocked;
  for (const id of ["unhighlight", "fold-names", "identity-sugar", "truncation-sugar", "assembly-more", "more-reduction-sites"])
    $(id).disabled = blocked;
  enableReductions(!blocked && !!checked);
}
function report(error) {
  $("diagnostic").hidden = false;
  $("diagnostic").textContent = error.message;
  if (workerFailure) {
    $("status").textContent = "Kernel worker stopped. Reload the page to start a new session.";
    $("reduction-status").textContent = "";
  }
}
function workerStopped(error) {
  workerFailure = error;
  requests.terminate(error);
  availability();
  report(error);
}
// DOM callbacks must report rejected worker/navigation requests. Kernel state
// is preserved unless checking edited syntax itself fails.
function action(handler) {
  return (...args) => {
    if (busy || workerFailure) return;
    try { Promise.resolve(handler(...args)).catch(report); }
    catch (error) { report(error); }
  };
}
async function request(command, args = {}, progress) {
  const input = { state, ...args }, entry = trace.begin(traceAttempt(command, input));
  busy++; availability();
  try {
    const result = await requests.request(command, input, progress);
    if (result.traceSession) trace.metadata.session = result.traceSession;
    trace.finish(entry, { status: "accepted", resultState: result.id,
      judgement: result.checked?.judgement, change: result.change,
      detail: result.trace ?? result.traceInitial });
    return result;
  } catch (error) {
    trace.finish(entry, { status: error.fatal || workerFailure ? "worker-failed" : "refused",
      error: traceError(error), detail: error.trace });
    if (error.fatal) workerStopped(error);
    throw error;
  } finally {
    busy--; availability();
    if (entry) $("trace-status").textContent = `${trace.sequence} trace events recorded since page load.`;
  }
}
// Clipboard access stays on the page: it must work with a busy/dead worker,
// and writeText must be called directly from the user's click for Safari.
$("copy-trace").onclick = async () => {
  const button = $("copy-trace");
  button.disabled = true;
  const text = trace.text({ state, binding: selected, checked: !!checked,
    judgement: checked?.judgement, side: $("kernel-side").value, path: [...kernelPath],
    selection: occurrence ? { handle: occurrence.handle, kind: occurrence.kind, preview: occurrence.text } : null,
    workerFailed: workerFailure ? traceError(workerFailure) : null });
  try {
    await navigator.clipboard.writeText(text);
    $("trace-fallback").hidden = true;
    $("trace-status").textContent = `Copied ${trace.entries.length} trace events. Paste the trace into the conversation.`;
  } catch {
    $("trace-fallback").value = text; $("trace-fallback").hidden = false;
    $("trace-fallback").focus(); $("trace-fallback").select();
    $("trace-status").textContent = "Clipboard unavailable. Copy the selected trace below.";
  } finally { button.disabled = false; }
};
function adopt(snapshot) {
  ({ view, checked, selected } = snapshot); state = snapshot.id;
  assemblyView = null; occurrence = null; treeKey = null;
  $("kernel-actions").replaceChildren(); $("kernel-operands").replaceChildren();
  $("kernel-preview").textContent = ""; $("kernel-selection").textContent = "";
  $("kernel-tree-content").replaceChildren();
  availability();
}
const remember = () => ({ view, checked, selected, id: state, kernelPath: [...kernelPath], kernelSide: $("kernel-side").value });
const options = () => ({ resolve: binding => view.symbols[binding], inspect: info => inspect(info.binding),
  identitySugar: $("identity-sugar").checked, truncationSugar: $("truncation-sugar").checked });
async function display(updateSyntax = true) {
  const mode = $("workbench-view").value, assembly = mode === "assembly", kernelGraph = mode === "graph";
  $("mathematical-view").hidden = mode !== "math";
  $("assembly-view").hidden = !assembly;
  $("graph-view").hidden = !kernelGraph;
  document.querySelectorAll("[data-math-option]").forEach(element => { element.hidden = mode !== "math"; });
  $("name").textContent = view.symbols[selected]?.name ?? selected ?? "Edited expression";
  $("back").disabled = !history.length;
  if (updateSyntax) {
    const syntax = boundedSyntaxJson(view.expression);
    $("syntax").value = syntax ?? syntaxDisplayLimitMessage;
    $("check").disabled = syntax === null;
  }
  if (assembly || kernelGraph) {
    $("more-reduction-sites").hidden = true;
    if (assembly) await displayAssembly(); else await displayGraph();
    return;
  }
  const display = $("fold-names").checked ? view.folded ?? foldedInspection(view) : view;
  $("name").textContent = view.symbols[selected]?.name ?? selected ?? "Edited expression";
  const { context, axioms } = splitInspectionContext(view, display.context);
  $("context").replaceChildren();
  $("axioms").replaceChildren();
  $("axioms-section").hidden = !axioms.length;
  if (!context.length && !view.dimensions?.length) $("context").textContent = "Empty context";
  if (view.dimensions?.length) {
    const row = document.createElement("div");
    row.textContent = `Interval coordinates: ${view.dimensions.map(([name]) => name).join(", ")}`;
    $("context").append(row);
  }
  for (const [target, entries] of [["context", context], ["axioms", axioms]]) for (const entry of entries) {
    const row = document.createElement("div"); row.className = "context-entry";
    const label = document.createElement("span"), button = document.createElement("button");
    button.className = "reference"; button.textContent = entry.label ?? entry.name; button.disabled = !entry.binding;
    button.onclick = () => inspect(entry.binding); label.append(button, " :");
    const type = document.createElement("div"); renderMathNotation(type, cubicalMathTree(entry.type, view.symbols), options());
    row.append(label, type); $(target).append(row);
  }
  for (const side of ["expression", "type"]) {
    const active = reductionMode?.side === side;
    const decorateTerm = active ? (node, element) => {
      if (!node.sourcePath || node.name === "…") return element;
      const rule = reductionRule(termAtPath(view[side], node.sourcePath), reductionMode.kind);
      if (!rule) return element;
      element.classList.add("reduction-site");
      element.dataset.reductionPath = JSON.stringify(node.sourcePath);
      element.setAttribute("role", "button"); element.setAttribute("tabindex", "0");
      const label = `${rule.rule} reduce ${view.symbols[rule.name]?.name ?? rule.name}`;
      element.setAttribute("title", label); element.setAttribute("aria-label", label);
      return element;
    } : null;
    renderMathNotation($(side), cubicalMathTree(active ? view[side] : display[side], view.symbols,
      active ? reductionLimit : 1200, { paths: active }), { ...options(), decorateTerm,
        ...(active ? { truncationSugar: false } : {}) });
  }
  for (const side of ["expression", "type"]) for (const kind of ["beta", "delta"])
    $(kind + "-" + side).setAttribute("aria-pressed", String(reductionMode?.side === side && reductionMode.kind === kind));
  $("more-reduction-sites").hidden = true;
  if (reductionMode) {
    const target = $(reductionMode.side), count = target.querySelectorAll(".reduction-site").length;
    const truncated = target.textContent.includes("…");
    $("more-reduction-sites").hidden = !truncated;
    $("reduction-status").textContent = count
      ? `Select one of ${count} highlighted ${reductionMode.kind === "beta" ? "β" : "δ"} sites in the ${reductionMode.side}.`
      : `No ${reductionMode.kind === "beta" ? "β" : "δ"} sites ${truncated ? "in the displayed portion" : "in the " + reductionMode.side}.`;
    $("reduction-status").textContent += truncated ? " Show more to reveal hidden sites." : "";
  }
  $("back").disabled = !history.length;
}
async function displayAssembly() {
  $("kernel-controls").disabled = !checked;
  if (!checked) {
    $("kernel-selection").textContent = ""; $("kernel-operands").replaceChildren();
    $("kernel-preview").textContent = ""; $("kernel-actions").replaceChildren();
    $("kernel-tree-content").replaceChildren(); treeKey = null; occurrence = null;
    listing = null; $("assembly-listing").replaceChildren();
    $("assembly-status").textContent = "Return to Mathematical view and check the edited expression before inspecting its AST.";
    $("assembly-more").hidden = true; $("assembly-download").disabled = true; return;
  }
  if (assemblyView !== view) {
    assemblyView = view; assemblyLimit = 400; assemblyFocus = []; expandedDefinitions = new Set();
  }
  listing = await request("assembly", { options: { limit: assemblyLimit, focus: assemblyFocus, expanded: [...expandedDefinitions] } });
  // The term and its type, typeset, above the nodes that store them.
  $("assembly-math").replaceChildren(...[["Term", view.expression], ["Type", view.type]].map(([label, term]) => {
    const row = document.createElement("div"), name = document.createElement("span"), math = document.createElement("div");
    row.className = "assembly-math-row"; name.textContent = label; math.className = "kernel-term typeset";
    renderMathNotation(math, cubicalMathTree(term, view.symbols, 1200), options());
    row.append(name, math);
    return row;
  }));
  renderAssembly($("assembly-listing"), listing, { jump: action(jumpAssembly),
    expand: action(async (id, body) => { expandedDefinitions.add(id); assemblyFocus.unshift(body); await displayAssembly(); await jumpAssembly(body); }),
    inspect: binding => inspect(binding) });
  $("assembly-status").textContent = `${listing.nodes.length.toLocaleString()} native nodes shown`
    + (listing.pending ? ` · ${listing.pending.toLocaleString()} discovered operands remain; show more or follow a handle.` : ". Named definitions can be expanded individually.");
  $("assembly-more").hidden = !listing.pending;
  $("assembly-download").disabled = false;
  await displayOccurrence();
}
async function displayOccurrence() {
  if (!checked) return;
  const side = $("kernel-side").value, path = [...kernelPath];
  const node = await request("occurrence", { side, path });
  occurrence = { ...node, side, path };
  $("kernel-selection").textContent = `${side} [${path.join(", ")}] · ${node.label} · ${opcodeName(node.kind)} · %${node.handle}`;
  $("kernel-preview").textContent = node.text;
  $("kernel-actions").replaceChildren(...node.actions.map(({ rule, label, path: target }) => {
    const button = document.createElement("button");
    button.textContent = label; button.dataset.kernelRule = rule;
    button.dataset.kernelPath = JSON.stringify(target);
    if (rule === "delta") button.id = "kernel-delta";
    button.title = `${rule} · ${side} [${target.join(", ")}] · uses the work budget below`;
    button.onclick = action(() => applyNative(rule, target, side));
    return button;
  }));
  $("kernel-parent").disabled = !kernelPath.length;
  $("assembly-listing").querySelectorAll(".current-occurrence").forEach(row => row.classList.remove("current-occurrence"));
  $(`assembly-node-${node.handle}`)?.classList.add("current-occurrence");
  $("kernel-operands").replaceChildren(...node.operands.filter(operand => operand.handle).map(({ handle, index, role, label, kind }) => {
    const row = document.createElement("div"), button = document.createElement("button");
    row.className = "kernel-operand";
    button.dataset.operand = index;
    button.textContent = `${role}: ${label}`;
    button.title = `Select operand ${index} / ${"abcd"[index]} · %${handle}`;
    button.onclick = action(async () => { kernelPath = [...kernelPath, index]; await selectOccurrence(); });
    row.append(button);
    if (kind === "DefRef") {
      const unfold = document.createElement("button");
      unfold.textContent = `δ unfold ${label}`; unfold.dataset.unfoldOperand = index;
      unfold.onclick = action(async () => {
        kernelPath = [...kernelPath, index]; await selectOccurrence(); await applyNative("delta");
      });
      row.append(unfold);
    }
    return row;
  }));
  await displayTree().catch(report);
}
async function selectOccurrence() {
  $("diagnostic").hidden = true; $("reduction-status").textContent = "";
  const previous = occurrence;
  try { await displayOccurrence(); }
  catch (error) {
    if (previous) { kernelPath = previous.path; $("kernel-side").value = previous.side; }
    throw error;
  }
}
async function displayTree() {
  if (!checked || !occurrence) return;
  const treeState = state, { side, path } = occurrence, key = JSON.stringify([treeState, side, path]);
  if (treeKey === key) return;
  $("kernel-tree-content").replaceChildren(); treeKey = null;
  if (!$("kernel-tree").open) return;
  treeKey = key; $("kernel-tree-content").textContent = "Loading native operands…";
  const load = path => request("subtree", { state: treeState, side, path });
  try {
    const tree = await load(path);
    if (treeKey !== key) return;
    renderNativeTree($("kernel-tree-content"), tree, { path, load, select: action(async path => {
      if (state !== treeState) return;
      kernelPath = path; $("kernel-side").value = side; await selectOccurrence();
    }) });
  } catch (error) {
    if (treeKey === key) {
      treeKey = null;
      $("kernel-tree-content").textContent = error.message;
    }
    throw error;
  }
}
$("kernel-tree").ontoggle = () => { if ($("kernel-tree").open) displayTree().catch(report); };
$("kernel-side").onchange = $("kernel-root").onclick = action(async () => { kernelPath = []; await selectOccurrence(); });
$("kernel-parent").onclick = action(async () => { kernelPath = kernelPath.slice(0, -1); await selectOccurrence(); });
$("kernel-show").onclick = action(() => { if (occurrence) return jumpAssembly(occurrence.handle); });
$("kernel-apply").onclick = action(() => applyNative($("kernel-rule").value));
async function applyNative(rule, targetPath = kernelPath, targetSide = $("kernel-side").value) {
  if (!checked || busy) return;
  let result;
  try {
    $("status").textContent = `Running ${rule} in the kernel worker…`;
    result = await request("step", { side: targetSide, path: targetPath, rule,
      budget: $("kernel-budget").valueAsNumber });
  } catch (error) {
    if (workerFailure) { report(error); return; }
    $("diagnostic").hidden = false; $("diagnostic").textContent = error.message;
    $("status").textContent = "Cubical C checked · previous judgement retained";
    $("reduction-status").textContent = "Operation refused; the previous checked term and selected occurrence are retained.";
    return;
  }
  history.push(remember()); adopt(result);
  const { before, after, judgement, side, path } = result.change;
  kernelPath = [...path]; $("kernel-side").value = side;
  $("diagnostic").hidden = true;
  $("status").textContent = `Cubical C checked · native Step judgement #${judgement}`;
  $("reduction-status").textContent = `${rule} ${side} [${path.join(", ")}]: %${before} → %${after}.`
    + (before === after ? " The selected syntax is unchanged." : "") + " Back undoes this operation.";
  try { await display(); }
  catch (error) {
    $("diagnostic").hidden = false;
    $("diagnostic").textContent = `The operation was checked, but displaying its result failed: ${error.message}`;
  }
}
// The judgement graph of the checked view, derived in instruction mode. A
// definition's body is derived on request, as its lookup's premise.
let graphView = null, graphExpanded = new Set();
async function displayGraph(focus = null) {
  $("graph-listing").replaceChildren();
  if (!checked) {
    $("graph-status").textContent = "Return to Mathematical view and check the edited expression before deriving its judgement graph.";
    return;
  }
  if (graphView !== view) { graphView = view; graphExpanded = new Set(); }
  try {
    const graph = await request("graph", { options: { expanded: [...graphExpanded] } });
    const rendered = renderJudgementGraph($("graph-listing"), graph, {
      jumpNode: action(async handle => { $("workbench-view").value = "assembly"; await display(false); await jumpAssembly(handle); }),
      expand: action(reference => { graphExpanded.add(reference); return displayGraph(reference); }),
    });
    const defined = focus && graph.rows.find(row => row.definition?.reference === focus)?.definition.root;
    if (defined) rendered.jump(defined);
    const steps = graph.rows.filter(row => row.rule === "step").length;
    const plural = (count, word) => `${count.toLocaleString()} ${word}${count === 1 ? "" : "s"}`;
    $("graph-status").textContent = `${plural(graph.rows.length, "judgement")}, ${plural(steps, "highlighted step")}; `
      + `#${graph.root} is the conclusion.` + (graph.truncated ? " Only part of the graph is shown." : "");
  } catch (error) {
    $("graph-status").textContent = `The instruction kernel could not derive this view: ${error.message}`;
  }
}
async function jumpAssembly(handle) {
  if (busy) return;
  let row = $(`assembly-node-${handle}`);
  if (!row) { assemblyFocus.unshift(handle); await displayAssembly(); row = $(`assembly-node-${handle}`); }
  $("assembly-listing").querySelectorAll(".selected").forEach(node => node.classList.remove("selected"));
  row?.classList.add("selected"); row?.scrollIntoView({ block: "nearest" }); row?.focus({ preventScroll: true });
}
$("workbench-view").onchange = action(async () => {
  reductionMode = null; $("reduction-status").textContent = "";
  if (view) await display(false);
});
$("assembly-more").onclick = action(() => { assemblyLimit *= 2; return displayAssembly(); });
$("assembly-download").onclick = () => {
  if (!listing) return;
  const url = URL.createObjectURL(new Blob([assemblyText(listing)], { type: "text/plain" }));
  const link = document.createElement("a"); link.href = url; link.download = `${selected ?? "kernel"}.ast.txt`; link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
};
async function validate(term = view.expression) {
  adopt(await request("check", { term }));
  kernelPath = [];
  assemblyView = null;
  enableReductions(true); $("check").disabled = false;
  $("status").textContent = `Cubical C checked · ${checked.checkingSteps.toLocaleString()} checking steps · ${checked.arenaNodes.toLocaleString()} nodes`;
  $("diagnostic").hidden = true;
}
function failure(error) {
  if (workerFailure) { report(error); return; }
  reductionMode = null;
  checked = null; enableReductions(false);
  $("kernel-controls").disabled = true;
  if (view) display(false).catch(report);
  $("diagnostic").hidden = false; $("diagnostic").textContent = error.message;
  $("status").textContent = "Expression not checked";
}
async function inspect(binding, save = true) {
  if (busy) return;
  reductionMode = null;
  let next;
  try {
    next = await request("inspect", { binding });
  } catch (error) {
    report(error);
    if (!workerFailure && checked) $("status").textContent = "Inspection failed · previous checked judgement retained";
    return;
  }
  if (save && view) history.push(remember());
  adopt(next);
  kernelPath = [];
  $("reduction-status").textContent = "";
  $("diagnostic").hidden = true; $("status").textContent = "Cubical C checked · inspected definition";
  try { await display(); }
  catch (error) {
    report(error);
    if (!workerFailure) $("status").textContent = "Definition checked · displaying the inspected view failed";
  }
}
$("back").onclick = action(async () => {
  reductionMode = null;
  const previous = history.pop(); if (!previous) return;
  trace.finish(trace.begin({ command: "back", state }), { status: "accepted",
    resultState: previous.id, side: previous.kernelSide, path: previous.kernelPath,
    judgement: previous.checked?.judgement });
  adopt(previous);
  kernelPath = previous.kernelPath ?? [];
  if (previous.kernelSide) $("kernel-side").value = previous.kernelSide;
  $("reduction-status").textContent = "Restored the previous checked view.";
  try {
    if (previous.checked) {
      checked = previous.checked; enableReductions(true); $("diagnostic").hidden = true;
      $("status").textContent = "Cubical C checked · restored previous judgement";
    } else await validate();
    await display();
  } catch (error) { failure(error); }
});
$("unhighlight").onclick = action(async () => {
  reductionMode = null;
  $("reduction-status").textContent = "";
  if (view) await display(false);
  getSelection()?.removeAllRanges();
  document.querySelectorAll(".highlight,.selected").forEach(node => node.classList.remove("highlight", "selected"));
});
for (const id of ["identity-sugar", "truncation-sugar", "fold-names"]) $(id).onchange = action(() => { if (view) return display(false); });
$("syntax").oninput = () => {
  const wasSelecting = reductionMode !== null;
  reductionMode = null;
  if (wasSelecting) display(false).catch(report);
  $("reduction-status").textContent = "";
  checked = null; enableReductions(false);
  $("kernel-controls").disabled = true;
  $("check").disabled = false;
  $("status").textContent = "Edited syntax is not checked; displayed terms show the last checked version.";
};
$("check").onclick = action(async () => { try { await validate(JSON.parse($("syntax").value)); await display(); } catch (error) { failure(error); } });
async function reduce(side, kind, path = null) {
  if (!checked || busy) return;
  reductionMode = null;
  try {
    $("status").textContent = `Running ${kind} in the kernel worker…`;
    const result = await request("reduce", { side, kind, path });
    if (!result.change) {
      $("reduction-status").textContent = kind === "delta" ? `No named definitions to unfold in the ${side}.`
        : `No function/path applications or pair projections to beta-reduce in the ${side}.`;
      return;
    }
    history.push(remember()); adopt(result);
    kernelPath = [];
    enableReductions(true); $("diagnostic").hidden = true;
    $("status").textContent = "Cubical C checked · reduction is definitionally equal to the previous term";
    const name = view.symbols[result.change.name]?.name ?? result.change.name;
    $("reduction-status").textContent = kind === "normalize" ? `Normalized ${side}.`
      : `${result.change.rule} ${side}: ${name}. Back undoes this step.`;
    await display();
  } catch (error) { failure(error); }
}
for (const side of ["expression", "type"]) {
  for (const kind of ["beta", "delta"]) $(kind + "-" + side).onclick = action(() => {
    if (!checked) return;
    reductionMode = { side, kind }; reductionLimit = 5000; return display();
  });
  $(side === "expression" ? "normalize" : "normalize-type").onclick = action(() => reduce(side, "normalize"));
  const select = event => {
    if (!checked || reductionMode?.side !== side) return;
    if (event.type === "keydown" && !["Enter", " "].includes(event.key)) return;
    const target = event.target.closest(".reduction-site");
    if (!target || !$(side).contains(target)) return;
    event.preventDefault(); event.stopImmediatePropagation();
    reduce(side, reductionMode.kind, JSON.parse(target.dataset.reductionPath));
  };
  // Capture before ordinary name-inspection handlers, including nested sites.
  $(side).addEventListener("click", select, true);
  $(side).addEventListener("keydown", select, true);
}
$("more-reduction-sites").onclick = action(() => { if (reductionMode) { reductionLimit *= 2; return display(); } });
addEventListener("keydown", event => { if (event.key === "Escape" && reductionMode) $("unhighlight").click(); });
try {
  const params = new URLSearchParams(location.search);
  const requested = params.get("view") === "ast" ? "assembly" : params.get("view");
  if (["assembly", "graph"].includes(requested)) $("workbench-view").value = requested;
  const key = params.get("transfer");
  const payload = key ? await readWorkbenchTransfer(key) : {
    format: "thth-cubical", version: 1, main: "workbench", sources: {},
    source: "import unat; use unat; def identity(n : UNat) := n; def example := identity(2);",
    binding: "workbench__example", side: "expression",
  };
  if (payload.format !== "thth-cubical" || payload.version !== 1) throw new Error("Unsupported cubical transfer format.");
  if (payload.proofReturn) {
    const address = new URL(payload.proofReturn, location.href);
    if (address.origin === location.origin && address.pathname.endsWith("/proof.html")) $("source-back").href = address.href;
  }
  adopt(await request("load", payload, progress => {
    $("status").textContent = `Checking source in worker · ${progress.completed}${progress.total ? "/" + progress.total : ""} declarations · ${progress.current ?? ""}`;
  }));
  $("status").textContent = `Cubical C checked · ${checked.arenaNodes.toLocaleString()} nodes`;
  await display();
} catch (error) { failure(error); }
addEventListener("pagehide", () => requests.terminate());
