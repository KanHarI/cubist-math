import { foldedInspection } from "./cubical-inspection.mjs";
import createCubical from "./dist/cubical.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { readWorkbenchTransfer } from "./workbench-transfer.mjs";
import { cubicalMathTree } from "./cubical-notation.mjs";
import { renderMathNotation } from "./math-notation.mjs";
import { reduceView, checkReduction, reductionRule, termAtPath } from "./cubical-reduction.mjs";
const $ = id => document.getElementById(id), history = [];
let program, view, checked, selected, reductionMode = null, reductionLimit = 5000;
const enableReductions = enabled => document.querySelectorAll("[data-reduction]").forEach(button => { button.disabled = !enabled; });
const options = () => ({ resolve: binding => view.symbols[binding], inspect: info => inspect(info.binding),
  identitySugar: $("identity-sugar").checked, truncationSugar: $("truncation-sugar").checked });
function display(updateSyntax = true) {
  const display = $("fold-names").checked ? view.folded ?? foldedInspection(view) : view;
  $("name").textContent = view.symbols[selected]?.name ?? selected ?? "Edited expression";
  $("context").replaceChildren();
  if (!view.context.length && !view.dimensions?.length) $("context").textContent = "Empty context";
  if (view.dimensions?.length) {
    const row = document.createElement("div");
    row.textContent = `Interval coordinates: ${view.dimensions.map(([name]) => name).join(", ")}`;
    $("context").append(row);
  }
  for (const entry of display.context) {
    const row = document.createElement("div"); row.className = "context-entry";
    const label = document.createElement("span"), button = document.createElement("button");
    button.className = "reference"; button.textContent = entry.label ?? entry.name; button.disabled = !entry.binding;
    button.onclick = () => inspect(entry.binding); label.append(button, " :");
    const type = document.createElement("div"); renderMathNotation(type, cubicalMathTree(entry.type, view.symbols), options());
    row.append(label, type); $("context").append(row);
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
      ? `Choose one of ${count} highlighted ${reductionMode.kind === "beta" ? "β" : "δ"} sites in the ${reductionMode.side}.`
      : `No ${reductionMode.kind === "beta" ? "β" : "δ"} sites ${truncated ? "in the displayed portion" : "in the " + reductionMode.side}.`;
    $("reduction-status").textContent += truncated ? " Show more to reveal hidden sites." : "";
  }
  if (updateSyntax) $("syntax").value = JSON.stringify(view.expression, null, 2);
  $("back").disabled = !history.length;
}
function validate(term = view.expression) {
  checked = program.kernel.withUnfoldingHints(view.unfoldingHints ?? [], () => program.checker.syntax.check(term, view.type, view.context.map(x => [x.name, x.type]), new Map(view.dimensions ?? [])));
  view.expression = checked.term;
  enableReductions(true); $("check").disabled = false;
  $("status").textContent = `Cubical C checked · ${checked.checkingSteps.toLocaleString()} checking steps · ${checked.arenaNodes.toLocaleString()} nodes`;
  $("diagnostic").hidden = true;
}
function failure(error) {
  reductionMode = null;
  checked = null; enableReductions(false);
  if (view) display(false);
  $("diagnostic").hidden = false; $("diagnostic").textContent = error.message;
  $("status").textContent = "Expression not checked";
}
function inspect(binding, remember = true) {
  reductionMode = null;
  try {
    if (remember && view) history.push({ view, selected });
    view = program.inspect(binding); selected = binding;
    $("reduction-status").textContent = "";
    validate(); display();
  } catch (error) { failure(error); }
}
$("back").onclick = () => {
  reductionMode = null;
  const previous = history.pop(); if (!previous) return;
  ({ view, selected } = previous);
  $("reduction-status").textContent = "Restored the previous checked view.";
  try { validate(); display(); } catch (error) { failure(error); }
};
$("unhighlight").onclick = () => {
  reductionMode = null;
  $("reduction-status").textContent = "";
  if (view) display(false);
  getSelection()?.removeAllRanges();
  document.querySelectorAll(".highlight,.selected").forEach(node => node.classList.remove("highlight", "selected"));
};
for (const id of ["identity-sugar", "truncation-sugar", "fold-names"]) $(id).onchange = () => { if (view) display(false); };
$("syntax").oninput = () => {
  const wasSelecting = reductionMode !== null;
  reductionMode = null;
  if (wasSelecting) display(false);
  $("reduction-status").textContent = "";
  checked = null; enableReductions(false);
  $("status").textContent = "Edited syntax is not checked; displayed terms show the last checked version.";
};
$("check").onclick = () => { try { validate(JSON.parse($("syntax").value)); view.folded = null; display(); } catch (error) { failure(error); } };
function reduce(side, kind, path = null) {
  if (!checked) return;
  reductionMode = null;
  try {
    let result;
    if (kind === "normalize") {
      const dimensions = new Map(view.dimensions ?? []);
      const term = program.kernel.withUnfoldingHints(view.unfoldingHints ?? [], () => {
        const original = program.checker.syntax.check(view[side], null, view.context.map(x => [x.name, x.type]), dimensions);
        return program.checker.syntax.decode(program.kernel.normalize(original.expression), dimensions);
      });
      result = { ...checkReduction(program, view, side, term), change: { rule: "Normalized", name: side } };
    } else result = reduceView(program, view, side, kind, path);
    if (!result.change) {
      $("reduction-status").textContent = kind === "delta" ? `No named definitions to unfold in the ${side}.`
        : `No function/path applications or pair projections to beta-reduce in the ${side}.`;
      return;
    }
    history.push({ view, selected });
    // Preserve folding elsewhere, but never immediately refold the changed term.
    const folded = { ...(view.folded ?? foldedInspection(view)), [side]: result.view[side] };
    if (side === "expression") delete folded.reference;
    view = { ...result.view, folded }; checked = result.checked;
    enableReductions(true); $("diagnostic").hidden = true;
    $("status").textContent = "Cubical C checked · reduction is definitionally equal to the previous term";
    const name = view.symbols[result.change.name]?.name ?? result.change.name;
    $("reduction-status").textContent = kind === "normalize" ? `Normalized ${side}.`
      : `${result.change.rule} ${side}: ${name}. Back undoes this step.`;
    display();
  } catch (error) { failure(error); }
}
for (const side of ["expression", "type"]) {
  for (const kind of ["beta", "delta"]) $(kind + "-" + side).onclick = () => {
    if (!checked) return;
    reductionMode = { side, kind }; reductionLimit = 5000; display();
  };
  $(side === "expression" ? "normalize" : "normalize-type").onclick = () => reduce(side, "normalize");
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
$("more-reduction-sites").onclick = () => { if (reductionMode) { reductionLimit *= 2; display(); } };
addEventListener("keydown", event => { if (event.key === "Escape" && reductionMode) $("unhighlight").click(); });
try {
  const key = new URLSearchParams(location.search).get("transfer");
  if (!key) throw new Error("Open a checked expression from the cubical proof inspector.");
  const payload = await readWorkbenchTransfer(key);
  if (payload.format !== "thth-cubical" || payload.version !== 1) throw new Error("Unsupported cubical transfer format.");
  if (payload.proofReturn) {
    const address = new URL(payload.proofReturn, location.href);
    if (address.origin === location.origin && address.pathname.endsWith("/proof.html")) $("source-back").href = address.href;
  }
  program = new CubicalProgram(await createCubical(), async name => {
    if (typeof payload.sources?.[name] !== "string") throw new Error(`Missing source module ${name}.`);
    return payload.sources[name];
  });
  await program.check(payload.source, payload.main, progress => { $("status").textContent = `Rechecking source · ${progress.completed} declarations`; });
  // Ignore supplied expression/type claims. Reconstruct from replayed source.
  view = program.inspect(payload.binding); selected = payload.binding;
  if (payload.side === "type") {
    const type = program.checker.syntax.check(view.type, null, view.context.map(x => [x.name, x.type]), new Map(view.dimensions ?? []));
    view = { ...view, expression: type.term, type: type.type, folded: view.folded ? { ...view.folded, expression: view.folded.type, type: type.type } : null };
  }
  validate(); display();
} catch (error) { failure(error); }
addEventListener("pagehide", () => program?.dispose());
