import createCubical from "./dist/cubical.mjs";
import { CubicalProgram } from "./cubical-program.mjs";
import { readWorkbenchTransfer } from "./workbench-transfer.mjs";
import { cubicalMathTree } from "./cubical-notation.mjs";
import { renderMathNotation } from "./math-notation.mjs";
const $ = id => document.getElementById(id), history = [];
let program, view, checked, selected;
const options = () => ({ resolve: binding => program.symbols[binding], inspect: info => inspect(info.binding),
  identitySugar: $("identity-sugar").checked });
function display() {
  $("name").textContent = program.symbols[selected]?.name ?? selected ?? "Edited expression";
  $("context").replaceChildren();
  if (!view.context.length && !view.dimensions?.length) $("context").textContent = "Empty context";
  if (view.dimensions?.length) {
    const row = document.createElement("div");
    row.textContent = `Interval coordinates: ${view.dimensions.map(([name]) => name).join(", ")}`;
    $("context").append(row);
  }
  for (const entry of view.context) {
    const row = document.createElement("div"); row.className = "context-entry";
    const label = document.createElement("span"); label.textContent = `${entry.label ?? entry.name} :`;
    const type = document.createElement("div"); renderMathNotation(type, cubicalMathTree(entry.type, view.symbols), options());
    row.append(label, type); $("context").append(row);
  }
  for (const side of ["expression", "type"])
    renderMathNotation($(side), cubicalMathTree(view[side], view.symbols), options());
  $("syntax").value = JSON.stringify(view.expression, null, 2);
  $("back").disabled = !history.length;
}
function validate(term = view.expression) {
  checked = program.kernel.withUnfoldingHints(view.unfoldingHints ?? [], () => program.checker.syntax.check(term, view.type, view.context.map(x => [x.name, x.type]), new Map(view.dimensions ?? [])));
  view.expression = checked.term; view.type = checked.type;
  $("normalize").disabled = false; $("check").disabled = false;
  $("status").textContent = `Cubical C checked · ${checked.checkingSteps.toLocaleString()} checking steps · ${checked.arenaNodes.toLocaleString()} nodes`;
  $("diagnostic").hidden = true;
}
function failure(error) {
  checked = null; $("normalize").disabled = true;
  $("diagnostic").hidden = false; $("diagnostic").textContent = error.message;
  $("status").textContent = "Expression not checked";
}
function inspect(binding, remember = true) {
  try {
    if (remember && view) history.push({ view, selected });
    view = program.inspect(binding); selected = binding;
    validate(); display();
  } catch (error) { failure(error); }
}
$("back").onclick = () => {
  const previous = history.pop(); if (!previous) return;
  ({ view, selected } = previous);
  try { validate(); display(); } catch (error) { failure(error); }
};
$("unhighlight").onclick = () => {
  getSelection()?.removeAllRanges();
  document.querySelectorAll(".highlight,.selected").forEach(node => node.classList.remove("highlight", "selected"));
};
$("identity-sugar").onchange = () => { if (view) display(); };
$("syntax").oninput = () => {
  checked = null; $("normalize").disabled = true;
  $("status").textContent = "Edited syntax is not checked; displayed terms show the last checked version.";
};
$("check").onclick = () => { try { validate(JSON.parse($("syntax").value)); display(); } catch (error) { failure(error); } };
$("normalize").onclick = () => {
  if (!checked) return;
  try {
    view.expression = program.checker.syntax.decode(program.kernel.normalize(checked.expression), new Map(view.dimensions ?? []));
    validate(); display();
  } catch (error) { failure(error); }
};
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
    view = { ...view, expression: type.term, type: type.type };
  }
  validate(); display();
} catch (error) { failure(error); }
addEventListener("pagehide", () => program?.dispose());
