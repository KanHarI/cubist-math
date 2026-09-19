import { proofChoices as choices, proofTopics, proofsInTopic } from "./proof-library.mjs";
import { proofRequestWatchdog } from "./proof-watchdog.mjs";
import { renderMathNotation, kernelMathTree } from "./math-notation.mjs";
import { axiomLabels } from "./axiom-labels.mjs";
import { saveWorkbenchTransfer } from "./workbench-transfer.mjs";

const query = new URLSearchParams(location.search);
const proofId = choices.some((p) => p.id === query.get("proof"))
  ? query.get("proof")
  : "euclid";
const sourceURL = `proofs/${choices.find((p) => p.id === proofId).file ?? proofId + ".proof"}`;
const response = await fetch(sourceURL, { cache: "no-store" });
if (!response.ok) throw new Error("Unable to load source: " + sourceURL);
const original = await response.text();
let savedDraft = null,
  previousDraft = null,
  sourceNotice = "";
try {
  const stored = sessionStorage.getItem("mathscript:" + proofId);
  if (stored) {
    let record;
    try {
      record = JSON.parse(stored);
    } catch {
      record = { source: stored };
    }
    if (record && typeof record.source === "string") {
      const obsoleteAudit =
        proofId === "primes" &&
        /\bconstruction\s+primes\s*\{/.test(record.source) &&
        !/\bconstruction\s+primes\s*\{/.test(original);
      const repositoryChanged =
        typeof record.baseline === "string" && record.baseline !== original;
      if (
        obsoleteAudit ||
        query.get("source") === "repo" ||
        (repositoryChanged && record.source === record.baseline)
      ) {
        previousDraft = record.source;
        sessionStorage.setItem("mathscript:previous:" + proofId, previousDraft);
        sourceNotice =
          "Loaded the current repository source. Your previous saved source is preserved.";
      } else {
        savedDraft = record.source;
        if (repositoryChanged)
          sourceNotice =
            "Your edited draft is restored. The repository has a newer source; Load repository source keeps a backup of this draft.";
      }
    }
  }
  previousDraft ??= sessionStorage.getItem("mathscript:previous:" + proofId);
} catch {}
const example = savedDraft ?? original;
import { layout } from "./expressions.mjs";
const $ = (id) => document.getElementById(id);
let worker,
  ready = false,
  last = null,
  serial = 0,
  selected = null,
  inspectSerial = 0;
const pending = new Map(),
  history = [];
$("editor").value = example;
for (const id of ["reuse-normal-forms", "memoize-instructions"]) {
  $(id).checked = true;
  try { $(id).checked = localStorage.getItem("mathscript:" + id) !== "false"; } catch {}
}
$("proof-title").textContent = choices.find((p) => p.id === proofId).title;
$("development-note").hidden = !choices.find((p) => p.id === proofId).realDevelopment;
$("puncture-note").hidden = !choices.find((p) => p.id === proofId).punctureDevelopment;
$("complex-note").hidden = !choices.find((p) => p.id === proofId).complexDevelopment;
$("source-file").href = sourceURL;
$("source-file").textContent = `web/${sourceURL}`;
$("repository-source").href =
  `proof.html?proof=${encodeURIComponent(proofId)}&source=repo`;
$("source-notice").textContent = sourceNotice;
$("source-notice").hidden = !sourceNotice;
$("previous-draft").hidden = !previousDraft;
$("previous-draft").onclick = () =>
  download(previousDraft, proofId + "-previous.proof", "text/plain");
for (const topic of proofTopics) {
  const option = document.createElement("option");
  option.value = topic.id;
  option.textContent = topic.title;
  $("proof-topic").append(option);
}
function showTopic(topic) {
  const proofs = proofsInTopic(topic);
  $("proof-picker").replaceChildren();
  // Browsing a topic must not navigate away from an edited proof.
  if (!proofs.some(item => item.id === proofId)) {
    const prompt = document.createElement("option");
    prompt.value = "";
    prompt.textContent = "Choose a proof…";
    prompt.disabled = true;
    prompt.selected = true;
    $("proof-picker").append(prompt);
  }
  for (const item of proofs) {
    const option = document.createElement("option");
    option.value = item.id;
    option.textContent = item.title;
    $("proof-picker").append(option);
  }
  if (proofs.some(item => item.id === proofId)) $("proof-picker").value = proofId;
  $("proof-count").textContent = `${proofs.length} proofs`;
}
$("proof-topic").value = choices.find(item => item.id === proofId).topic;
showTopic($("proof-topic").value);
$("proof-topic").onchange = () => showTopic($("proof-topic").value);
function rememberDraft() {
  try {
    sessionStorage.setItem(
      "mathscript:" + proofId,
      JSON.stringify({ source: $("editor").value, baseline: original }),
    );
  } catch {}
}
$("proof-picker").onchange = () => {
  if (!$("proof-picker").value) return;
  rememberDraft();
  location.href = `proof.html?proof=${encodeURIComponent($("proof-picker").value)}`;
};
addEventListener("pagehide", rememberDraft);

function showChecking(active, message = "Checking proof…") {
  $("check-loader").hidden = !active;
  $("source-panel").setAttribute("aria-busy", String(active));
  $("check-message").textContent = message;
  if (active) {
    $("check-progress").removeAttribute("value");
    $("check-detail").textContent = "0 kernel steps · 0 definitions checked · Loading proof…";
  }
}
function checkingProgress(progress) {
  const { completed, total, current, unit, instructions } = progress;
  $("check-progress").max = Math.max(1, total);
  $("check-progress").value = completed;
  $("check-message").textContent = total && completed === total
    ? "Preparing checked results…"
    : "Checking proof…";
  $("check-detail").textContent =
    `${(instructions ?? 0).toLocaleString()} kernel steps · ` +
    `${completed.toLocaleString()} of ${total.toLocaleString()} ${unit} checked` +
    (current ? ` · ${current}` : "");
}
function diagnostic(e) {
  showChecking(false);
  $("diagnostic").hidden = false;
  $("diagnostic").textContent = e.message || String(e);
}
function dirty() {
  return last && $("editor").value !== last.source;
}
function compilerOptimizations() {
  if (/^\s*(?:\/\/[^\n]*\n\s*)*construction\b/.test($("editor").value)) return {};
  return { normalForms: $("reuse-normal-forms").checked, instructions: $("memoize-instructions").checked };
}
function refreshStatus() {
  $("check").disabled = !ready || pending.size > 0;
  for (const id of ["reuse-normal-forms", "memoize-instructions"])
    $(id).disabled = !ready || pending.size > 0 || !Object.keys(compilerOptimizations()).length;
  $("export").disabled = !last || pending.size > 0;
  $("dirty").textContent = dirty()
    ? "Edited — changes are not checked. Read shows the last checked version."
    : "";
  $("status").textContent = pending.size
    ? "Checking…"
    : last
      ? `Kernel checked · ${last.axiomCount ? last.axiomCount + " explicit axioms" : "no axioms"}`
      : ready
        ? "Ready to check"
        : "Loading kernel…";
}
function request(command, args = {}) {
  const id = ++serial;
  return new Promise((resolve, reject) => {
    const watchdog = proofRequestWatchdog(command, () => {
      worker.terminate();
      ready = false;
      for (const p of pending.values()) {
        p.watchdog.stop();
        p.reject(
          new Error(
            "The checking worker stopped making progress. Reload the page to restart the kernel.",
          ),
        );
      }
      pending.clear();
      refreshStatus();
    });
    pending.set(id, { resolve, reject, watchdog });
    refreshStatus();
    worker.postMessage({ id, command, args });
  });
}
async function check() {
  showChecking(true);
  if (await refreshCompiler()) return;
  $("diagnostic").hidden = true;
  const source = $("editor").value;
  try {
    const result = await request("check", { source, optimizations: compilerOptimizations() });
    last = result;
    history.length = 0;
    renderLibrary();
    renderSource();
    renderResult();
    setMode("read");
    const target = query.get("name");
    const info =
      target &&
      [...(result.declarations ?? []), ...result.outputs].find(
        (d) => d.binding === target,
      );
    await inspect(decorate(info ?? result.outputs.at(-1)), false);
    if (info) revealSource(info);
    rememberDraft();
  } catch (e) {
    diagnostic(e);
    setMode("edit");
    if (Number.isInteger(e.offset)) {
      $("editor").focus();
      $("editor").setSelectionRange(e.offset, e.offset + 1);
    }
  } finally {
    showChecking(false);
  }
  refreshStatus();
}
function setMode(mode) {
  $("editor").hidden = mode !== "edit";
  $("read-source").hidden = mode === "edit";
  $("read-mode").setAttribute("aria-pressed", String(mode === "read"));
  $("edit-mode").setAttribute("aria-pressed", String(mode === "edit"));
  $("source-hint").textContent =
    mode === "edit"
      ? "Edit the source, then Check proof. A failed check preserves your last checked proof."
      : "Click a name to inspect it. Click a line number to see its goal and assumptions.";
}
function decorate(info) {
  const imported = last?.imports.find(
    (d) => d.binding === info.binding && d.name === info.name,
  );
  const declaration = last?.declarations?.find(
    (d) => d.binding === info.binding,
  );
  const local = last?.links.find(
    (d) =>
      d.binding === info.binding &&
      ["local", "parameter", "def", "theorem"].includes(d.role),
  );
  const value = { ...declaration, ...info, ...imported, kind: "value" };
  if (value.definitionStart === undefined && local)
    value.definitionStart = local.start;
  if (/^[0-9]+$/.test(info.name ?? "")) {
    const n = Number(info.name);
    value.role = "natural-number literal";
    value.description = `${n} : Nat is notation for ${"succ(".repeat(n)}0${")".repeat(n)}. Numerals are built from zero and successor; they are not axioms.`;
  }
  return value;
}
function revealSource(info) {
  const start = info.definitionStart ?? info.start;
  if (!Number.isInteger(start)) return;
  const line = last.source.slice(0, start).split("\n").length;
  if (last.mode === "construction" && !$("show-intermediate").checked) {
    $("show-intermediate").checked = true;
    renderSource();
    renderLibrary();
  }
  setMode("read");
  for (const row of document.querySelectorAll(".source-line.active"))
    row.classList.remove("active");
  const row = document.querySelector(`.source-line[data-line="${line}"]`);
  row?.classList.add("active");
  row?.scrollIntoView({ block: "center" });
}
function sourceLink(info) {
  const link = $("view-source");
  link.hidden = true;
  link.onclick = null;
  if (info.sourceModule) {
    link.href = `proof.html?proof=${encodeURIComponent(info.sourceModule)}${info.sourceName ? "&name=" + encodeURIComponent(info.sourceName) : ""}`;
    link.textContent =
      info.kind === "module" ? "View module source →" : "View source →";
    link.hidden = false;
  } else if (Number.isInteger(info.definitionStart)) {
    link.href = "#read-source";
    link.textContent = "View source →";
    link.hidden = false;
    link.onclick = (e) => {
      e.preventDefault();
      revealSource(info);
    };
  }
}
function renderLibrary() {
  $("definitions").replaceChildren();
  if (!last) return;
  const query = $("search").value.toLowerCase();
  const visible = [...last.outputs, ...last.imports];
  if ($("show-intermediate").checked)
    visible.push(...(last.declarations ?? []).filter((d) => d.private));
  for (const info of visible.filter((d) =>
    `${d.name} ${d.title ?? ""} ${d.description ?? ""}`
      .toLowerCase()
      .includes(query),
  )) {
    const button = document.createElement("button");
    button.className = "definition";
    button.dataset.name = info.name;
    button.append(document.createTextNode(info.name));
    const small = document.createElement("small");
    small.textContent = info.title ?? "Checked " + info.kind;
    button.append(small);
    button.onclick = () => inspect(decorate(info));
    $("definitions").append(button);
  }
}

function axiomInfo(binding) {
  return decorate({ binding, name: binding, role: "explicit axiom",
    ...[...last.outputs, ...last.imports].find(o => o.binding === binding),
    ...(last.preludeAxioms?.includes(binding)
      ? { sourceModule: "prelude_library_construction", sourceName: binding } : {}),
  });
}
function renderAxioms(target, axioms) {
  target.replaceChildren(document.createTextNode("Axioms used: "));
  if (!axioms.length) {
    target.append("None");
    return;
  }
  for (const [index, binding] of axioms.entries()) {
    if (index) target.append(document.createTextNode(", "));
    const button = document.createElement("button");
    button.className = "reference";
    button.dataset.axiom = binding;
    button.textContent = axiomLabels[binding] ?? binding;
    button.title = `Inspect ${binding} and its declared type`;
    button.onclick = () => inspect(axiomInfo(binding));
    target.append(button);
  }
}
function renderResult() {
  $("result").hidden = !last;
  $("result").replaceChildren();
  if (!last) return;
  for (const output of last.outputs) {
    const line = document.createElement("div");
    line.append(
      output.kind === "axiom" ? "Axiom " : last.mode !== "construction" || output.verified
        ? "Verified "
        : "Checked ",
    );
    const button = document.createElement("button");
    button.textContent = output.name;
    button.onclick = () =>
      inspect({ ...output, kind: "value", role: output.kind });
    line.append(button, document.createTextNode(" : " + output.type));
    const dependencies = document.createElement("small");
    dependencies.className = "axiom-dependencies";
    renderAxioms(dependencies, output.axioms ?? []);
    line.append(dependencies);
    $("result").append(line);
  }
  const detail = document.createElement("small");
  detail.textContent = `${last.instructionCount.toLocaleString()} checked instructions. ${last.axiomCount ? last.axiomCount + " explicit axioms in this module." : "No axioms."}`;
  $("result").append(detail);
}
const keywords = new Set([
  "import",
  "theorem",
  "def",
  "forall",
  "exists",
  "and",
  "or",
  "let",
  "obtain",
  "intro",
  "have",
  "cases",
  "left",
  "right",
  "exact",
  "construction",
  "private",
  "export",
  "verify",
  "with",
  "axiom",
  "opaque",
  "axioms",
  "allow",
  "none",
  "intro",
  "induction",
  "zero",
  "succ",
  "fun",
  "match",
  "return",
  "as",
]);
// Language-provided forms share the keyword palette; ordinary library and
// user-defined functions retain the green reference style.
const builtinForms = new Set([
  "Nat", "Unit", "Void", "Universe", "tt", "succ", "refl", "absurd",
  "sym", "trans", "cong", "transport", "apd", "Eq", "typed", "unfold",
  "induct", "unpack", "pair_induction", "unit_induction",
  "Suspension", "north", "south", "meridian", "suspension_induction",
  "suspension_meridian_beta", "Choice", "LEM", "FunExt", "Truncate",
  "TruncateIntro", "TruncateProp", "TruncateElim", "Univalence", "UnivalenceBeta",
]);
function renderSource() {
  $("read-source").replaceChildren();
  if (!last) return;
  const linkMap = new Map();
  for (const link of last.links) {
    const old = linkMap.get(link.start);
    if (!old || link.end - link.start < old.end - old.start)
      linkMap.set(link.start, link);
  }
  const importStarts = new Map(
    [...last.source.matchAll(/\bimport\s+([A-Za-z_][A-Za-z_0-9]*)\s*;/g)].map(
      (match) => [match.index + match[0].indexOf(match[1]), match[1]],
    ),
  );
  $("intermediate-label").hidden = last.mode !== "construction";
  const total = last.declarations?.length ?? last.steps.length;
  const hidden =
    last.mode === "construction" && !$("show-intermediate").checked
      ? last.declarations.filter((d) => d.private).length
      : 0;
  $("source-count").textContent =
    last.mode === "construction"
      ? `All ${total.toLocaleString()} steps checked. ${hidden.toLocaleString()} intermediate steps hidden; use the checkbox to show them.`
      : `${last.source.split("\n").length} lines · click a name, numeral, or line number`;
  let offset = 0;
  for (const [index, line] of last.source.split("\n").entries()) {
    if (hidden && /^\s*private\b/.test(line)) {
      offset += line.length + 1;
      continue;
    }
    const row = document.createElement("div");
    row.className = "source-line";
    row.dataset.line = index + 1;
    const number = document.createElement("button");
    number.className = "line-number";
    number.textContent = index + 1;
    number.setAttribute("aria-label", `Inspect goal at line ${index + 1}`);
    const lineOffset = offset;
    number.onclick = () => {
      const step = last.steps
        .filter(
          (s) => s.start <= lineOffset + line.length && s.end > lineOffset,
        )
        .sort((a, b) => a.end - a.start - (b.end - b.start))[0];
      if (step)
        inspect({
          kind: "goal",
          name: `Goal at line ${index + 1}`,
          step,
          line: index + 1,
        });
    };
    const code = document.createElement("span");
    code.className = "line-code";
    let cursor = 0;
    for (const token of line.matchAll(
      /\/\/.*|(?:<=|->|=>)|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[+*<=>]|\s+|./g,
    )) {
      if (token.index > cursor)
        code.append(document.createTextNode(line.slice(cursor, token.index)));
      const text = token[0],
        start = offset + token.index,
        end = start + text.length;
      if (text.startsWith("//")) {
        const span = document.createElement("span");
        span.className = "comment";
        span.textContent = text;
        code.append(span);
      } else if (importStarts.has(start)) {
        const link = document.createElement("a");
        link.className = "reference";
        link.textContent = text;
        link.dataset.name = text;
        link.href = `proof.html?proof=${encodeURIComponent(text === "prelude" ? "prelude_library_construction" : text)}`;
        link.title = `Open ${text} module source`;
        code.append(link);
      } else {
        const info = linkMap.get(start);
        const expansion = last.mode === "mathematical" && /^[0-9]+$/.test(text) && Number(text) <= 256
          ? "succ(".repeat(Number(text)) + "0" + ")".repeat(Number(text))
          : info?.expansion;
        const style = keywords.has(text) || builtinForms.has(text) || /^U[0-9]+$/.test(text)
          ? "keyword" : expansion ? "macro" : "";
        if (info) {
          const button = document.createElement("button");
          button.className = `reference${style ? " " + style : ""}`;
          button.textContent = text;
          button.title = expansion ? `${text} expands to ${expansion}` : `Inspect ${text}`;
          if (expansion) button.setAttribute("aria-label", button.title);
          button.dataset.name = text;
          button.onclick = () =>
            inspect({ ...decorate(info), line: index + 1 });
          code.append(button);
        } else if (style) {
          const span = document.createElement("span");
          span.className = style;
          span.textContent = text;
          if (expansion) span.title = `${text} expands to ${expansion}`;
          code.append(span);
        } else code.append(document.createTextNode(text));
      }
      cursor = token.index + text.length;
    }
    row.append(number, code);
    $("read-source").append(row);
    offset += line.length + 1;
  }
}
async function inspect(info, remember = true) {
  if (remember && selected) {
    history.push(selected);
    if (history.length > 60) history.shift();
  }
  selected = info;
  const sequence = ++inspectSerial;
  $("back").hidden = !history.length;
  $("inspect-name").textContent = info.name;
  $("inspect-kind").textContent =
    info.kind === "goal"
      ? "Goal & local assumptions"
      : (info.role ?? info.kind ?? "Definition");
  renderType(info.kind === "goal" ? info.step.goal : (info.type ?? ""));
  $("inspect-description").textContent = info.description ?? "";
  sourceLink(info);
  $("inspect-axioms").replaceChildren();
  $("locals").replaceChildren();
  $("kernel-details").hidden = info.kind === "goal";
  $("kernel-details").open = true;
  $("open-kernel-expression").disabled = true;
  $("open-kernel-type").disabled = true;
  $("kernel-expression").textContent = "";
  $("kernel-type").textContent = "";
  $("kernel-inference").textContent = "";
  $("kernel-context-list").replaceChildren();
  $("kernel-context-note").textContent = "";
  checkedKernelView = null;
  $("kernel-view").value = "notation";
  $("kernel-view").disabled = true;
  $("kernel-view-note").textContent = "";
  $("expand-kernel").hidden = true;
  $("export-folding").hidden = true;
  for (const line of document.querySelectorAll(".source-line.active"))
    line.classList.remove("active");
  if (info.line)
    document
      .querySelector(`.source-line[data-line="${info.line}"]`)
      ?.classList.add("active");
  if (info.kind === "goal") {
    if (info.step.locals.length) {
      const h = document.createElement("h3");
      h.className = "locals-title";
      h.textContent = "In scope";
      $("locals").append(h);
    }
    for (const local of info.step.locals) {
      const button = document.createElement("button");
      button.className = "local";
      button.append(document.createTextNode(local.name));
      const type = document.createElement("small");
      type.textContent = local.type;
      button.append(type);
      button.onclick = () =>
        inspect({ ...local, kind: "value", role: "Local assumption" });
      $("locals").append(button);
    }
  } else {
    try {
      const view = await request("inspect", { binding: info.binding });
      if (sequence !== inspectSerial) return;
      if (!info.type) renderType(layout(view.type, view.contextNames).text);
      renderKernel(view);
    } catch (e) {
      diagnostic(e);
    }
  }
  if (matchMedia("(max-width:1150px)").matches)
    $("inspect-name").scrollIntoView({ block: "center" });
}
function renderType(text) {
  $("inspect-type").replaceChildren();
  const symbols = new Map(
    [
      ...(last?.symbols ?? []),
      ...(last?.imports ?? []),
      ...(last?.outputs ?? []),
    ].map((v) => [v.name, v]),
  );
  for (const token of text.matchAll(
    /<=|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[+*<=>]|\s+|./g,
  )) {
    const word = token[0],
      name = { "<": "isLt", "<=": "le", "+": "add", "*": "mul" }[word] ?? word;
    let info = symbols.get(name);
    if (info) {
      info = decorate(info);
      if (name !== word)
        info = {
          ...info,
          name: word,
          role: "notation",
          description: `a ${word} b denotes ${name}(a, b), applied as (${name}(a))(b).${word === "<" ? " isLt(a, b) is le(succ(a), b)." : ""}`,
        };
      const button = document.createElement("button");
      button.className = "reference";
      button.dataset.name = word;
      button.textContent = word;
      button.onclick = () => inspect(info);
      $("inspect-type").append(button);
    } else $("inspect-type").append(document.createTextNode(word));
  }
}
let checkedKernelView = null;
function renderKernel(view) {
  checkedKernelView = view;
  $("open-kernel-expression").disabled = !view.expression;
  $("open-kernel-type").disabled = !view.type;
  const declaration = [...last.outputs, ...last.imports].find(item => item.binding === view.name);
  const mathscript = declaration?.mathscript;
  const notation = view.folded;
  $("kernel-view").disabled = false;
  $("kernel-view").querySelector('[value="mathscript"]').disabled = !mathscript;
  $("kernel-view").querySelector('[value="notation"]').disabled = !view.expression && !view.type;
  if (!mathscript && $("kernel-view").value === "mathscript") $("kernel-view").value = "notation";
  const mode = $("kernel-view").value;
  $("kernel-truncation-options").hidden = mode !== "notation";
  $("kernel-binder-options").hidden = mode !== "notation";
  $("kernel-identity-options").hidden = mode !== "notation";
  const folded = mode === "mathscript" && mathscript;
  const typeset = mode === "notation" && (notation ?? { verified: {} });
  $("kernel-view-note").textContent = typeset
    ? Object.keys(typeset.verified).length
      ? "Checked kernel term with folded definitions. The kernel verified its definitional equality to the stored term. Click a name to inspect it."
      : "Showing the stored checked kernel terms in mathematical notation; a verified folded view is unavailable."
    : folded
    ? "MathScript from the last successful check, preserving definition names and notation."
    : "Raw checked kernel representation.";
  $("kernel-expression-label").textContent = folded?.expressionKind === "declaration" ? "Declaration" : "Expression";
  renderAxioms($("inspect-axioms"), view.axioms ?? []);
  const symbols = new Map([...(last.symbols ?? []), ...(last.localViews ?? []), ...last.imports, ...last.outputs].map(info => [info.binding, info]));
  for (const binding of view.axioms ?? []) symbols.set(binding, axiomInfo(binding));
  for (const entry of view.context?.entries ?? []) {
    if (!entry.binding) continue;
    symbols.set(entry.binding, { ...symbols.get(entry.binding), name: entry.name, binding: entry.binding, role: "Kernel context assumption" });
  }
  const navigation = { resolve: binding => symbols.get(binding), inspect: info => inspect(decorate(info)),
    truncationSugar: $("kernel-truncation-sugar").checked,
    identitySugar: $("kernel-identity-sugar").checked,
    groupIndependentBinders: $("kernel-group-binders").checked };
  $("kernel-context-note").textContent = view.assumptions.length
    ? "Open assumptions of this checked judgement. Click a name to inspect its type and source. Π, Σ and λ bind variables inside the term."
    : "Empty context. Π, Σ and λ bind variables inside the term.";
  $("kernel-context-list").replaceChildren();
  for (const entry of view.context?.entries ?? []) {
    const row = document.createElement("li");
    row.className = "kernel-context-row";
    row.dataset.contextId = entry.id;
    row.dataset.name = entry.name;
    const label = document.createElement("span");
    const name = document.createElement("button");
    name.className = "reference";
    name.dataset.name = entry.name;
    name.textContent = entry.name;
    name.title = `Inspect context assumption ${entry.name}`;
    name.disabled = !entry.binding;
    name.onclick = () => { if (entry.binding) navigation.inspect(symbols.get(entry.binding)); };
    label.append(name, document.createTextNode(" : "));
    const type = document.createElement("div");
    type.className = "kernel-term kernel-context-type";
    const certified = mode === "notation" && entry.folded;
    if (mode === "raw") type.textContent = layout(entry.type, view.contextNames).text;
    else {
      type.classList.add("typeset");
      renderMathNotation(type, kernelMathTree(certified?.type ?? entry.type, certified?.references ?? {},
        certified?.contextNames ?? view.contextNames, certified?.contextReferences ?? view.context?.references ?? {},
        certified?.declarations ?? view.declarations, certified?.axiomNotation ?? view.axiomNotation), navigation);
    }
    row.append(label, type);
    $("kernel-context-list").append(row);
  }
  for (const side of ["expression", "type"]) {
    const container = $("kernel-" + side);
    const tree = typeset && (typeset[side] ?? view[side]);
    container.classList.toggle("typeset", !!tree);
    if (tree) renderMathNotation(container, kernelMathTree(tree, typeset[side] ? typeset.references : {},
      typeset[side] ? typeset.contextNames ?? view.contextNames : view.contextNames,
      typeset[side] ? typeset.contextReferences ?? {} : view.context?.references ?? {},
      typeset[side] ? typeset.declarations ?? {} : view.declarations,
      typeset[side] ? typeset.axiomNotation ?? {} : view.axiomNotation), navigation);
    else container.textContent = folded ? mathscript[side] : view[side]
      ? layout(view[side], view.contextNames).text : "Context assumption";
  }
  if (typeset && Object.keys(typeset.verified).length && (!typeset.expression || !typeset.type))
    $("kernel-view-note").textContent += " Where folding could not be verified, the stored term is typeset directly.";
  $("export-folding").hidden = !typeset || !Object.keys(typeset.verified).length;
  $("kernel-inference").textContent =
    `${view.inference?.op ?? view.kind}. ${view.assumptions.length ? view.assumptions.length + " open assumptions." : "Closed judgement."}`;
  $("kernel-premises").replaceChildren();
  for (const binding of [
    ...(view.inference?.args ?? []),
    view.inference?.context,
    ...(view.inference?.free ?? []),
  ].filter(Boolean)) {
    const button = document.createElement("button");
    button.className = "reference";
    button.textContent = binding;
    button.onclick = () =>
      inspect(decorate({ binding, name: binding, role: "checked premise" }));
    $("kernel-premises").append(button, document.createTextNode(" "));
  }
  const truncated = (n) => n && (n.truncated || n.children.some(truncated));
  $("expand-kernel").hidden =
    !!folded || (!truncated(typeset?.expression ?? view.expression) && !truncated(typeset?.type ?? view.type));
}
$("kernel-view").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
$("kernel-truncation-sugar").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
$("kernel-group-binders").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
$("kernel-identity-sugar").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
for (const side of ["expression", "type"]) $("open-kernel-" + side).onclick = async () => {
  if (!checkedKernelView) return;
  const binding = checkedKernelView.name;
  const folded = $("kernel-view").value === "notation" && !!checkedKernelView.folded?.verified[side];
  const tab = window.open("about:blank", "_blank");
  if (!tab) { diagnostic(new Error("Allow a new tab to open the kernel workbench.")); return; }
  tab.document.body.textContent = "Preparing checked expression…";
  try {
    const payload = await request("export-inspection", { binding, side, folded });
    const key = await saveWorkbenchTransfer(payload);
    tab.location.href = new URL(`workbench.html?transfer=${encodeURIComponent(key)}`, location.href).href;
  } catch (error) { tab.close(); diagnostic(error); }
};
$("export-folding").onclick = async () => {
  if (!checkedKernelView) return;
  const binding = checkedKernelView.name;
  try {
    const certificate = await request("export-folding", { binding });
    if (certificate) download(JSON.stringify(certificate, null, 2), `${binding}-folding.json`, "application/json");
  } catch (error) { diagnostic(error); }
};
function download(text, name, type) {
  const url = URL.createObjectURL(new Blob([text], { type })),
    a = document.createElement("a");
  a.href = url;
  a.download = name;
  a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
$("check").onclick = check;
for (const id of ["reuse-normal-forms", "memoize-instructions"]) $(id).onchange = () => {
  try { localStorage.setItem("mathscript:" + id, String($(id).checked)); } catch {}
  check();
};
$("read-mode").onclick = () => setMode("read");
$("edit-mode").onclick = () => setMode("edit");
$("editor").oninput = () => {
  refreshStatus();
  rememberDraft();
};
$("show-intermediate").onchange = () => {
  renderSource();
  renderLibrary();
};
$("editor").onkeydown = (e) => {
  if ((e.ctrlKey || e.metaKey) && e.key === "Enter") {
    e.preventDefault();
    if (ready && !pending.size) check();
  }
};
$("search").oninput = renderLibrary;
$("back").onclick = () => {
  const previous = history.pop();
  if (previous) inspect(previous, false);
};
$("save").onclick = () =>
  download($("editor").value, proofId + ".proof", "text/plain");
$("export").onclick = async () => {
  try {
    download(
      JSON.stringify(await request("export"), null, 2),
      "proof.thth.json",
      "application/json",
    );
  } catch (e) {
    diagnostic(e);
  }
};
$("open").onclick = () => $("file").click();
$("file").onchange = async () => {
  try {
    const file = $("file").files[0];
    if (!file) return;
    if (file.size > 1000000) throw new Error("Source exceeds 1 MB.");
    $("editor").value = await file.text();
    if (ready) await check();
  } catch (e) {
    diagnostic(e);
  } finally {
    $("file").value = "";
  }
};
$("expand-kernel").onclick = async () => {
  try {
    const item = selected,
      view = await request("inspect", {
        binding: item.binding,
        expand: ["expression", "type"],
      });
    if (selected === item) renderKernel(view);
  } catch (e) {
    diagnostic(e);
  }
};
$("guide-link").href = "#language-guide";
$("guide-link").onclick = () => {
  $("language-guide").open = true;
};
let workerVersion = null;
async function serverVersion() {
  try {
    const r = await fetch("mathscript-version", { cache: "no-store" });
    return r.ok ? (await r.json()).version : null;
  } catch {
    return null;
  }
}
async function refreshCompiler() {
  if (pending.size || !ready) return false;
  const version = await serverVersion();
  if (!version || version === workerVersion) return false;
  ready = false;
  showChecking(true, "Updating proof checker…");
  worker.terminate();
  last = null;
  $("result").hidden = true;
  $("source-notice").hidden = false;
  $("source-notice").textContent =
    "The compiler was updated. Rechecking your current source; edits are preserved.";
  await startWorker(version);
  return true;
}
async function startWorker(version = undefined) {
  workerVersion = version ?? (await serverVersion());
  const url = new URL("./mathscript/worker.mjs", import.meta.url);
  if (workerVersion) url.searchParams.set("version", workerVersion);
  worker = new Worker(url, { type: "module" });
  worker.onmessage = ({ data }) => {
    if (data.ready) {
      if (data.maxSteps < 4194304) {
        diagnostic(
          new Error(
            "An outdated compiler was loaded. Reload this page to update the worker.",
          ),
        );
        worker.terminate();
        ready = false;
        return;
      }
      ready = true;
      refreshStatus();
      check();
      return;
    }
    const p = pending.get(data.id);
    if (!p) return;
    if (data.progress) {
      p.watchdog.progress(data.progress);
      checkingProgress(data.progress);
      return;
    }
    pending.delete(data.id);
    p.watchdog.stop();
    if (data.error)
      p.reject(Object.assign(new Error(data.error.message), data.error));
    else p.resolve(data.result);
    refreshStatus();
  };
  worker.onerror = (e) => {
    ready = false;
    worker.terminate();
    for (const p of pending.values()) {
      p.watchdog.stop();
      p.reject(new Error(e.message || "Unable to load the checking worker."));
    }
    pending.clear();
    diagnostic(
      new Error(
        e.message ||
          "Unable to load the checking worker. Build with make wasm.",
      ),
    );
    refreshStatus();
  };
}
addEventListener("focus", () => {
  refreshCompiler().catch(diagnostic);
});
addEventListener("pageshow", (event) => {
  if (event.persisted) refreshCompiler().catch(diagnostic);
});
await startWorker();
