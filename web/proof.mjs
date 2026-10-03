import { splitInspectionContext } from "./cubical-context.mjs";
import { cubicalSourceFile } from "./cubical-sources.mjs";
import { proofCatalog, proofTopics, proofsInTopic } from "./proof-library.mjs";
import { proofRequestWatchdog } from "./proof-watchdog.mjs";
import { renderMathNotation } from "./math-notation.mjs";
import { axiomLabels } from "./axiom-labels.mjs";
import { saveWorkbenchTransfer } from "./workbench-transfer.mjs";
import { readProofNavigation, saveProofNavigation, proofReturnURL } from "./proof-navigation.mjs";
import { cubicalMathTree } from "./cubical-notation.mjs";
import { boundedSyntaxJson, syntaxDisplayLimitMessage } from "./cubical-json.mjs";
import { numeralAt, tokenStyle, headerWordAt } from "./source-tokens.mjs";
import { cubistTestModules, libraryModules } from "./cubist/modules.mjs";
import { enableTokenTips } from "./token-tips.mjs";
import { createReplConsole } from "./repl-console.mjs";
import { withCode } from "./diagnostics.mjs";

const query = new URLSearchParams(location.search);
const backend = "cubical";
// A reference example is not a library proof: its source comes from the URL
// fragment (#source=…), or, when embedded in a reference page, by message.
const exampleMode = query.has("example"), embedded = exampleMode && query.has("embed");
// A module of the rebuilt library opens like a proof, from library/, and so
// does a Cubist test, from cubist-tests/.
const libraryModule = !exampleMode && libraryModules.includes(query.get("proof"));
const testModule = !exampleMode && !libraryModule && cubistTestModules.includes(query.get("proof"));
const proofId = exampleMode ? "reference_example"
  : libraryModule || testModule || proofCatalog.some((p) => p.id === query.get("proof")) ? query.get("proof")
  : "euclid";
const catalogEntry = proofCatalog.find((p) => p.id === proofId);
const sourceURL = exampleMode ? null
  : libraryModule ? `library/${proofId}.cubist`
  : testModule ? `cubist-tests/${proofId}.cubist`
  : `archive/first-library/${cubicalSourceFile(proofId)}`;
const snapshot = readProofNavigation(query.get("restore"));
let restoring = snapshot?.proof === proofId ? snapshot : null;
const crossFileBack = restoring?.back ?? query.get("back");
function exampleSource() {
  const encoded = new URLSearchParams(location.hash.slice(1)).get("source");
  if (!encoded) return "";
  try { return new TextDecoder().decode(Uint8Array.from(atob(encoded.replace(/-/g, "+").replace(/_/g, "/")), c => c.charCodeAt(0))); }
  catch { return ""; }
}
let original;
if (exampleMode) original = exampleSource();
else {
  const response = await fetch(sourceURL, { cache: "no-store" });
  if (!response.ok) throw new Error("Unable to load source: " + sourceURL);
  original = await response.text();
}
document.body.classList.toggle("embedded", embedded);
let savedDraft = null,
  previousDraft = null,
  sourceNotice = "";
try {
  // An example always opens with the source it was given. Storage keys keep
  // the language's former name, MathScript, so saved drafts still load.
  const stored = exampleMode ? null : sessionStorage.getItem("mathscript:" + proofId);
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
const example = restoring?.source ?? savedDraft ?? original;
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
for (const id of ["share-syntax", "reuse-checks", "compact-paths"]) {
  $(id).checked = true;
  try { $(id).checked = localStorage.getItem("mathscript:" + id) !== "false"; } catch {}
}
$("proof-title").textContent = catalogEntry?.title
  ?? (libraryModule ? `Library: ${proofId}` : testModule ? `Cubist test: ${proofId}` : "Reference example");
$("development-note").hidden = !catalogEntry?.realDevelopment;
$("puncture-note").hidden = !catalogEntry?.punctureDevelopment;
$("complex-note").hidden = !catalogEntry?.complexDevelopment;
$("archive-note").hidden = exampleMode || libraryModule || testModule;
$("test-note").hidden = !testModule;
$("source-file").hidden = exampleMode;
$("repository-source").hidden = exampleMode;
if (sourceURL) {
  $("source-file").href = sourceURL;
  $("source-file").textContent = `web/${sourceURL}`;
}
$("repository-source").href =
  `proof.html?proof=${encodeURIComponent(proofId)}&source=repo`;
$("source-notice").textContent = sourceNotice;
$("source-notice").hidden = !sourceNotice;
$("previous-draft").hidden = !previousDraft;
$("previous-draft").onclick = () =>
  download(previousDraft, proofId + "-previous.cubist", "text/plain");
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
    prompt.textContent = "Select a proof…";
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
$("proof-topic").value = catalogEntry?.topic ?? proofTopics[0].id;
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
    $("check-detail").textContent = "0 kernel steps\n0 declarations processed\nLoading proof…";
  }
}
function checkingProgress(progress) {
  const { completed, total, current, unit, instructions } = progress;
  const knownTotal = Number.isFinite(total) && total >= completed;
  if (knownTotal) {
    $("check-progress").max = Math.max(1, total);
    $("check-progress").value = completed;
  } else $("check-progress").removeAttribute("value");
  $("check-message").textContent = total && completed === total
    ? "Preparing checked results…"
    : progress.phase === "loading" ? "Reading source imports…" : "Checking proof…";
  $("check-detail").textContent =
    `${(instructions ?? 0).toLocaleString()} kernel steps\n` +
    `${completed.toLocaleString()}${knownTotal ? ` of ${total.toLocaleString()}` : ""} ${unit} ${backend === "cubical" ? "processed" : "checked"}` +
    (current ? `\n${progress.phase === "checking" ? "Checking " : ""}${current}` : "");
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
  return {
    shareSyntax: $("share-syntax").checked, reuseChecks: $("reuse-checks").checked,
    compactPaths: $("compact-paths").checked,
  };
}
function refreshStatus() {
  $("check").disabled = !ready || pending.size > 0;
  for (const id of ["share-syntax", "reuse-checks", "compact-paths"])
    $(id).disabled = !ready || pending.size > 0 || !Object.keys(compilerOptimizations()).length;
  $("export").disabled = !last || pending.size > 0;
  $("dirty").textContent = dirty()
    ? "Edited — changes are not checked. Read shows the last checked version."
    : "";
  $("status").textContent = pending.size
    ? "Checking…"
    : last
      ? `Cubical C · ${last.complete ? `checked · ${last.axiomCount ? `${last.axiomCount} explicit assumptions` : "no axioms"}` : "check incomplete"}`
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
let focusOffset = null, queuedExample = null;
// Check an example sent by the embedding reference page, then inspect the
// name the reader clicked.
async function runExample({ source, offset }) {
  if (!ready) { queuedExample = { source, offset }; return; }
  queuedExample = null;
  $("editor").value = source;
  focusOffset = Number.isInteger(offset) ? offset : null;
  await check();
}
if (embedded) addEventListener("message", ({ data, origin }) => {
  if (origin !== location.origin || data?.type !== "cubist-inspect" || typeof data.source !== "string") return;
  runExample(data);
});
async function check() {
  showChecking(true);
  if (await refreshCompiler()) return;
  $("diagnostic").hidden = true;
  const source = $("editor").value;
  try {
    // Where the source came from decides where its imports are found
    // (module-resolution.mjs): an archive proof imports only from the archive.
    const place = exampleMode ? null : libraryModule ? "library" : testModule ? "tests" : "archive";
    const result = await request("check", { source, module: proofId, place, optimizations: compilerOptimizations() });
    last = result;
    history.length = 0;
    renderSource();
    renderResult();
    setMode("read");
    const target = query.get("name");
    const info =
      target &&
      [...(result.declarations ?? []), ...result.outputs].find(
        (d) => d.binding === target || (backend === "cubical" && d.name === target),
      );
    if (restoring) {
      const saved = restoring;
      restoring = null;
      history.push(...saved.history);
      await inspect(saved.selected ?? decorate(result.outputs.at(-1)), false);
      $("read-source").scrollTop = saved.sourceScroll ?? 0;
      window.scrollTo(0, saved.scroll ?? 0);
    } else {
      const fallback = result.outputs.at(-1);
      // An embedding page asks for the name at a source offset.
      const focus = focusOffset === null ? null : [...result.links].filter(link => link.start === focusOffset)
        .sort((a, b) => a.end - a.start - (b.end - b.start))[0];
      focusOffset = null;
      if (focus) await inspect({ ...decorate(focus), line: result.source.slice(0, focus.start).split("\n").length }, false);
      else if (info ?? fallback) await inspect(decorate(info ?? fallback), false);
      // Embedded, the inspector is on top and the source below stays in place.
      if (focus && !embedded) revealSource(focus);
      else if (info) revealSource(info);
    }
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
      : last?.backend === "cubical" ? "Click a name or numeral to inspect its checked type, context, and definition."
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
      ["local", "parameter", "def"].includes(d.role),
  );
  const output = last?.outputs.find(d => d.binding === info.binding && d.name === info.name);
  const value = { ...declaration, ...output, ...info, ...imported, kind: "value" };
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
    link.onclick = () => {
      const address = new URL(link.href);
      address.searchParams.set("back", rememberInspection());
      link.href = address.href;
    };
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

function axiomInfo(binding) {
  return decorate({ binding, name: last.assumptionLabels?.[binding] ?? binding, role: "explicit axiom",
    ...[...last.outputs, ...last.imports].find(o => o.binding === binding),
  });
}
// A diagnostic's code, linked to its entry in the errors chapter, and the
// separator after it; nothing for a message without a code.
function codeLink(code) {
  if (!code) return [];
  const link = document.createElement("a");
  link.href = `reference/errors.html#${code}`;
  link.target = "_blank";
  link.rel = "noopener";
  link.className = "diagnostic-code";
  link.textContent = code;
  return [link, " "];
}
function renderAxioms(target, axioms, extensions = []) {
  target.replaceChildren(document.createTextNode("Axioms used: "));
  // A kernel extension under review is listed apart: it is not an assumption,
  // and the result still computes.
  const marker = () => {
    if (!extensions.length) return;
    const note = document.createElement("span");
    note.className = "kernel-extensions";
    note.textContent = ` · ${extensions.map(name => `kernel extension: ${name}`).join(", ")}`;
    note.title = "Relies on a kernel extension under review. It is not an assumption, and the result still computes.";
    target.append(note);
  };
  if (!axioms.length) {
    target.append("None");
    marker();
    return;
  }
  for (const [index, binding] of axioms.entries()) {
    if (index) target.append(document.createTextNode(", "));
    const button = document.createElement("button");
    button.className = "reference";
    button.dataset.axiom = binding;
    button.textContent = last.assumptionLabels?.[binding] ?? axiomLabels[binding] ?? binding;
    button.title = `Inspect ${binding} and its declared type`;
    button.onclick = () => inspect(axiomInfo(binding));
    target.append(button);
  }
  marker();
}
function renderResult() {
  $("result").hidden = !last;
  $("result").replaceChildren();
  if (!last) return;
  for (const output of last.outputs) {
    const line = document.createElement("div");
    line.append(
      output.verified === false && last.backend === "cubical" ? "Not checked " : output.kind === "axiom" ? "Axiom " : last.mode !== "construction" || output.verified
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
    if (last.backend === "cubical" && !output.verified) dependencies.append(...codeLink(output.code), output.reason);
    else renderAxioms(dependencies, output.axioms ?? [], output.extensions ?? []);
    line.append(dependencies);
    $("result").append(line);
  }
  // Lint warnings: bindings that are never used and can be removed.
  for (const warning of last.warnings ?? []) {
    const line = document.createElement("div"), at = document.createElement("button");
    line.className = "lint-warning";
    at.textContent = `line ${warning.line}`;
    at.onclick = () => revealSource(warning);
    line.append("Warning ", ...codeLink(warning.code), "at ", at, `: ${warning.message}`);
    $("result").append(line);
  }
  const detail = document.createElement("small");
  detail.textContent = `${last.instructionCount.toLocaleString()} checked instructions. ${last.axiomCount ? last.axiomCount + " explicit axioms in this module." : "No axioms."}`;
  $("result").append(detail);
}
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
  $("source-count").textContent = `${last.source.split("\n").length} lines · click a name or numeral`;
  let offset = 0;
  for (const [index, line] of last.source.split("\n").entries()) {
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
      /\/\/.*|(?:<=|->|=>)|0b[01]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[+*<=>]|\s+|./g,
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
        link.href = `proof.html?proof=${encodeURIComponent(text)}`;
        link.title = `Open ${text} module source`;
        link.onclick = () => {
          const address = new URL(link.href);
          address.searchParams.set("back", rememberInspection());
          link.href = address.href;
        };
        code.append(link);
      } else {
        const info = linkMap.get(start);
        const expansion = (last.mode === "mathematical" ? numeralAt(line, token.index, text) : null) ?? info?.expansion;
        // The whole source: a header's colon and its inductive may be on earlier lines.
        const style = tokenStyle(text, expansion, headerWordAt(last.source, start, text));
        if (info) {
          const button = document.createElement("button");
          button.className = `reference${style ? " " + style : ""}`;
          button.textContent = text;
          if (expansion && expansion !== text) {
            button.dataset.tip = `${text} expands to ${expansion}`;
            button.setAttribute("aria-label", button.dataset.tip);
          } else button.title = `Inspect ${text}`;
          button.dataset.name = text;
          button.onclick = () =>
            inspect({ ...decorate(info), line: index + 1 });
          code.append(button);
        } else if (style) {
          const span = document.createElement("span");
          span.className = style;
          span.textContent = text;
          if (expansion && expansion !== text) span.dataset.tip = `${text} expands to ${expansion}`;
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
function renderWitnessDetails(info) {
  $("inspect-description").textContent = info.description ?? "";
  const trace=$("rewrite-trace");
  trace.replaceChildren();trace.hidden=!info.rewriteSteps?.length;
  for(const step of info.rewriteSteps??[]) {
    const button=document.createElement("button");
    button.className="reference";
    button.textContent=step.description;
    button.onclick=()=>inspect(decorate(step));
    trace.append(button);
  }
  const freeze=$("freeze-simp");
  freeze.hidden=!info.freeze;
  freeze.disabled=dirty();
  freeze.onclick=async()=>{
    const edit=info.freeze;
    if(!edit||!last||dirty()||last.source.slice(edit.start,edit.end)!==edit.original) {
      diagnostic(Error("Recheck the current source before replacing this simplification."));
      return;
    }
    $("editor").value=last.source.slice(0,edit.start)+edit.text+last.source.slice(edit.end);
    $("editor").dispatchEvent(new Event("input",{bubbles:true}));
    await check();
  };
}
async function inspect(info, remember = true) {
  if (remember && selected) {
    history.push(selected);
    if (history.length > 60) history.shift();
  }
  selected = info;
  const sequence = ++inspectSerial;
  $("back").hidden = !history.length && !proofReturnURL(crossFileBack);
  $("inspect-name").textContent = info.name;
  $("inspect-kind").textContent =
    info.kind === "goal"
      ? "Goal & local assumptions"
      : (info.role ?? info.kind ?? "Definition");
  $("inspect-statement-label").hidden = true;
  $("inspect-parameters").hidden = true;
  $("inspect-parameters").open = false;
  $("inspect-parameters-list").replaceChildren();
  renderType(info.kind === "goal" ? info.step.goal : (info.type ?? ""));
  renderWitnessDetails(info);
  sourceLink(info);
  $("inspect-axioms").replaceChildren();
  $("inspect-signature").hidden = true;
  $("locals").replaceChildren();
  $("kernel-details").hidden = info.kind === "goal";
  $("kernel-terms").hidden = info.kind === "goal";
  $("kernel-details").open = true;
  $("open-kernel-expression").disabled = true;
  $("open-kernel-type").disabled = true;
  $("open-kernel-assembly").hidden = true;
  $("open-kernel-assembly").disabled = true;
  $("kernel-expression").textContent = "";
  $("kernel-type").textContent = "";
  $("kernel-inference").textContent = "";
  $("kernel-context-list").replaceChildren();
  $("kernel-context-note").textContent = "";
  $("kernel-axioms-list").replaceChildren();
  $("kernel-axioms").hidden = true;
  checkedKernelView = null; showKernelBody = false; kernelDisplayLimit = 1200;
  $("toggle-kernel-body").hidden = true;
  $("kernel-local-definitions").hidden = true;
  $("kernel-view").value = "notation";
  $("kernel-view").disabled = true;
  $("kernel-view-note").textContent = "";
  $("expand-kernel").hidden = true;
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
      type.textContent = local.relation === "<" ? `< ${local.type}` : local.type;
      button.append(type);
      button.onclick = () =>
        inspect({ ...local, kind: "value", role: "Local assumption" });
      $("locals").append(button);
    }
  } else {
    if (last.backend === "cubical" && info.verified === false) {
      $("kernel-details").hidden = true;
      $("kernel-terms").hidden = true;
      $("inspect-description").textContent = `Not checked by cubical C: ${withCode(info.reason, info.code)}`;
      return;
    }
    // A declared type has no checked term: its signature and eliminator.
    const declared = last.backend === "cubical" && [info.kind, info.role].includes("inductive");
    if (declared) {
      $("kernel-details").hidden = true;
      $("kernel-terms").hidden = true;
    }
    try {
      if (declared) {
        const view = await request("signature", { binding: info.binding });
        if (sequence !== inspectSerial) return;
        if (view) renderSignature(view);
      } else {
        const view = await request("inspect", { binding: info.binding });
        if (sequence !== inspectSerial) return;
        if (view.statement) renderStatement(view);
        else renderType(view.typeText, Object.values(view.symbols));
        renderKernel(view);
      }
    } catch (e) {
      if (sequence === inspectSerial) diagnostic(e);
    }
  }
  if (embedded) scrollTo(0, 0);
  else if (matchMedia("(max-width:1150px)").matches)
    $("inspect-name").scrollIntoView({ block: "center" });
}
// A declared type: its former, its constructors in the kernel's normal form
// with their shapes, and the clause type the eliminator asks for each
// constructor, for a motive P (the H1 specification's 6.5).
function renderSignature(view) {
  const plural = (count, word) => `${count} ${word}${count === 1 ? "" : "s"}`;
  const item = (text, note) => {
    const row = document.createElement("li"), code = document.createElement("code");
    code.textContent = text;
    row.append(code);
    if (note) {
      const small = document.createElement("small");
      small.textContent = note;
      row.append(small);
    }
    return row;
  };
  $("inspect-kind").textContent = `Declared type · ${view.modifier}`;
  renderType(view.former);
  $("inspect-signature").hidden = false;
  $("inspect-signature-recorded").hidden = !view.recorded.length;
  $("inspect-signature-recorded").textContent = `Recorded universe parameters: ${view.recorded.join(", ")}`;
  $("inspect-constructors").replaceChildren(...view.constructors.map(c => item(`${c.name} : ${c.type}`,
    `${c.data} data · ${plural(c.positions, "position")} · ${plural(c.dimensions, "dimension")}${c.generated ? " · generated" : ""}`)));
  const eliminator = view.eliminator;
  $("inspect-eliminator").hidden = !eliminator;
  $("inspect-eliminator-motive").textContent = eliminator ? `For a motive ${eliminator.motive}, one clause per constructor:` : "";
  $("inspect-clauses").replaceChildren(...(eliminator?.clauses ?? []).map(clause => item(`${clause.name} : ${clause.type}`)),
    ...(eliminator?.error ? [item("…", `The remaining clause types could not be computed: ${eliminator.error}`)] : []));
  renderAxioms($("inspect-axioms"), [], view.extensions ?? []);
}
function renderStatement(view) {
  const append = (target, parts) => {
    for (const part of parts) {
      const info = part.binding && view.symbols[part.binding];
      if (!info) { target.append(document.createTextNode(part.text)); continue; }
      const button = document.createElement("button"); button.className = "reference";
      button.textContent = part.text; button.dataset.name = part.text;
      button.onclick = () => inspect(decorate(info)); target.append(button);
    }
  };
  const { conclusion, parameters } = view.statement;
  $("inspect-type").replaceChildren(); append($("inspect-type"), conclusion);
  $("inspect-statement-label").hidden = !parameters.length;
  $("inspect-parameters").hidden = !parameters.length;
  $("inspect-parameters-label").textContent = `Parameters and hypotheses (${parameters.length})`;
  $("inspect-parameters-list").replaceChildren();
  for (const parameter of parameters) {
    const row = document.createElement("div"); row.className = "statement-parameter";
    const name = document.createElement("span"), type = document.createElement("span");
    append(name, parameter.name);
    append(type, parameter.type);
    row.append(name, ` ${parameter.relation} `, type);
    $("inspect-parameters-list").append(row);
  }
}
function renderType(text, extraSymbols = []) {
  $("inspect-type").replaceChildren();
  const symbols = new Map(
    [
      ...(last?.symbols ?? []),
      ...(last?.imports ?? []),
      ...(last?.outputs ?? []),
      ...extraSymbols,
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
let checkedKernelView = null, showKernelBody = false, kernelDisplayLimit = 1200;
function renderKernel(view) {
  checkedKernelView = view;
  renderCubicalKernel(view);
}
function renderCubicalKernel(view) {
  $("open-kernel-assembly").hidden = false;
  $("open-kernel-assembly").disabled = false;
  const mode = $("kernel-view").value, raw = mode === "raw", folded = mode === "notation";
  const display = folded ? view.folded ?? view : view;
  const { context, axioms } = splitInspectionContext(view, display.context);
  const open = view.context.length || view.dimensions?.length;
  const localContext = context.length || view.dimensions?.length;
  $("kernel-view").disabled = false;
  $("kernel-view").querySelector('[value="expanded"]').hidden = false;
  $("kernel-view-note").textContent = folded
    ? "Checked cubical terms with source names. Type applications are simplified and local names abbreviate their checked expressions. Select stored notation or raw syntax to inspect every constructor."
    : raw ? "Raw checked syntax, including annotations and internal names."
    : "Stored checked syntax in mathematical notation, with source labels for bound variables.";
  $("kernel-inference").textContent = `Cubical C · ${open ? "Open judgement" : "Closed judgement"}`;
  $("kernel-premises").replaceChildren();
  $("kernel-context-note").textContent = localContext ? "Local assumptions · click a name to inspect it" : "Empty context";
  $("kernel-axioms").hidden = !axioms.length;
  $("kernel-axioms-list").replaceChildren();
  $("kernel-context-list").replaceChildren();
  const navigation = { resolve: binding => view.symbols[binding], inspect: info => inspect(decorate(info)),
    identitySugar: $("kernel-identity-sugar").checked, truncationSugar: $("kernel-truncation-sugar").checked,
    groupIndependentBinders: false };
  if (view.dimensions?.length) {
    const row = document.createElement("li");
    row.textContent = `Interval coordinates: ${view.dimensions.map(([name]) => name).join(", ")}`;
    $("kernel-context-list").append(row);
  }
  const render = (target, term) => {
    target.classList.toggle("typeset", !raw);
    if (raw) target.textContent = boundedSyntaxJson(term) ?? syntaxDisplayLimitMessage;
    else renderMathNotation(target, cubicalMathTree(term, view.symbols, kernelDisplayLimit), navigation);
  };
  for (const [list, entries] of [["kernel-context-list", context], ["kernel-axioms-list", axioms]]) for (const entry of entries) {
    const row = document.createElement("li"); row.className = "kernel-context-row"; row.dataset.name = entry.label;
    const label = document.createElement("span"), button = document.createElement("button");
    button.className = "reference"; button.textContent = entry.label; button.dataset.name = entry.label;
    button.disabled = !entry.binding;
    button.onclick = () => navigation.inspect(view.symbols[entry.binding]);
    // A universe variable's entry is its bound: U < UU0.
    label.append(button, entry.type?.tag === "LBound" ? " < " : " : ");
    const value = document.createElement("div"); value.className = "kernel-term kernel-context-type";
    render(value, entry.type); row.append(label, value); $(list).append(row);
  }
  const locals = view.locals ?? [];
  $("kernel-local-definitions").hidden = !locals.length;
  $("kernel-local-links").replaceChildren(...locals.map(local => {
    const button = document.createElement("button"); button.className = "reference";
    button.textContent = local.name; button.dataset.name = local.name;
    button.onclick = () => navigation.inspect(view.symbols[local.binding]); return button;
  }));
  $("toggle-kernel-body").hidden = !folded || !display.reference;
  $("toggle-kernel-body").textContent = showKernelBody ? "Fold expression" : "Show body";
  $("toggle-kernel-body").setAttribute("aria-expanded", String(showKernelBody));
  for (const side of ["expression", "type"]) {
    $("open-kernel-" + side).disabled = false;
    render($("kernel-" + side), side === "expression" && folded && display.reference && !showKernelBody ? display.reference : display[side]);
  }
  $("kernel-truncation-options").hidden = raw;
  $("kernel-binder-options").hidden = true;
  $("kernel-identity-options").hidden = raw;
  $("expand-kernel").textContent = "Show more of the term";
  $("expand-kernel").hidden = raw || !["kernel-expression", "kernel-type", "kernel-context-list", "kernel-axioms-list"].some(id => $(id).textContent.includes("…"));
  renderAxioms($("inspect-axioms"), view.axioms ?? [], view.extensions ?? []);
}
$("toggle-kernel-body").onclick = () => { showKernelBody = !showKernelBody; renderKernel(checkedKernelView); };
$("widen-inspector").onclick = () => {
  const wide = document.querySelector(".workspace").classList.toggle("inspector-wide");
  $("widen-inspector").textContent = wide ? "Narrow" : "Widen";
  $("widen-inspector").setAttribute("aria-pressed", String(wide));
};

$("kernel-view").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
$("kernel-truncation-sugar").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
$("kernel-group-binders").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
$("kernel-identity-sugar").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
// The workbench opens on the kernel graph: the judgements the instruction
// kernel derives for the term.
async function openKernelWorkbench(side, representation = "graph") {
  if (!checkedKernelView) return;
  const binding = checkedKernelView.name;
  const folded = $("kernel-view").value === "notation" && !!checkedKernelView.folded?.verified?.[side];
  // Save before opening the tab, so its sessionStorage clone includes the
  // return selection even if the workbench transfer is prepared asynchronously.
  const returnURL = proofReturnURL(rememberInspection());
  const tab = window.open("about:blank", "_blank");
  if (!tab) { diagnostic(new Error("Allow a new tab to open the kernel workbench.")); return; }
  tab.document.body.textContent = "Preparing checked expression…";
  try {
    const payload = await request("export-inspection", { binding, side, folded });
    payload.proofReturn = returnURL;
    const key = await saveWorkbenchTransfer(payload);
    const page = "workbench.html";
    tab.location.href = new URL(`${page}?transfer=${encodeURIComponent(key)}&view=${representation}`, location.href).href;
  } catch (error) { tab.close(); diagnostic(error); }
}
for (const side of ["expression", "type"]) $("open-kernel-" + side).onclick = () => openKernelWorkbench(side);
$("open-kernel-assembly").onclick = () => openKernelWorkbench("expression", "assembly");
function download(text, name, type) {
  const url = URL.createObjectURL(new Blob([text], { type })),
    a = document.createElement("a");
  a.href = url;
  a.download = name;
  a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
$("check").onclick = check;
for (const id of ["share-syntax", "reuse-checks", "compact-paths"]) $(id).onchange = () => {
  try { localStorage.setItem("mathscript:" + id, String($(id).checked)); } catch {}
  check();
};
$("read-mode").onclick = () => setMode("read");
$("edit-mode").onclick = () => setMode("edit");
$("editor").oninput = () => {
  refreshStatus();
  rememberDraft();
};
$("editor").onkeydown = (e) => {
  if ((e.ctrlKey || e.metaKey) && e.key === "Enter") {
    e.preventDefault();
    if (ready && !pending.size) check();
  }
};
function rememberInspection() {
  return saveProofNavigation({ proof: proofId, backend, source: last.source,
    selected, history, back: crossFileBack, scroll: window.scrollY,
    sourceScroll: $("read-source").scrollTop });
}
$("back").onclick = () => {
  const previous = history.pop();
  if (previous) inspect(previous, false);
  else {
    const address = proofReturnURL(crossFileBack);
    if (address) location.href = address;
  }
};
$("save").onclick = () =>
  download($("editor").value, proofId + ".cubist", "text/plain");
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
$("expand-kernel").onclick = () => {
  if (checkedKernelView) { kernelDisplayLimit *= 4; renderKernel(checkedKernelView); }
};
// Links within the page, to the quick reference and its topics, scroll to
// their target and move focus there without replacing the URL's fragment:
// an example's source lives in #source=…, and reloading or sharing the URL
// must reopen it. A modified click keeps the browser's own behavior.
function followInPageLink(event) {
  const link = event.target instanceof Element ? event.target.closest('a[href^="#"]') : null;
  if (!link || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
  const target = document.getElementById(link.getAttribute("href").slice(1));
  if (!target) return;
  event.preventDefault();
  $("language-guide").open ||= target === $("language-guide") || $("language-guide").contains(target);
  const focus = target.matches("details") ? target.querySelector("summary") : target;
  if (!focus.matches("a[href], button, input, select, textarea, summary, [tabindex]")) focus.setAttribute("tabindex", "-1");
  target.scrollIntoView({ block: "start" });
  focus.focus({ preventScroll: true });
}
$("guide-link").href = "#language-guide";
$("guide-link").addEventListener("click", followInPageLink);
$("language-guide").addEventListener("click", followInPageLink);
let workerVersion = null;
async function serverVersion() {
  try {
    const r = await fetch("cubist-version", { cache: "no-store" });
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
  const url = new URL("./cubical-worker.mjs", import.meta.url);
  if (workerVersion) url.searchParams.set("version", workerVersion);
  worker = new Worker(url, { type: "module" });
  worker.onmessage = ({ data }) => {
    if (data.ready) {
      ready = true;
      refreshStatus();
      // Embedded, the page checks what the embedding page sends.
      if (embedded) {
        parent.postMessage({ type: "cubist-ready" }, location.origin);
        if (queuedExample) runExample(queuedExample);
      } else check();
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
enableTokenTips();
// The console runs over the last checked version of this file.
if (!embedded) createReplConsole($("repl"), {
  label: "Console input: a Cubist term or declaration",
  run: input => request("repl", { input }),
  reset: () => request("repl-reset", {}),
});
await startWorker();
