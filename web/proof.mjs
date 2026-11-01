import { splitInspectionContext } from "./cubical-context.mjs";
import { cubicalSourceFile } from "./cubical-sources.mjs";
import { proofCatalog, proofTopics, proofsInTopic } from "./proof-library.mjs";
import { proofRequestWatchdog } from "./proof-watchdog.mjs";
import { WorkerRequests } from "./worker-requests.mjs";
import { workerMaintenance } from "./worker-maintenance.mjs";
import { renderMathNotation } from "./math-notation.mjs";
import { axiomLabels } from "./axiom-labels.mjs";
import { saveWorkbenchTransfer } from "./workbench-transfer.mjs";
import { readProofNavigation, saveProofNavigation, proofReturnURL } from "./proof-navigation.mjs";
import { cubicalMathTree } from "./cubical-notation.mjs";
import { boundedSyntaxJson, syntaxDisplayLimitMessage } from "./cubical-json.mjs";
import { numeralAt, tokenStyle, scan } from "./source-tokens.mjs";
import { archiveModules, cubistTestModules, libraryModules } from "./cubist/modules.mjs";
import { enableTokenTips } from "./token-tips.mjs";
import { createReplConsole, recordedSession } from "./repl-console.mjs";
import { createContextualConsole } from "./contextual-console.mjs";
import { withCode } from "./diagnostics.mjs";
import { showExplorer } from "./proof-explorer.mjs";

const query = new URLSearchParams(location.search);
const backend = "cubical";
// A reference example is not a library proof: its source comes from the URL
// fragment (#source=…), or, when embedded in a reference page, by message.
const exampleMode = query.has("example"), embedded = exampleMode && query.has("embed");
// A source opens by its module's name (?proof=name), or by its path from the
// repository root (?file=path), as the explorer and the Files page link it.
// A module of the rebuilt library opens from library/, a Cubist test from
// cubist-tests/ and any other module from the archive; a name in more than
// one root opens as the library's, as an import of it would. By path, a
// documentation example opens too: a source that is not a module, importing
// library-first.
const filePath = exampleMode ? null : query.get("file");
const fileName = filePath?.match(/^(?:[\w-]+\/)*([\w-]+)\.cubist$/)?.[1] ?? null;
const fileRoot = !fileName ? null
  : filePath === `library/${fileName}.cubist` ? "library"
  : filePath === `cubist-tests/${fileName}.cubist` ? "tests"
  : filePath === `archive/first-library/${fileName}.cubist` ? "archive"
  : filePath.startsWith("docs/") ? "docs" : null;
const documentationExample = fileRoot === "docs";
// Where a module's name opens, within the root its path names, if any.
const placeOf = (name, root) => (!root || root === "library") && libraryModules.includes(name) ? "library"
  : (!root || root === "tests") && cubistTestModules.includes(name) ? "tests"
  : (!root || root === "archive") && (archiveModules.includes(name) || proofCatalog.some((p) => p.id === name)) ? "archive"
  : null;
// A page that names no module opens the default one, the library's Euclid.
const named = fileRoot ? fileName : query.get("proof");
const found = exampleMode || documentationExample ? null : placeOf(named, fileRoot);
const requested = found ? named : "euclid";
const modulePlace = exampleMode || documentationExample ? null : found ?? "library";
const libraryModule = modulePlace === "library", testModule = modulePlace === "tests", archiveModule = modulePlace === "archive";
// A documentation example is checked under its file's name, as a name.
const proofId = exampleMode ? "reference_example"
  : documentationExample ? fileName.replace(/\W/g, "_").replace(/^(?=\d)/, "_")
  : requested;
const catalogEntry = proofCatalog.find((p) => p.id === proofId);
const sourceURL = exampleMode ? null
  : documentationExample ? filePath
  : libraryModule ? `library/${proofId}.cubist`
  : testModule ? `cubist-tests/${proofId}.cubist`
  : `archive/first-library/${cubicalSourceFile(proofId)}`;
// Edited drafts are kept per source: an archive module named as a library
// module, and a documentation example, keep theirs apart.
const draftKey = documentationExample ? `file:${filePath}`
  : archiveModule && libraryModules.includes(proofId) ? `archive:${proofId}` : proofId;
// Where its imports resolve from (module-resolution.mjs).
const place = exampleMode || documentationExample ? null : libraryModule ? "library" : testModule ? "tests" : "archive";
// The explorer lists every source; the one open here is current.
if (!embedded) showExplorer(sourceURL).catch(error => console.error(error));
const snapshot = readProofNavigation(query.get("restore"));
let restoring = snapshot?.proof === proofId && (snapshot.file ?? null) === (documentationExample ? filePath : null) ? snapshot : null;
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
  const stored = exampleMode ? null : sessionStorage.getItem("mathscript:" + draftKey);
  if (stored) {
    let record;
    try {
      record = JSON.parse(stored);
    } catch {
      record = { source: stored };
    }
    if (record && typeof record.source === "string") {
      const repositoryChanged =
        typeof record.baseline === "string" && record.baseline !== original;
      if (
        query.get("source") === "repo" ||
        (repositoryChanged && record.source === record.baseline)
      ) {
        previousDraft = record.source;
        sessionStorage.setItem("mathscript:previous:" + draftKey, previousDraft);
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
  previousDraft ??= sessionStorage.getItem("mathscript:previous:" + draftKey);
} catch {}
const example = restoring?.source ?? savedDraft ?? original;
const $ = (id) => document.getElementById(id);
let worker,
  ready = false,
  last = null,
  selected = null,
  inspectSerial = 0;
const history = [];
let sourceMode = restoring?.sourceMode ?? "read", generationSerial = 0;
const generatedSources = new Map();
let contextual=null;
$("editor").value = example;
// The source is readable at once, before the kernel loads and checks it;
// the check replaces this view with one whose names are inspectable.
const previewHint = "The source as loaded. When the check finishes, each name links to its checked type, context, and definition.";
renderPreview(example);
for (const id of ["share-syntax", "reuse-checks", "compact-paths"]) {
  $(id).checked = true;
  try { $(id).checked = localStorage.getItem("mathscript:" + id) !== "false"; } catch {}
}
$("proof-title").textContent = catalogEntry?.title
  ?? (libraryModule ? `Library: ${proofId}` : testModule ? `Cubist test: ${proofId}`
    : documentationExample ? `Documentation example: ${filePath}` : archiveModule ? `Archive: ${proofId}` : "Reference example");
$("development-note").hidden = !catalogEntry?.realDevelopment;
$("puncture-note").hidden = !catalogEntry?.punctureDevelopment;
$("complex-note").hidden = !catalogEntry?.complexDevelopment;
$("archive-note").hidden = exampleMode || libraryModule || testModule || documentationExample;
$("test-note").hidden = !testModule;
$("source-file").hidden = exampleMode;
$("repository-source").hidden = exampleMode;
if (sourceURL) {
  $("source-file").href = sourceURL;
  // Its path from the repository root, where the site serves it from.
  $("source-file").textContent = sourceURL;
}
if (!embedded) document.title = `${$("proof-title").textContent} · Cubist`;
$("repository-source").href = documentationExample
  ? `proof.html?file=${encodeURIComponent(filePath)}&source=repo`
  : `proof.html?proof=${encodeURIComponent(proofId)}&source=repo`;
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
      "mathscript:" + draftKey,
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
  $("check").disabled = !ready && !halted || worker?.pendingCount > 0;
  $("collect-contexts").disabled = !ready || worker?.pendingCount > 0;
  $("open-context-repl").disabled = !ready || worker?.pendingCount > 0 || dirty() || !checkedKernelView?.contextEntry;
  for (const id of ["share-syntax", "reuse-checks", "compact-paths"])
    $(id).disabled = !ready || worker?.pendingCount > 0 || !Object.keys(compilerOptimizations()).length;
  $("export").disabled = !last || worker?.pendingCount > 0;
  $("generated-mode").disabled = !last;
  $("generated-module").disabled = worker?.pendingCount > 0;
  $("dirty").textContent = dirty()
    ? "Edited — changes are not checked. Read and Generated Cubist show the last checked version."
    : "";
  $("status").textContent = worker?.pendingCount
    ? "Checking…"
    : last
      ? `Cubical C · ${last.complete ? `checked · ${last.axiomCount ? `${last.axiomCount} explicit assumptions` : "no axioms"}` : "check incomplete"}`
      : ready
        ? "Ready to check"
        : "Loading kernel…";
}
// The page's maintenance of its worker (worker-maintenance.mjs): the
// rebuild after a kernel failure (restartAfterFault) and every restore of the
// console's session (recordedSession). A request waits until no
// maintenance is under way or asked for, unless it is maintenance's own
// (`internal`), and is sent only then, its deadline starting as it is sent:
// so none runs behind a rebuild's check or a restore. When maintenance
// ends, an example the embedding page sent meanwhile is checked. When the
// page stops replacing workers (halted), a request fails at once.
// `replaced` bounds the replacements (restartAfterFault). `checkedBy` is the
// worker that holds a checked proof, on which the console can restore.
let halted = null, replaced = false, checkedBy = null;
const upkeep = workerMaintenance({ onIdle: () => {
  refreshStatus();
  if (ready && queuedExample) runExample(queuedExample);
} });
function request(command, args = {}, { internal = false } = {}) {
  const send = () => sendToWorker(command, args);
  return internal ? upkeep.internal(send) : upkeep.request(send);
}
const internal = (command, args) => request(command, args, { internal: true });
function sendToWorker(command, args) {
  if (!ready) return Promise.reject(halted ?? new Error("The checking worker is unavailable. Reload the page to restart it."));
  const currentWorker = worker;
  const watchdog = proofRequestWatchdog(command, () => {
    currentWorker.terminate(new Error("The checking worker stopped making progress. Reload the page to restart the kernel."));
    if (worker !== currentWorker) return;
    ready = false;
    contextual?.invalidate("The checking worker stopped. Reload and check the source to open a new context.");
    refreshStatus();
  });
  const result = currentWorker.request(command, args, progress => {
    watchdog.progress(progress);
    checkingProgress(progress);
  });
  if (command === "check") result.then(() => { checkedBy = currentWorker; }, () => {});
  refreshStatus();
  return result.finally(() => { watchdog.stop(); refreshStatus(); });
}

let focusOffset = query.has("offset") && Number.isSafeInteger(Number(query.get("offset"))) ? Number(query.get("offset")) : null, queuedExample = null;
// Check an example sent by the embedding reference page, then inspect the
// name the reader clicked. One that arrives while a worker starts, or while
// the page rebuilds after a kernel failure, waits, the latest only, for the
// worker's first check or the rebuild (rebuild) to take it.
function showExample({ source, offset }) {
  queuedExample = null;
  $("editor").value = source;
  focusOffset = Number.isInteger(offset) ? offset : null;
}
async function runExample(example) {
  if (!ready && !halted || upkeep.busy) { queuedExample = example; return; }
  showExample(example);
  await check();
}
if (embedded) addEventListener("message", ({ data, origin }) => {
  if (origin !== location.origin || data?.type !== "cubist-inspect" || typeof data.source !== "string") return;
  // The reader asked for it on the embedding page (restartAfterFault).
  replaced = false;
  runExample({ source: data.source, offset: data.offset });
});
// What a check of the editor's source sends. Where the source came from
// decides where its imports are found (module-resolution.mjs): an archive
// proof imports only from the archive.
function checkArgs() {
  return { source: $("editor").value, module: proofId, place, optimizations: compilerOptimizations(), collectScopes: $("collect-contexts").checked };
}
// Check the editor's source and read its result. A rebuild after a kernel
// failure sends its check itself (`sent`: its arguments and the reply),
// and this reads it. After the page stopped replacing workers, a check
// starts a new one: the reader's retry (restartAfterFault).
async function check({keepInspection=false,sent=null}={}) {
  showChecking(true);
  if (halted && !sent && !await retry()) return;
  if (!sent && await refreshCompiler()) return;
  const contextVersion=contextual?.invalidate("Checking the source. Select a new context when checking finishes.");
  $("diagnostic").hidden = true;
  const args = sent?.args ?? checkArgs(), { source, collectScopes } = args;
  // Nothing checked yet: show the source being checked rather than nothing.
  // After a check, Read keeps the last checked version until this one ends.
  if (!last) renderPreview(source);
  try {
    const result = await (sent?.reply ?? request("check", args));
    last = result;
    contextual?.checked(result,contextVersion,collectScopes);
    generationSerial++;
    generatedSources.clear();
    $("generated-source").replaceChildren();
    const previousModule = restoring?.generatedModule ?? $("generated-module").value;
    $("generated-module").replaceChildren(...Object.keys(result.sources).map(name => {
      const option = document.createElement("option");
      option.value = name; option.textContent = name === proofId ? `${name} (current)` : name;
      return option;
    }));
    $("generated-module").value = Object.hasOwn(result.sources, previousModule) ? previousModule : proofId;
    if(!keepInspection)history.length = 0;
    renderSource();
    renderResult();
    // Editing that went on during the check stays open; otherwise the checked
    // source is shown.
    await setMode(sourceMode === "generated" ? "generated" : sourceMode === "edit" && dirty() ? "edit" : "read");
    if(!keepInspection) {
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
        $("generated-source").scrollTop = saved.generatedScroll ?? 0;
        window.scrollTo(0, saved.scroll ?? 0);
      } else {
        const fallback = result.outputs.at(-1);
        // An embedding page asks for the name at a source offset.
        const focus = focusOffset === null ? null : [...result.links].filter(link => link.start === focusOffset)
          .sort((a, b) => a.end - a.start - (b.end - b.start))[0];
        const requestedOffset = focusOffset;
        focusOffset = null;
        if (focus) await inspect({ ...decorate(focus), line: result.source.slice(0, focus.start).split("\n").length }, false);
        else if (info ?? fallback) await inspect(decorate(info ?? fallback), false);
        // Revealing the declaration switches to Read: not over an edit that
        // stayed open. Embedded, the inspector is on top and the source below
        // stays in place.
        if (sourceMode !== "edit") {
          if (!embedded && requestedOffset !== null && requestedOffset >= 0 && requestedOffset <= result.source.length)
            revealSource({ module: proofId, start: requestedOffset });
          else if (info) revealSource(definitionSite(info));
        }
      }
    }
    rememberDraft();
    return result;
  } catch (e) {
    contextual?.invalidate("The source could not be checked. Fix it and check again to select a new context.");
    diagnostic(e);
    setMode("edit");
    if (Number.isInteger(e.offset)) {
      $("editor").focus();
      $("editor").setSelectionRange(e.offset, e.offset + 1);
    }
  } finally {
    showChecking(false);
    refreshStatus();
  }
}
function setMode(mode) {
  sourceMode = mode;
  $("editor").hidden = mode !== "edit";
  $("read-source").hidden = mode !== "read";
  $("source-count").hidden = mode === "generated";
  $("generated-panel").hidden = mode !== "generated";
  $("read-mode").setAttribute("aria-pressed", String(mode === "read"));
  $("edit-mode").setAttribute("aria-pressed", String(mode === "edit"));
  $("generated-mode").setAttribute("aria-pressed", String(mode === "generated"));
  $("source-hint").textContent =
    mode === "edit"
      ? "Edit the source, then Check proof. A failed check preserves your last checked proof."
      : mode === "generated" ? "Frontend expansion from the last check. Click a declaration or linked name to inspect it. Each family shows its checking status."
      : last ? "Click a name or numeral to inspect its checked type, context, and definition. Click a line number to see its goal."
      : $("diagnostic").hidden ? previewHint
      : "The source as loaded. It did not check: see the diagnostic above, then edit it and check again.";
  if (mode === "generated") return showGeneration();
}
// The source before its check: highlighted, with nothing to inspect yet. An
// embedded frame starts without a source, and shows nothing until one arrives.
function renderPreview(source) {
  renderSource($("read-source"), source ? { source, links: [], mode: "mathematical", preview: true } : null);
  if (!source) $("source-count").textContent = "";
  if (sourceMode === "read") $("source-hint").textContent = previewHint;
}
async function showGeneration() {
  if (!last) return;
  const sequence = ++generationSerial, module = $("generated-module").value;
  $("generated-status").textContent = "Preparing generated source…";
  $("generated-source").replaceChildren();
  try {
    const result = generatedSources.get(module) ?? await request("generation", { module });
    if (sequence !== generationSerial) return;
    generatedSources.set(module, result);
    renderSource($("generated-source"), result);
    $("generated-status").textContent = `${result.count} generated declarations`
      + (last.gaps.some(gap => gap.module === module) ? " · check incomplete" : "");
  } catch (error) {
    if (sequence === generationSerial) $("generated-status").textContent = `Unable to display generation: ${error.message}`;
  }
}
function decorate(info) {
  const imported = last?.imports.find(
    (d) => d.binding === info.binding,
  );
  const declaration = last?.declarations?.find(
    (d) => d.binding === info.binding,
  );
  const local = last?.links.find(
    (d) =>
      d.binding === info.binding &&
      ["local", "parameter", "def"].includes(d.role),
  );
  const output = last?.outputs.find(d => d.binding === info.binding);
  const value = { ...declaration, ...output, ...imported, ...info, kind: "value" };
  if (value.definitionStart === undefined && local)
    value.definitionStart = local.start;
  if (/^[0-9]+$/.test(info.name ?? "")) {
    const n = Number(info.name);
    value.role = "natural-number literal";
    value.description = `${n} : UNat is notation for ${"succ(".repeat(n)}0${")".repeat(n)}. Numerals are built from zero and successor; they are not axioms.`;
  }
  return value;
}
function definitionSite(info) {
  return info.definitionSite ?? { module: info.sourceModule ?? proofId,
    start: info.definitionStart, name: info.sourceName };
}
function revealSource({ module, start }) {
  if (module !== proofId || !Number.isInteger(start)) return;
  const line = last.source.slice(0, start).split("\n").length;
  setMode("read");
  for (const row of document.querySelectorAll(".source-line.active"))
    row.classList.remove("active");
  const row = document.querySelector(`.source-line[data-line="${line}"]`);
  if (!row) return;
  row.classList.add("active");
  // Center the line in the source box, and bring the box into view only as
  // far as needed: the page does not jump away from what is being read.
  const box = $("read-source");
  box.scrollTop += row.getBoundingClientRect().top - box.getBoundingClientRect().top - (box.clientHeight - row.offsetHeight) / 2;
  row.scrollIntoView({ block: "nearest" });
}
function sourceLink(info) {
  const link = $("view-source");
  link.hidden = true;
  link.onclick = null;
  link.textContent = info.kind === "module" ? "View module source →" : "View source →";
  if (info.definitionSite || info.sourceModule || Number.isInteger(info.definitionStart)) {
    link.hidden = false;
    sourceTarget(link, definitionSite(info));
  }
}
// Source navigation uses the qualified site, independent of its display label.
function sourceTarget(link, site) {
  if (site.module !== proofId) {
    link.href = `proof.html?proof=${encodeURIComponent(site.module)}${site.name ? "&name=" + encodeURIComponent(site.name) : ""}`
      + (Number.isInteger(site.start) ? `&offset=${site.start}` : "");
    link.onclick = () => {
      const address = new URL(link.href);
      address.searchParams.set("back", rememberInspection());
      link.href = address.href;
    };
  } else {
    link.href = "#read-source";
    link.onclick = (e) => {
      e.preventDefault();
      revealSource(site);
    };
  }
}
function diagnosticLocations(target, diagnostic) {
  if (!diagnostic) return;
  const sites = [diagnostic.primary, ...diagnostic.related];
  for (const [index, site] of sites.entries()) {
    const source = last.sources[site.module];
    if (source === undefined || !Number.isInteger(site.start)) continue;
    const before = source.slice(0, site.start), line = before.split("\n").length;
    const at = document.createElement("a");
    at.className = "diagnostic-site";
    at.textContent = `${index ? "Related" : "Source"}: ${site.module}:${line}:${site.start - before.lastIndexOf("\n")}`;
    sourceTarget(at, site);
    target.append(" ", at);
  }
}

// An assumption as the check published it (CubicalProgram.assumptionSymbols):
// its label, and the site of the axiom definition it was recorded from.
function axiomInfo(binding) {
  return decorate({ binding, name: last.assumptionLabels?.[binding] ?? binding, role: "explicit axiom",
    ...(last.symbols ?? []).find(o => o.binding === binding),
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
    button.title = `Inspect ${button.textContent} and its declared type`;
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
    if (last.backend === "cubical" && !output.verified) {
      dependencies.append(...codeLink(output.code), output.reason);
      diagnosticLocations(dependencies, output.diagnostic);
    }
    else renderAxioms(dependencies, output.axioms ?? [], output.extensions ?? []);
    line.append(dependencies);
    $("result").append(line);
  }
  // A duplicate or directive has no new symbol to inspect: an earlier
  // declaration still owns its name. Show its separate diagnostic.
  for (const gap of last.gaps ?? []) if (gap.duplicate || gap.directive) {
    const line = document.createElement("div");
    line.className = "declaration-error";
    line.append("Not checked ", ...codeLink(gap.code), ": ", gap.reason);
    diagnosticLocations(line, gap.diagnostic);
    if (gap.module === proofId && Number.isInteger(gap.start)) {
      const at = document.createElement("button");
      at.textContent = "View source";
      at.onclick = () => revealSource(gap);
      line.append(" ", at);
    }
    $("result").append(line);
  }
  // Lint warnings: bindings that are never used and can be removed.
  for (const warning of last.warnings ?? []) {
    const line = document.createElement("div"), at = document.createElement("button");
    line.className = "lint-warning";
    at.textContent = `line ${warning.line}`;
    at.onclick = () => revealSource({ ...warning, module: proofId });
    line.append("Warning ", ...codeLink(warning.code), "at ", at, `: ${warning.message}`);
    $("result").append(line);
  }
  const detail = document.createElement("small");
  detail.textContent = `${last.instructionCount.toLocaleString()} checked instructions. ${last.axiomCount ? last.axiomCount + " explicit axioms in this module." : "No axioms."}`;
  $("result").append(detail);
}
function renderSource(target = $("read-source"), snapshot = last) {
  target.replaceChildren();
  if (!snapshot) return;
  const generated = target.id === "generated-source";
  const linkMap = new Map();
  for (const link of snapshot.links) {
    const old = linkMap.get(link.start);
    if (!old || link.end - link.start < old.end - old.start)
      linkMap.set(link.start, link);
  }
  const importStarts = new Map(
    [...snapshot.source.matchAll(/\bimport\s+([A-Za-z_][A-Za-z_0-9]*)\s*;/g)].map(
      (match) => [match.index + match[0].indexOf(match[1]), match[1]],
    ),
  );
  // A preview's line numbers lead nowhere yet: plain, as in generated source.
  const inspectable = !generated && !snapshot.preview;
  if (!generated) $("source-count").textContent = `${snapshot.source.split("\n").length} lines${inspectable ? " · click a name or numeral" : ""}`;
  let offset = 0;
  for (const [index, line] of snapshot.source.split("\n").entries()) {
    const row = document.createElement("div");
    row.className = "source-line";
    row.dataset.line = index + 1;
    const number = document.createElement(inspectable ? "button" : "span");
    number.className = "line-number";
    number.textContent = index + 1;
    if (inspectable) number.setAttribute("aria-label", `Inspect goal at line ${index + 1}`);
    else number.setAttribute("aria-hidden", "true");
    const lineOffset = offset;
    if (inspectable) number.onclick = () => {
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
    for (const token of scan(line)) {
      if (token.start < cursor) continue;
      if (token.start > cursor)
        code.append(document.createTextNode(line.slice(cursor, token.start)));
      const start = offset + token.start, info = linkMap.get(start);
      // A generated qualified name is one reference, including every dot.
      const text = generated && info?.generated ? snapshot.source.slice(start, info.end) : token.text;
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
          // Before a check there is no inspection to come back to.
          if (!last) return;
          const address = new URL(link.href);
          address.searchParams.set("back", rememberInspection());
          link.href = address.href;
        };
        code.append(link);
      } else {
        const expansion = ((snapshot.mode ?? last?.mode) === "mathematical" ? numeralAt(line, token.start, text) : null) ?? info?.expansion;
        // The whole source: a header's colon and its inductive may be on earlier lines.
        const style = tokenStyle(text, expansion);
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
            inspect({ ...decorate(info), line: index + 1, sourceView: target.id,
              ...(generated ? { generatedModule: snapshot.module } : {}) });
          code.append(button);
        } else if (style) {
          const span = document.createElement("span");
          span.className = style;
          span.textContent = text;
          if (expansion && expansion !== text) span.dataset.tip = `${text} expands to ${expansion}`;
          code.append(span);
        } else code.append(document.createTextNode(text));
      }
      cursor = token.start + text.length;
    }
    row.append(number, code);
    target.append(row);
    offset += line.length + 1;
  }
  if (!snapshot.preview) contextual?.decorate(target,snapshot,{module:generated?snapshot.module:proofId,generated});
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
  document.querySelector(".inspector").classList.remove("empty");
  if (info.sourceView === "generated-source" &&
      (sourceMode !== "generated" || $("generated-module").value !== info.generatedModule)) {
    $("generated-module").value = info.generatedModule;
    await setMode("generated");
    if (sequence !== inspectSerial) return;
  } else if (info.sourceView === "read-source") setMode("read");
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
  $("inspect-boundary").hidden = true;
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
  $("open-context-repl").hidden = true;
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
    $(info.sourceView ?? "read-source")
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
      diagnosticLocations($("inspect-description"), info.diagnostic);
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
    row.append(...parameter.implicit ? ["{{", name] : [name], ` ${parameter.relation} `, type, ...parameter.implicit ? ["}}"] : []);
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
  for (const token of scan(text)) {
    const word = token.text,
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
  $("open-context-repl").hidden = !view.contextEntry;
  renderCubicalKernel(view);
  refreshStatus();
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
    identitySugar: $("kernel-identity-sugar").checked, groupIndependentBinders: false };
  if (view.dimensions?.length) {
    const row = document.createElement("li");
    row.textContent = `Interval coordinates: ${view.dimensions.map(([name]) => name).join(", ")}`;
    $("kernel-context-list").append(row);
  }
  const render = (target, term) => {
    target.classList.toggle("typeset", !raw);
    if (raw) target.textContent = boundedSyntaxJson(term) ?? syntaxDisplayLimitMessage;
    else renderMathNotation(target, cubicalMathTree(term, view.symbols, kernelDisplayLimit,
      { dimensions: (view.dimensions ?? []).map(([name]) => name) }), navigation);
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
  $("kernel-binder-options").hidden = true;
  $("kernel-identity-options").hidden = raw;
  $("expand-kernel").textContent = "Show more of the term";
  $("expand-kernel").hidden = raw || !["kernel-expression", "kernel-type", "kernel-context-list", "kernel-axioms-list"].some(id => $(id).textContent.includes("…"));
  renderAxioms($("inspect-axioms"), view.axioms ?? [], view.extensions ?? []);
  renderBoundary(view.boundary);
}
// A square's boundary (L2.8): its four edges and four corners.
function renderBoundary(boundary) {
  $("inspect-boundary").hidden = !boundary;
  if (!boundary) return;
  for (const [name, text] of [...Object.entries(boundary.corners), ...Object.entries(boundary.edges)])
    $(`square-${name}`).textContent = text;
}
$("open-context-repl").onclick = async () => {
  if(!checkedKernelView?.contextEntry||dirty()||worker?.pendingCount)return;
  const info=selected,sequence=inspectSerial,source=last.source;
  try {
    if(!contextual.collecting) {
      $("collect-contexts").checked=true;
      const result=await check({keepInspection:true});
      if(!result||last!==result||result.source!==source||dirty()||inspectSerial!==sequence)return;
      await inspect(info,false);
      if(inspectSerial!==sequence+1||selected.binding!==info.binding||dirty())return;
    }
    const view=checkedKernelView,snapshot=last,current=inspectSerial;
    await contextual.openInspection(view.contextEntry,
      ()=>inspectSerial===current&&checkedKernelView===view&&last===snapshot&&!dirty());
  } catch(error) {diagnostic(error);}
};
$("toggle-kernel-body").onclick = () => { showKernelBody = !showKernelBody; renderKernel(checkedKernelView); };
$("widen-inspector").onclick = () => {
  const wide = document.querySelector(".workspace").classList.toggle("inspector-wide");
  $("widen-inspector").textContent = wide ? "Narrow" : "Widen";
  $("widen-inspector").setAttribute("aria-pressed", String(wide));
};

$("kernel-view").onchange = () => { if (checkedKernelView) renderKernel(checkedKernelView); };
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
$("generated-mode").onclick = () => setMode("generated");
$("generated-module").onchange = showGeneration;
$("collect-contexts").onchange=check;
$("editor").oninput = () => {
  contextual?.invalidate();
  if(ready)request("context-invalidate").catch(()=>{});
  refreshStatus();
  rememberDraft();
};
$("editor").onkeydown = (e) => {
  if ((e.ctrlKey || e.metaKey) && e.key === "Enter") {
    e.preventDefault();
    if ((ready || halted) && !worker?.pendingCount) check();
  }
};
function rememberInspection() {
  return saveProofNavigation({ proof: proofId, example: exampleMode, file: documentationExample ? filePath : undefined, backend, source: last.source,
    selected, history, back: crossFileBack, scroll: window.scrollY,
    sourceScroll: $("read-source").scrollTop, sourceMode,
    generatedModule: $("generated-module").value, generatedScroll: $("generated-source").scrollTop });
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
    if (ready || halted) await check();
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
// A newer compiler on the server replaces the worker, as maintenance
// (replaceWorker), which decides again once it is its turn: a restore or a
// rebuild under way when the version came is not cut off, and a worker that
// replaced this one meanwhile, or a page that stopped, is left as it is. The
// new worker checks the current source again and restores the console's
// session (rebuild); an embedded page that has checked no example yet
// waits for one.
async function refreshCompiler() {
  if (worker?.pendingCount || !ready || upkeep.busy) return false;
  const current = worker, version = await serverVersion();
  if (!version || version === workerVersion) return false;
  let recheck = true;
  return replaceWorker({ version, onReady: () => rebuild(recheck), prepare: () => {
    if (worker !== current || !ready || version === workerVersion) return false;
    recheck = !embedded || last !== null;
    ready = false;
    showChecking(true, "Updating proof checker…");
    contextual?.invalidate("The compiler changed. Check the source and select a new context.");
    last = null;
    $("result").hidden = true;
    $("source-notice").hidden = false;
    $("source-notice").textContent =
      "The compiler was updated. Rechecking your current source; edits are preserved.";
    return true;
  } });
}
// The workers started, counted: the console restores its session on a new
// one (recordedSession in repl-console.mjs).
let workers = 0;
// Every start of the page's worker, and every replacement, is maintenance
// (upkeep): it begins once maintenance under way and the requests already
// sent are done, and then, unless `prepare` declines, ends the worker there
// was, if any, and lasts until the new one is ready and has done what
// `onReady` does (startWorker). So no request is sent to a worker on its way
// out or before its successor is ready, and nothing replaces a worker while
// a restore or a rebuild runs on it.
function replaceWorker({ version = undefined, onReady = null, prepare = () => true } = {}) {
  return upkeep.run(async () => {
    if (!prepare()) return false;
    worker?.terminate();
    const { started } = await startWorker(version, { onReady });
    await started;
    return true;
  });
}
// A worker and, once it is ready, the page's first check, or what `onReady`
// does instead, as rebuild after a kernel failure. `started` settles when
// that is done.
async function startWorker(version = undefined, { onReady = null } = {}) {
  workerVersion = version ?? (await serverVersion());
  const url = new URL("./cubical-worker.mjs", import.meta.url);
  if (workerVersion) url.searchParams.set("version", workerVersion);
  workers++;
  worker = new WorkerRequests(new Worker(url, { type: "module" }), { onError: error => {
    ready = false;
    if (error.fatal) { restartAfterFault(error); return; }
    contextual?.invalidate("The checking worker stopped. Reload and check the source to open a new context.");
    diagnostic(error);
    refreshStatus();
  } });
  const started = worker.ready.then(async () => {
    ready = true;
    refreshStatus();
    if (onReady) await onReady();
    // Embedded, the page checks what the embedding page sends.
    else if (embedded) {
      parent.postMessage({ type: "cubist-ready" }, location.origin);
      if (queuedExample) runExample(queuedExample);
    } else check();
  }, () => {}); // The transport's onError reports startup failure.
  return { started };
}
// A kernel failure stops the worker (a fatal reply, WorkerRequests), which
// failed every request it held. A new worker starts, as after a compiler
// update, and the page builds on it again what it held (rebuild). A check
// that failed so is not checked again; the new worker waits for the next.
// The page replaces a worker so once until the reader does something, a key
// or a pointer pressed, or an example sent from the embedding page: should
// the new worker fail too before that, in its rebuild or in what the page
// reads from it after, the page stops (halted) and says so, and the reader's
// next check starts a worker (retry).
for (const type of ["keydown", "pointerdown"]) addEventListener(type, () => { replaced = false; }, true);
function restartAfterFault(error) {
  contextual?.invalidate("The kernel failed. Select a context again once the source is checked.");
  diagnostic(error);
  $("source-notice").hidden = false;
  if (replaced) {
    halted = new Error("The kernel failed again in the checking worker that replaced a failed one, so no other starts on its own: check the source to start one.");
    $("source-notice").textContent = halted.message;
    refreshStatus();
    return;
  }
  replaced = true;
  const recheck = error.command !== "check";
  $("source-notice").textContent = recheck
    ? "The kernel's WebAssembly instance failed, so a new checking worker checks your current source again; edits are preserved."
    : "The kernel's WebAssembly instance failed while checking, so a new checking worker waits for the next check.";
  // The new worker and its rebuild are maintenance, asked for at once: what
  // is asked from here on waits for them. A worker that replaced the failed
  // one meanwhile is left as it is.
  const failed = worker;
  replaceWorker({ version: workerVersion, onReady: () => rebuild(recheck), prepare: () => worker === failed })
    .catch(diagnostic);
}
// What the page held, built again on a new worker: the source checked again,
// or the latest example the embedding page sent while the worker started,
// and the console's session restored on it. The check's result is read as
// any check's (check), and what reading it asks of the worker, as the
// inspector's view and the contexts, waits for the rebuild like any other
// request, so the rebuild's own requests are the check and the restore.
async function rebuild(recheck) {
  if (queuedExample) showExample(queuedExample);
  else if (!recheck) return;
  const args = checkArgs(), reply = internal("check", args);
  check({ sent: { args, reply } });
  try { await reply; } catch { return; }
  for (const note of await consoleSession.restore(internal)) replConsole?.show(note);
}
// The reader's check after the page stopped replacing workers: a new worker,
// for that check, unless one is ready by its turn. False when none is.
async function retry() {
  halted = null;
  $("source-notice").hidden = true;
  refreshStatus();
  await replaceWorker({ onReady: () => {}, prepare: () => !ready });
  return ready;
}
addEventListener("focus", () => {
  refreshCompiler().catch(diagnostic);
});
addEventListener("pageshow", (event) => {
  if (event.persisted) refreshCompiler().catch(diagnostic);
});
enableTokenTips();
$("context-option").hidden=embedded;
contextual=createContextualConsole($("context-panel"),{request});
// The console runs over the last checked version of this file. Its session
// is restored on a worker that replaced one: by the rebuild, or, when the
// rebuild checked nothing, before its next entry once the new worker has
// checked the source (recordedSession). Each restore is maintenance, run
// once the requests already sent, a check among them, have settled.
const consoleSession = recordedSession(request, { generation: () => workers, restoreAfterFault: false,
  restorable: () => ready && checkedBy === worker, maintain: work => upkeep.run(() => work(internal)) });
const replConsole = embedded ? null : createReplConsole($("repl"), {
  label: "Console input: a Cubist term or declaration",
  run: consoleSession.run,
  reset: () => { consoleSession.reset(); return request("repl-reset", {}); },
});
await replaceWorker();
