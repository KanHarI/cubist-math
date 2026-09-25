import { splitInspectionContext } from "./cubical-context.mjs";
import { renderSpecialization } from "./cubical-specialization.mjs";
import { cubicalSourceFile } from "./cubical-sources.mjs";
import { proofChoices as choices, proofTopics, proofsInTopic } from "./proof-library.mjs";
import { proofRequestWatchdog } from "./proof-watchdog.mjs";
import { renderMathNotation } from "./math-notation.mjs";
import { axiomLabels } from "./axiom-labels.mjs";
import { saveWorkbenchTransfer } from "./workbench-transfer.mjs";
import { readProofNavigation, saveProofNavigation, proofReturnURL } from "./proof-navigation.mjs";
import { cubicalMathTree } from "./cubical-notation.mjs";
import { boundedSyntaxJson, syntaxDisplayLimitMessage } from "./cubical-json.mjs";

const query = new URLSearchParams(location.search);
const backend = "cubical";
const proofId = choices.some((p) => p.id === query.get("proof"))
  ? query.get("proof")
  : "euclid";
const sourceURL = `archive/first-library/${choices.find((p) => p.id === proofId).file ?? cubicalSourceFile(proofId)}`;
const snapshot = readProofNavigation(query.get("restore"));
let restoring = snapshot?.proof === proofId ? snapshot : null;
const crossFileBack = restoring?.back ?? query.get("back");
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
async function check() {
  showChecking(true);
  if (await refreshCompiler()) return;
  $("diagnostic").hidden = true;
  const source = $("editor").value;
  try {
    const result = await request("check", { source, module: proofId, optimizations: compilerOptimizations() });
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
      if (info ?? fallback) await inspect(decorate(info ?? fallback), false);
      if (info) revealSource(info);
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
    button.textContent = last.assumptionLabels?.[binding] ?? axiomLabels[binding] ?? binding;
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
      output.template ? "Universe template " : output.verified === false && last.backend === "cubical" ? "Not checked " : output.kind === "axiom" ? "Axiom " : last.mode !== "construction" || output.verified
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
    if (last.backend === "cubical" && !output.verified) dependencies.textContent = output.reason;
    else renderAxioms(dependencies, output.axioms ?? []);
    line.append(dependencies);
    $("result").append(line);
  }
  const detail = document.createElement("small");
  detail.textContent = `${last.instructionCount.toLocaleString()} checked instructions. ${last.axiomCount ? last.axiomCount + " explicit axioms in this module." : "No axioms."}`;
  $("result").append(detail);
}
const keywords = new Set([
  "import",
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
  "rfl", "calc", "rw", "simp", "simpa", "simp_rule", "simp_set", "priority", "only", "without", "using", "by", "occurrence", "ext", "over", "along", "from",
  "private",
  "export",
  "verify",
  "with",
  "unfolding",
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
  "W", "sup", "wrec",
  "Interval", "path", "PathP", "at", "comp", "face", "flip", "meet", "join",
  "Pushout", "push_left", "push_right", "push_path", "pushout_induction",
  "Nat", "Unit", "Void", "Universe", "tt", "succ", "refl", "absurd",
  "sym", "trans", "cong", "transport", "apd", "apd_path", "Eq", "typed", "unfold",
  "induct", "unpack", "pair_induction", "unit_induction", "path_induction",
  "Choice", "LEM", "FunExt", "Truncate",
  "TruncateIntro", "TruncateProp", "TruncateElim", "Univalence", "UnivalenceBeta", "UnivalenceEta", "ua", "idtoequiv",
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
  const previousUniverses = selected?.universes;
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
  const templateBinding = info.template ? info.binding : info.templateBinding;
  const universeControls = $("inspect-universes");
  universeControls.replaceChildren(); universeControls.hidden = !templateBinding;
  if (templateBinding) {
    const parameters = info.templateParameters ?? ["U"];
    info.universes ??= parameters.map((_, index) => previousUniverses?.[index] ?? 0);
    for (const [index, parameter] of parameters.entries()) {
      const label = document.createElement("label"), select = document.createElement("select");
      label.textContent = `Universe ${parameter} `;
      select.setAttribute("aria-label", `Universe ${parameter}`);
      for (let level = 0; level <= 3; level++) select.add(new Option(`U${level}`, String(level)));
      select.value = String(info.universes[index]);
      select.onchange = () => {
        const universes = [...info.universes]; universes[index] = Number(select.value);
        inspect({ ...info, universes }, false);
      };
      label.append(select); universeControls.append(label);
    }
    $("inspect-description").textContent = `Inspecting ${info.name} at ${info.universes.map(level => `U${level}`).join(", ")}. This specialization is checked by cubical C; the generic definition remains a template.`;
  }
  sourceLink(info);
  $("inspect-axioms").replaceChildren();
  $("locals").replaceChildren();
  $("kernel-details").hidden = info.kind === "goal";
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
      type.textContent = local.type;
      button.append(type);
      button.onclick = () =>
        inspect({ ...local, kind: "value", role: "Local assumption" });
      $("locals").append(button);
    }
  } else {
    if (last.backend === "cubical" && info.verified === false && !templateBinding) {
      $("kernel-details").hidden = true;
      $("inspect-description").textContent = info.template
        ? `Library universe template. Each concrete specialization is checked by cubical C when used. ${info.description ?? ""}`
        : `Not checked by cubical C: ${info.reason}`;
      return;
    }
    try {
      const view = await request("inspect", { binding: templateBinding ?? info.binding,
        ...(templateBinding ? { universes: info.universes, offset: info.templateOffset,
          expansion: info.templateExpansion } : {}) });
      if (sequence !== inspectSerial) return;
      if (templateBinding) {
        const checkedInfo = view.symbols[view.name];
        if (checkedInfo) {
          sourceLink(checkedInfo);
          if (info.templateOffset !== undefined) {
            renderWitnessDetails(checkedInfo);
            $("inspect-description").prepend(document.createTextNode(
              `Inspecting at ${info.universes.map(level=>`U${level}`).join(", ")}. `));
          }
        }
      }
      if (view.statement) renderStatement(view);
      else renderType(view.typeText, Object.values(view.symbols));
      renderKernel(view);
    } catch (e) {
      if (sequence === inspectSerial) diagnostic(e);
    }
  }
  if (matchMedia("(max-width:1150px)").matches)
    $("inspect-name").scrollIntoView({ block: "center" });
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
    row.append(name, " : ", type);
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
  renderSpecialization($("kernel-specialization"), view);
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
    label.append(button, " : ");
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
  renderAxioms($("inspect-axioms"), view.axioms ?? []);
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
async function openKernelWorkbench(side, representation = "math") {
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
  const url = new URL("./cubical-worker.mjs", import.meta.url);
  if (workerVersion) url.searchParams.set("version", workerVersion);
  worker = new Worker(url, { type: "module" });
  worker.onmessage = ({ data }) => {
    if (data.ready) {
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
