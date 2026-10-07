import { areaLabels, savedReport } from "./benchmark-areas.mjs";

const $ = id => document.getElementById(id);
// The area measured, from the page's address: ?area=library, archive or tests.
const requested = new URLSearchParams(location.search).get("area");
if (Object.hasOwn(areaLabels, requested)) $("area").value = requested;
const area = () => $("area").value;
const labels = { checked: "1 · Checked within deadline", optimize: "2 · Needs optimization",
  blocked: "3 · Blocked", failed: "4 · Needs fixing", intended: "5 · Intended failures" };
let report, lastText, worker, localRun = false;
function link(row) {
  const a = document.createElement("a");
  a.href = `proof.html?proof=${encodeURIComponent(row.module)}&name=${encodeURIComponent(row.name)}`;
  a.textContent = `${row.module}.${row.name}`; return a;
}
function renderRows() {
  if (!report) return;
  const query = $("search").value.toLowerCase(), category = $("category").value;
  const rows = report.declarations.filter(row => (!category || row.category === category)
    && `${row.module}.${row.name} ${row.reason ?? ""} ${row.rootBlocker ?? ""}`.toLowerCase().includes(query));
  // Put actionable failures and timeouts first, then the slowest entries in
  // each category; intended failures, which need nothing, last.
  const rank = { optimize: 0, failed: 1, blocked: 2, checked: 3, intended: 4 };
  rows.sort((a, b) => rank[a.category] - rank[b.category] || b.elapsedMs - a.elapsedMs);
  const fragment = document.createDocumentFragment();
  const bindings = new Map(report.declarations.map(row => [row.binding, row]));
  for (const row of rows) {
    const tr = document.createElement("tr"); tr.dataset.category = row.category;
    const cells = Array.from({ length: 7 }, () => document.createElement("td"));
    const ms = value => `${value.toLocaleString(undefined, { maximumFractionDigits: 1 })} ms`;
    cells[0].append(link(row)); cells[1].textContent = labels[row.category];
    cells[2].textContent = ms(row.elapsedMs);
    // The time split between the elaborator and the instruction kernel's
    // derivations; a report from before the split records the admission's.
    const kernelMs = row.kernelMs ?? row.instructionMs, judgements = row.kernelJudgements ?? row.instructionJudgements;
    cells[3].textContent = kernelMs == null ? "—" : ms(Math.max(0, row.elapsedMs - kernelMs));
    cells[4].textContent = kernelMs == null ? "—" : ms(kernelMs);
    cells[5].textContent = judgements?.toLocaleString() ?? "—";
    cells[6].textContent = row.category === "intended" ? `As its comment states: ${row.reason}` : row.reason ?? (row.instructionJudgements != null
      ? "Checked, and derived by the instruction kernel." : "Native kernel check passed.");
    const root = bindings.get(row.rootBlocker);
    if (root) { const small = document.createElement("small"); small.append("Root blocker: ", link(root)); cells[6].append(small); }
    tr.append(...cells); fragment.append(tr);
  }
  $("entries").replaceChildren(fragment);
  $("shown").textContent = `${rows.length.toLocaleString()} of ${report.declarations.length.toLocaleString()} declarations shown`;
}
function renderReport() {
    labels.checked = `1 · Checked within ${report.limitMs ?? 1000} ms`;
    $("category").querySelector('[value="checked"]').textContent = labels.checked;
    const counts = report.counts ?? Object.fromEntries(Object.keys(labels).map(c => [c, report.declarations.filter(d => d.category === c).length]));
    const total = report.total ?? report.declarations.length;
    $("status").textContent = `${areaLabels[report.area ?? "archive"]} · ${report.complete ? "Completed" : "Running"} · ${new Date(report.generatedAt).toLocaleString()} · ${report.modules ?? "…"} modules · ${total} declarations${report.elapsedSeconds ? ` · ${report.elapsedSeconds}s elapsed` : ""}${report.revision ? ` · ${report.revision.slice(0, 8)}${report.dirty ? " + working changes" : ""}` : ""}`;
    $("progress").max = Math.max(1, total); $("progress").value = counts.checked ?? 0;
    $("counts").replaceChildren(...Object.entries(labels).map(([key, label]) => {
      const button = document.createElement("button"), number = document.createElement("strong");
      number.textContent = (counts[key] ?? 0).toLocaleString(); button.append(number, label);
      button.onclick = () => { $("category").value = key; renderRows(); }; return button;
    }));
    $("comparison").textContent = report.baseline && (report.baseline.area ?? "archive") === (report.area ?? "archive") && report.baseline.limitMs === report.limitMs && JSON.stringify(report.baseline.optimizations) === JSON.stringify(report.optimizations) ? `Checked since baseline: ${counts.checked - report.baseline.counts.checked >= 0 ? "+" : ""}${counts.checked - report.baseline.counts.checked}. Baseline recorded ${new Date(report.baseline.generatedAt).toLocaleString()}.` : `Deadline: ${report.limitMs ?? 1000} ms. Comparisons require the same area, deadline and optimization settings.`;
    renderRows();
    $("download").disabled = false;
}
// No report: the counts and the table are empty, and the status says why.
function clear(message) {
  report = null; lastText = null;
  $("counts").replaceChildren(); $("entries").replaceChildren(); $("shown").textContent = ""; $("comparison").textContent = "";
  $("progress").value = 0; $("download").disabled = true; $("status").textContent = message;
}
async function refresh() {
  if (localRun) return;
  const wanted = area(), file = savedReport(wanted);
  $("report-link").href = file;
  try {
    const response = await fetch(file, { cache: "no-store" });
    if (!response.ok) throw Error(`No saved benchmark of the ${areaLabels[wanted].toLowerCase()} yet. Run it in this browser, or run npm run benchmark:cubical -- --area=${wanted}.`);
    const text = await response.text(); if (text === lastText || localRun || wanted !== area()) return;
    report = { area: wanted, ...JSON.parse(text) }; lastText = text;
    renderReport();
  } catch (error) { if (!localRun && wanted === area()) clear(error.message); }
}
$("search").oninput = renderRows; $("category").onchange = renderRows;
// Another area shows its saved benchmark; a run in this browser stops.
$("area").onchange = () => {
  const url = new URL(location.href); url.searchParams.set("area", area()); history.replaceState(null, "", url);
  stop(); localRun = false; clear("Loading the saved benchmark…"); refresh();
};
await refresh(); setInterval(refresh, 5000);

function stop() {
  worker?.terminate(); worker = null;
  $("run").disabled = false; $("cancel").disabled = true;
}
$("run").onclick = () => {
  stop(); localRun = true;
  const measured = area();
  const baseline = report?.complete ? { area: report.area ?? "archive", generatedAt: report.generatedAt, counts: report.counts, limitMs: report.limitMs, optimizations: report.optimizations } : report?.baseline;
  const limitMs = Number($("limit-ms").value);
  const optimizations = { shareSyntax: $("share-syntax").checked, reuseChecks: $("reuse-checks").checked, compactPaths: $("compact-paths").checked };
  report = { area: measured, limitMs, optimizations, declarations: [], generatedAt: new Date().toISOString(), complete: false, baseline };
  renderReport(); $("status").textContent = `Reading the ${areaLabels[measured].toLowerCase()} and starting the native kernel…`;
  $("run").disabled = true; $("cancel").disabled = false;
  worker = new Worker(new URL("./benchmark-worker.mjs", import.meta.url), { type: "module" });
  worker.onmessage = ({ data }) => {
    if (data.type === "error") { stop(); $("status").textContent = `Benchmark stopped: ${data.message}`; return; }
    report = { ...data.report, baseline }; renderReport();
    if (data.type === "complete") stop();
  };
  worker.onerror = event => { stop(); $("status").textContent = `Benchmark stopped: ${event.message}`; };
  worker.postMessage({ type: "run", area: measured, limitMs, optimizations });
};
$("cancel").onclick = () => { stop(); $("status").textContent = "Cancelled. Partial results remain below."; };
$("saved").onclick = () => { stop(); localRun = false; lastText = null; refresh(); };
$("download").onclick = () => {
  const url = URL.createObjectURL(new Blob([JSON.stringify(report, null, 2)], { type: "application/json" }));
  const a = document.createElement("a"); a.href = url; a.download = `cubical-benchmark-${report.area ?? "archive"}.json`; a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
};
