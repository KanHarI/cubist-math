const $ = id => document.getElementById(id);
const labels = { checked: "1 · Checked within 1s", optimize: "2 · Needs optimization",
  blocked: "3 · Blocked", failed: "4 · Needs fixing", template: "Universe template" };
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
  // Put actionable failures and timeouts first; retain source order within categories.
  const rank = { optimize: 0, failed: 1, blocked: 2, checked: 3, template: 4 };
  rows.sort((a, b) => rank[a.category] - rank[b.category]);
  const fragment = document.createDocumentFragment();
  const bindings = new Map(report.declarations.map(row => [row.binding, row]));
  for (const row of rows) {
    const tr = document.createElement("tr"); tr.dataset.category = row.category;
    const cells = Array.from({ length: 4 }, () => document.createElement("td"));
    cells[0].append(link(row)); cells[1].textContent = labels[row.category];
    cells[2].textContent = `${row.elapsedMs.toLocaleString(undefined, { maximumFractionDigits: 1 })} ms`;
    cells[3].textContent = row.reason ?? "Native kernel check passed.";
    const root = bindings.get(row.rootBlocker);
    if (root) { const small = document.createElement("small"); small.append("Root blocker: ", link(root)); cells[3].append(small); }
    tr.append(...cells); fragment.append(tr);
  }
  $("entries").replaceChildren(fragment);
  $("shown").textContent = `${rows.length.toLocaleString()} of ${report.declarations.length.toLocaleString()} declarations shown`;
}
function renderReport() {
    const counts = report.counts ?? Object.fromEntries(Object.keys(labels).map(c => [c, report.declarations.filter(d => d.category === c).length]));
    const total = report.total ?? report.declarations.length;
    $("status").textContent = `${report.complete ? "Completed" : "Running"} · ${new Date(report.generatedAt).toLocaleString()} · ${report.modules ?? "…"} modules · ${total} declarations${report.elapsedSeconds ? ` · ${report.elapsedSeconds}s elapsed` : ""}${report.revision ? ` · ${report.revision.slice(0, 8)}${report.dirty ? " + working changes" : ""}` : ""}`;
    $("progress").max = Math.max(1, total - (counts.template ?? 0)); $("progress").value = counts.checked ?? 0;
    $("counts").replaceChildren(...Object.entries(labels).map(([key, label]) => {
      const button = document.createElement("button"), number = document.createElement("strong");
      number.textContent = (counts[key] ?? 0).toLocaleString(); button.append(number, label);
      button.onclick = () => { $("category").value = key; renderRows(); }; return button;
    }));
    $("comparison").textContent = report.baseline ? `Checked since baseline: ${counts.checked - report.baseline.counts.checked >= 0 ? "+" : ""}${counts.checked - report.baseline.counts.checked}. Baseline recorded ${new Date(report.baseline.generatedAt).toLocaleString()}.` : "This run establishes the baseline.";
    renderRows();
    $("download").disabled = false;
}
async function refresh() {
  if (localRun) return;
  try {
    const response = await fetch("benchmark-results.json", { cache: "no-store" });
    if (!response.ok) throw Error("No benchmark report yet. Run npm run benchmark:cubical.");
    const text = await response.text(); if (text === lastText) return;
    report = JSON.parse(text); lastText = text;
    renderReport();
  } catch (error) { $("status").textContent = error.message; }
}
$("search").oninput = renderRows; $("category").onchange = renderRows;
await refresh(); setInterval(refresh, 5000);

function stop() {
  worker?.terminate(); worker = null;
  $("run").disabled = false; $("cancel").disabled = true;
}
$("run").onclick = () => {
  stop(); localRun = true;
  const baseline = report?.complete ? { generatedAt: report.generatedAt, counts: report.counts } : report?.baseline;
  report = { declarations: [], generatedAt: new Date().toISOString(), complete: false, baseline };
  renderReport(); $("status").textContent = "Reading the corpus and starting the native kernel…";
  $("run").disabled = true; $("cancel").disabled = false;
  worker = new Worker(new URL("./benchmark-worker.mjs", import.meta.url), { type: "module" });
  worker.onmessage = ({ data }) => {
    if (data.type === "error") { stop(); $("status").textContent = `Benchmark stopped: ${data.message}`; return; }
    report = { ...data.report, baseline }; renderReport();
    if (data.type === "complete") stop();
  };
  worker.onerror = event => { stop(); $("status").textContent = `Benchmark stopped: ${event.message}`; };
  worker.postMessage({ type: "run" });
};
$("cancel").onclick = () => { stop(); $("status").textContent = "Cancelled. Partial results remain below."; };
$("saved").onclick = () => { stop(); localRun = false; lastText = null; refresh(); };
$("download").onclick = () => {
  const url = URL.createObjectURL(new Blob([JSON.stringify(report, null, 2)], { type: "application/json" }));
  const a = document.createElement("a"); a.href = url; a.download = "cubical-benchmark.json"; a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
};
