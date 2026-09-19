import catalogue from "./proofs/catalogue.mjs";
import { proofRequestWatchdog } from "./proof-watchdog.mjs";
const choices = [
  { id: "curve_tag_stability", title: "Curve contours · fine meshes control admissible tag changes", complexDevelopment: true },
  { id: "uniform_curve_tags", title: "Curve sampling · continuity bounds integrand errors", complexDevelopment: true },
  { id: "interval_sampling", title: "Curve sampling · admissible endpoint tags and mesh bounds", complexDevelopment: true },
  { id: "interval_tag_bounds", title: "Curve sampling · tags in a short interval are close", complexDevelopment: true },
  { id: "sample_tagged", title: "Curve sampling · explicit endpoint tag lists", complexDevelopment: true },
  { id: "parameter_tag_sampling", title: "Curve sampling · local tag bounds control all samples", complexDevelopment: true },
  { id: "curve_contour_estimates", title: "Curve contours · finite tag-change estimates", complexDevelopment: true },
  { id: "parameter_contour_estimates", title: "Curve contours · finite estimates with parameter weights", complexDevelopment: true },
  { id: "curve_contour_limits", title: "Curve contours · affine tag-independent limits", complexDevelopment: true },
  { id: "parameter_contour_limits", title: "Curve contours · limits with parameter weights", complexDevelopment: true },
  { id: "parameter_contour_bounds", title: "Curve contours · parameter-based error estimates", complexDevelopment: true },
  { id: "parameter_increment_bounds", title: "Curve contours · coordinate increment certificates", complexDevelopment: true },
  { id: "parameter_contours", title: "Curve contours · sums on mapped samples", complexDevelopment: true },
  { id: "sample_maps", title: "Curve sampling · mapping vertices and tags", complexDevelopment: true },
  { id: "complex_curve_variation", title: "Complex curves · bounded coordinate variation", complexDevelopment: true },
  { id: "affine_variation", title: "Curve sampling · ordered affine increment bounds", complexDevelopment: true },
  { id: "interval_weights", title: "Curve sampling · telescoping interval weights", complexDevelopment: true },
  { id: "sample_relations", title: "Curve sampling · conditions on adjacent vertices", complexDevelopment: true },
  { id: "complex_curves", title: "Complex curves · continuous straight segments and endpoints", complexDevelopment: true },
  { id: "complex_affine", title: "Complex curves · constructive uniform continuity", complexDevelopment: true },
  { id: "field_interval", title: "Curve parameters · the closed unit interval", complexDevelopment: true },
  { id: "field_affine", title: "Affine estimates · parameter differences control increments", complexDevelopment: true },
  { id: "complex_contour_tag_limits", title: "Complex contours · tag-independent limits", complexDevelopment: true },
  { id: "complex_contour_bounds", title: "Complex contours · coordinate variation estimates", complexDevelopment: true },
  { id: "field_scale_limits", title: "Limits · fixed factors preserve vanishing errors", complexDevelopment: true },
  { id: "complex_convergence", title: "Complex limits · convergence and Cauchy definitions", complexDevelopment: true },
  { id: "complex_contour_samples", title: "Complex contours · finite sums", complexDevelopment: true },
  { id: "contour_tag_limits", title: "Contour estimates · vanishing tag errors", complexDevelopment: true },
  { id: "contour_error_bounds", title: "Contour estimates · error times variation", complexDevelopment: true },
  { id: "complex_magnitude", title: "Complex estimates · coordinate bounds without square roots", complexDevelopment: true },
  { id: "field_magnitude_close", title: "Error bounds · closeness and convergence to zero", complexDevelopment: true },
  { id: "sample_magnitude_bounds", title: "Finite estimates · weighted sums and variation", complexDevelopment: true },
  { id: "sample_magnitude", title: "Finite estimates · bounds at sampled edges", complexDevelopment: true },
  { id: "field_magnitude", title: "Ordered estimates · constructive magnitude bounds", complexDevelopment: true },
  { id: "complex_contour_sums", title: "Contour sums · complex composition and backtracking", complexDevelopment: true },
  { id: "contour_examples", title: "Contour sums · finite backtracking errors", complexDevelopment: true },
  { id: "contour_refinement", title: "Contour sums · refinement and tag errors", complexDevelopment: true },
  { id: "contour_samples", title: "Contour sums · samples and oriented increments", complexDevelopment: true },
  { id: "contour_sums", title: "Contour sums · linearity and telescoping", complexDevelopment: true },
  { id: "sample_error_bounds", title: "Finite sums · accumulated error bounds", complexDevelopment: true },
  { id: "sample_sum_laws", title: "Finite sums · composition and telescoping", complexDevelopment: true },
  { id: "sample_chains", title: "Sampling data · vertices, tags and concatenation", complexDevelopment: true },
  { id: "homotopy_limits", title: "Homotopy periods · limits descend from curves", punctureDevelopment: true },
  { id: "surjective_descent", title: "Descent · unique values without chosen representatives" },
  { id: "descent_loop_laws", title: "Homotopy periods · composition through representatives", punctureDevelopment: true },
  { id: "complex_limit_periods", title: "Complex periods · constructed from Cauchy approximations", punctureDevelopment: true },
  { id: "limit_periods", title: "Homotopy periods · limits of approximate laws", punctureDevelopment: true },
  { id: "complex_limits", title: "Complex analysis · completeness and limit laws", complexDevelopment: true },
  { id: "field_asymptotics", title: "Limits · vanishing errors preserve the limit", complexDevelopment: true },
  { id: "field_limits", title: "Limits · uniqueness, addition and Cauchy sequences", complexDevelopment: true },
  { id: "field_closeness", title: "Error bounds · triangle, addition and separation", complexDevelopment: true },
  { id: "ordered_halves", title: "Ordered fields · constructive halving", complexDevelopment: true },
  { id: "cauchy_ordered", title: "Cauchy quotient · closeness assumptions proved", realDevelopment: true },
  { id: "complex_numbers", title: "Complex numbers · coordinates and operations", complexDevelopment: true },
  { id: "puncture_periods", title: "Puncture periods · the winding sum formula", punctureDevelopment: true },
  { id: "complex_periods", title: "Complex periods · local contributions and winding", punctureDevelopment: true },
  { id: "puncture_period_examples", title: "Periods · noncontractible loop with zero period", punctureDevelopment: true },
  { id: "integer_multiples", title: "Additive groups · signed integer multiples" },
  { id: "finite_sums", title: "Finite sums · additivity and single terms" },
  { id: "ordered_bounds", title: "Ordered fields · constructive inequality bounds", complexDevelopment: true },
  { id: "quadratic_identities", title: "Quadratic algebra · parallelogram identity", complexDevelopment: true },
  { id: "circle_degree", title: "Circle degree · obstruction to contraction", complexDevelopment: true },
  { id: "complex_deformation", title: "Complex deformations · dominant term avoids zero", complexDevelopment: true },
  { id: "homotopy_paths", title: "Homotopies · moving basepoints and contractions", complexDevelopment: true },
  { id: "complex_inverses", title: "Complex numbers · constructive inverses and apartness", complexDevelopment: true },
  { id: "classical_complex_inverses", title: "Complex numbers · nonzero inverses using excluded middle", complexDevelopment: true },
  { id: "ordered_squares", title: "Ordered fields · constructive square positivity", complexDevelopment: true },
  { id: "complex_norm_coordinates", title: "Complex numbers · multiplicative norm", complexDevelopment: true },
  { id: "complex_algebra", title: "Complex numbers · ring, conjugation and inverses", complexDevelopment: true },
  { id: "complex_polynomials", title: "Polynomials · roots and algebraic closure target", complexDevelopment: true },
  { id: "polynomial_difference", title: "Polynomials · difference and factor identities", complexDevelopment: true },
  { id: "complex_coordinates", title: "Complex numbers · coordinate identities", complexDevelopment: true },
  { id: "ring_laws", title: "Ring algebra · derived identities", complexDevelopment: true },
  { id: "field_products", title: "Field foundations · products are sets", complexDevelopment: true },
  { id: "bouquet_generation", title: "Punctures · every loop is a word", punctureDevelopment: true },
  { id: "puncture_noncommutative", title: "Punctures · zero winding, nontrivial loop", punctureDevelopment: true },
  { id: "bouquet_invariants", title: "Loop invariants · determined by generators", punctureDevelopment: true },
  { id: "puncture_winding", title: "Punctures · winding around each generator", punctureDevelopment: true },
  { id: "puncture_graph", title: "Punctures · graph and generating loops", punctureDevelopment: true },
  { id: "loop_words", title: "Loop words · evaluation and cancellation", punctureDevelopment: true },
  { id: "bouquet_actions", title: "Loop actions · transport in local systems", punctureDevelopment: true },
  { id: "bouquet_cover", title: "Loop generation · auxiliary family", punctureDevelopment: true },
  { id: "path_actions", title: "Paths · append, map and reconnect", punctureDevelopment: true },
  { id: "complete_fields", title: "Real numbers · shared completeness interface", realDevelopment: true },
  { id: "dedekind_cuts", title: "Real numbers · constructive Dedekind cuts", realDevelopment: true },
  { id: "boolean_cuts", title: "Real numbers · classical Boolean cuts", realDevelopment: true },
  { id: "cauchy_quotient", title: "Real numbers · ordinary Cauchy quotient", realDevelopment: true },
  { id: "ordered_fields", title: "Ordered fields · laws and algebraic lemmas", realDevelopment: true },
  { id: "set_quotients", title: "Equivalence classes · representatives and choice", realDevelopment: true },
  { id: "field_logic", title: "Field foundations · logic in Type1", realDevelopment: true },
  { id: "field_extensionality", title: "Field foundations · predicate equality", realDevelopment: true },
  { id: "surjections", title: "Surjections · right inverses and choice" },
  { id: "maps", title: "Maps · injections, embeddings and fibers" },
  { id: "classical", title: "Classical logic · excluded middle" },
  { id: "schroeder_bernstein", title: "Cantor–Schröder–Bernstein · mutual injections" },
  { id: "binomial_counting", title: "Binomial types · finite cardinality" },
  { id: "permutations", title: "Permutations · factorials" },
  { id: "binomial_types", title: "Binomial types · Rijke construction" },
  { id: "binomial_pascal", title: "Binomial types · Pascal bijection" },
  { id: "truncation", title: "Propositional truncation · explicit principles" },
  { id: "finite_cancellation", title: "Finite types · cancellation and cardinality" },
  { id: "bijection_equality", title: "Bijections · equality and coherence" },
  { id: "function_counting", title: "Finite functions · powers" },
  { id: "binomial", title: "Subsets · Pascal counting" },
  { id: "finite", title: "Finite types · sums of Unit" },
  { id: "equivalences", title: "Bijections · reusable constructions" },
  { id: "groups", title: "Groups · structures and isomorphisms" },
  { id: "sets", title: "Sets · decidable equality" },
  { id: "circle", title: "Circle · fundamental group is Z" },
  { id: "integers", title: "Integers · successor equivalence" },
  { id: "paths", title: "Paths · equality reasoning" },
  { id: "suspension", title: "Suspension & the circle · foundations" },
  { id: "euclid", title: "Euclid · mathematical proof" },
  { id: "basics", title: "Functions, pairs & induction · examples" },
  { id: "primes", title: "Primes · mathematical foundations" },
  ...catalogue.map((p) => ({
    ...p,
    id: p.id + "_construction",
    file: p.id + ".construction.proof",
    title: p.title + " · kernel audit",
  })),
];
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
for (const id of ["reuse-normal-forms", "memoize-instructions", "index-fresh-contexts"]) {
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
for (const item of choices) {
  const option = document.createElement("option");
  option.value = item.id;
  option.textContent = item.title;
  $("proof-picker").append(option);
}
$("proof-picker").value = proofId;
function rememberDraft() {
  try {
    sessionStorage.setItem(
      "mathscript:" + proofId,
      JSON.stringify({ source: $("editor").value, baseline: original }),
    );
  } catch {}
}
$("proof-picker").onchange = () => {
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
  return { normalForms: $("reuse-normal-forms").checked, instructions: $("memoize-instructions").checked, freshContexts: $("index-fresh-contexts").checked };
}
function refreshStatus() {
  $("check").disabled = !ready || pending.size > 0;
  for (const id of ["reuse-normal-forms", "memoize-instructions", "index-fresh-contexts"])
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
const axiomLabels = {
  lib_univalence: "Univalence",
  lib_ua_elim: "Univalence transport computation",
  lib_funext: "Function extensionality",
  lib_funext_compute: "Function extensionality computation",
  lib_LEM: "Excluded middle",
  lib_AOC: "Axiom of choice",
  LEM: "Excluded middle",
  AOC: "Axiom of choice",
  lib_Trunc: "Propositional truncation",
  lib_trunc_intro: "Truncation introduction",
  lib_trunc_elim: "Truncation elimination",
  lib_trunc_is_trunc: "Truncation is a proposition",
};
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
    button.onclick = () =>
      inspect(
        decorate({
          binding,
          name: binding,
          role: "explicit axiom",
          ...[...last.outputs, ...last.imports].find(o => o.binding === binding),
          ...(last.preludeAxioms?.includes(binding)
            ? {
                sourceModule: "prelude_library_construction",
                sourceName: binding,
              }
            : {}),
        }),
      );
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
      } else if (keywords.has(text)) {
        const span = document.createElement("span");
        span.className = "keyword";
        span.textContent = text;
        code.append(span);
      } else if (linkMap.has(start)) {
        const info = linkMap.get(start);
        if (info) {
          const button = document.createElement("button");
          button.className = "reference";
          button.textContent = text;
          button.title = `Inspect ${text}`;
          button.dataset.name = text;
          button.onclick = () =>
            inspect({ ...decorate(info), line: index + 1 });
          code.append(button);
        } else code.append(document.createTextNode(text));
      } else code.append(document.createTextNode(text));
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
  $("kernel-details").open = false;
  $("kernel-expression").textContent = "";
  $("kernel-type").textContent = "";
  $("kernel-inference").textContent = "";
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
function renderKernel(view) {
  renderAxioms($("inspect-axioms"), view.axioms ?? []);
  $("kernel-expression").textContent = view.expression
    ? layout(view.expression, view.contextNames).text
    : "Context assumption";
  $("kernel-type").textContent = layout(view.type, view.contextNames).text;
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
    !truncated(view.expression) && !truncated(view.type);
}
function download(text, name, type) {
  const url = URL.createObjectURL(new Blob([text], { type })),
    a = document.createElement("a");
  a.href = url;
  a.download = name;
  a.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
$("check").onclick = check;
for (const id of ["reuse-normal-forms", "memoize-instructions", "index-fresh-contexts"]) $(id).onchange = () => {
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
$("example").onclick = () => {
  rememberDraft();
  location.href = "proof.html?proof=euclid";
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
