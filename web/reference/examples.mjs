// Checked reference examples become inspectable. Each example is checked in
// the browser by the same worker as the proof workspace; every name the
// checker links becomes clickable and opens the workspace's kernel inspector
// in a side panel, checked and inspected in the same way as in a proof.
import { tokenPattern, tokenStyle, numeralExpansion } from "../source-tokens.mjs";
import { enableTokenTips } from "../token-tips.mjs";
import { sourceModules, cubicalSourceModules, libraryModules } from "../mathscript/modules.mjs";
import { replTranscript } from "../repl-session.mjs";

const workerURL = new URL("../cubical-worker.mjs", import.meta.url);
const workspaceURL = new URL("../proof.html?example=1", import.meta.url);

let worker = null, ready = null, serial = 0;
const pending = new Map();
function request(command, args) {
  if (!worker) {
    worker = new Worker(workerURL, { type: "module" });
    ready = new Promise(resolve => {
      worker.onmessage = ({ data }) => {
        if (data.ready) return resolve();
        const waiting = pending.get(data.id);
        if (!waiting || data.progress) return;
        pending.delete(data.id);
        if (data.error) waiting.reject(Object.assign(new Error(data.error.message), data.error));
        else waiting.resolve(data.result);
      };
    });
  }
  return ready.then(() => new Promise((resolve, reject) => {
    const id = ++serial;
    pending.set(id, { resolve, reject });
    worker.postMessage({ id, command, args });
  }));
}

// The worker keeps one program at a time, so examples are checked in turn.
let queue = Promise.resolve();
const checkInTurn = source => (queue = queue.then(() => request("check", { source, module: "reference_example" }))
  .catch(error => ({ error })));

const encode = source => btoa(String.fromCharCode(...new TextEncoder().encode(source)))
  .replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
const workspaceLink = source => `${workspaceURL.href}#source=${encode(source)}`;

// Highlight source as the workspace's Read view does. Names the checker linked
// become buttons that open the kernel inspector, and an imported module's
// name links to its source in the workspace.
const modules = new Set([...sourceModules, ...cubicalSourceModules, ...libraryModules]);
function render(code, source, links = []) {
  const imports = new Map([...source.matchAll(/^\s*import\s+([A-Za-z_][A-Za-z_0-9]*)\s*;/gm)]
    .filter(match => modules.has(match[1]))
    .map(match => [match.index + match[0].lastIndexOf(match[1]), match[1]]));
  const linkAt = new Map();
  for (const link of links) {
    const old = linkAt.get(link.start);
    if (!old || link.end - link.start < old.end - old.start) linkAt.set(link.start, link);
  }
  const parts = [];
  for (const match of source.matchAll(tokenPattern)) {
    const text = match[0], start = match.index;
    if (text.startsWith("//")) {
      const span = document.createElement("span");
      span.className = "comment";
      span.textContent = text;
      parts.push(span);
      continue;
    }
    if (imports.has(start)) {
      const link = document.createElement("a");
      link.className = "example-module";
      link.textContent = text;
      link.href = new URL(`../proof.html?proof=${encodeURIComponent(text)}`, import.meta.url).href;
      link.title = `Open the ${text} module`;
      parts.push(link);
      continue;
    }
    const expansion = numeralExpansion(text) ?? linkAt.get(start)?.expansion;
    const style = tokenStyle(text, expansion), link = linkAt.get(start);
    if (link) {
      const button = document.createElement("button");
      button.type = "button";
      button.className = `example-token${style ? ` ${style}` : ""}`;
      button.textContent = text;
      if (expansion && expansion !== text) button.dataset.tip = `${text} expands to ${expansion}`;
      else button.title = `Inspect ${text} as a checked kernel term`;
      button.onclick = () => openInspector(source, start);
      parts.push(button);
    } else if (style) {
      const span = document.createElement("span");
      span.className = style;
      span.textContent = text;
      if (expansion && expansion !== text) span.dataset.tip = `${text} expands to ${expansion}`;
      parts.push(span);
    } else parts.push(document.createTextNode(text));
  }
  code.replaceChildren(...parts);
}

let drawer = null, frameReady = null;
function openInspector(source, offset) {
  if (!drawer) {
    drawer = document.createElement("aside");
    drawer.className = "inspector-drawer";
    drawer.setAttribute("aria-label", "Kernel inspector");
    const head = document.createElement("div"), title = document.createElement("strong");
    const open = document.createElement("a"), close = document.createElement("button");
    head.className = "drawer-head";
    title.textContent = "Kernel inspector";
    open.textContent = "Open in workspace ↗";
    open.target = "_blank";
    open.rel = "noopener";
    close.type = "button";
    close.textContent = "Close";
    close.onclick = () => { drawer.hidden = true; document.body.classList.remove("inspector-open"); };
    head.append(title, open, close);
    const frame = document.createElement("iframe");
    frame.title = "Kernel inspector";
    frame.src = `${workspaceURL.href}&embed=1`;
    frameReady = new Promise(resolve => addEventListener("message", ({ data, source: from }) => {
      if (from === frame.contentWindow && data?.type === "cubist-ready") resolve();
    }));
    drawer.append(head, frame);
    document.body.append(drawer);
  }
  drawer.hidden = false;
  document.body.classList.add("inspector-open");
  drawer.querySelector("a").href = workspaceLink(source);
  const frame = drawer.querySelector("iframe");
  frameReady.then(() => frame.contentWindow.postMessage({ type: "cubist-inspect", source, offset }, location.origin));
}

// An example marked data-elaborate has a collapsed Elaboration panel: each
// declaration's source, type, proof statements with their goals and the terms
// they built, the finished term, and the kernel's term and type as opcode
// trees. It is computed by the checker when first opened.
const element = (tag, className, text) => {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
};
const kernelPage = new URL("../kernel.html", import.meta.url).href;
function sourceCode(text) {
  const code = element("code");
  render(code, text);
  return code;
}
// The kernel's check as a forward derivation, in the style of THTH's proofs:
// each step applies one rule (opcode) to earlier steps, under a comment with
// the judgement or context it derives. Steps the elaborator added are marked.
function derivationList({ steps, truncated }) {
  const section = element("div", "kernel-derivation");
  const legend = element("p", "derivation-note");
  const reference = element("a", null, "kernel reference");
  reference.href = new URL("../kernel.html#trace", import.meta.url).href;
  legend.append(`The kernel’s check as a forward derivation: each of the ${steps.length} steps applies one rule to earlier steps, `
    + "and the comment above it is the judgement or context it derives. The ", reference, " explains the rules.");
  const list = element("ol", "derivation");
  for (const step of steps) {
    const item = element("li", `derivation-step${step.scaffold ? " derivation-scaffold" : ""}`);
    item.append(element("div", "derivation-comment", `// ${step.comment}`));
    const line = element("div", "derivation-rule");
    line.append(element("span", "derivation-number", String(step.number)), " ", element("span", "opcode", step.rule),
      `(${step.premises.join(", ")})`);
    if (step.scaffold) line.append(element("span", "derivation-added", step.scaffold));
    item.append(line);
    list.append(item);
  }
  section.append(legend, list);
  if (truncated) section.append(element("p", "derivation-note", "… the rest of the derivation is not shown."));
  return section;
}
function renderElaboration(panel, declarations) {
  const body = element("div", "elaboration-body");
  body.append(element("p", "elaboration-legend",
    "For each proof statement: the goal it faces, with the names in scope before ⊢, and the part of the term it builds; ? stands for what the following statements build."));
  for (const declaration of declarations) {
    const section = element("section", "elaboration-declaration");
    const title = element("h4");
    title.append(element("code", null, declaration.name));
    section.append(title);
    const rows = element("dl", "elaboration-stages");
    const row = (label, ...content) => { rows.append(element("dt", null, label)); const cell = element("dd"); cell.append(...content); rows.append(cell); };
    const source = element("pre");
    source.append(sourceCode(declaration.source));
    row("Source", source);
    if (!declaration.verified || declaration.reason) {
      row("Result", element("span", "elaboration-error", declaration.reason ?? "Not checked."));
      section.append(rows);
      body.append(section);
      continue;
    }
    row("Type", sourceCode(declaration.type));
    if (declaration.steps.length) {
      const list = element("ol", "elaboration-steps");
      for (const step of declaration.steps) {
        const item = element("li");
        const goal = element("div", "elaboration-goal");
        goal.append(sourceCode(step.locals.map(local => `${local.name} : ${local.type}`).join(", ")), element("span", "turnstile", " ⊢ "), sourceCode(step.goal));
        const built = element("div", "elaboration-built");
        built.append(element("span", "maps-to", "builds "), sourceCode(step.built));
        item.append(sourceCode(step.text), goal, built);
        list.append(item);
      }
      row("Statements", list);
    } else row("Statements", element("span", null, "None: the value is given directly after :=."));
    row("Term", sourceCode(declaration.term));
    const note = element("p", "elaboration-checked");
    const link = element("a", null, "For more info");
    link.href = kernelPage;
    note.append("✓ The C kernel checked this term at this type. ", link, " on the kernel and its rules, see the kernel reference.");
    row("Kernel", derivationList(declaration.derivation), note);
    section.append(rows);
    body.append(section);
  }
  panel.querySelector(".elaboration-body")?.remove();
  panel.append(body);
}
const elaborateInTurn = source => {
  const run = queue.then(() => request("elaborate", { source, module: "reference_example" }));
  queue = run.catch(() => {});
  return run;
};

function enhance(pre, code) {
  const source = code.textContent;
  const bar = document.createElement("div");
  bar.className = "example-bar";
  const status = document.createElement("span"), open = document.createElement("a");
  status.textContent = "Checking…";
  open.textContent = "Open in workspace ↗";
  open.href = workspaceLink(source);
  open.target = "_blank";
  open.rel = "noopener";
  bar.append(status, open);
  // Pages with a REPL bar load its script.
  if (document.querySelector('script[src*="repl-dock"]')) {
    const repl = document.createElement("button");
    repl.type = "button";
    repl.className = "repl-fork";
    repl.textContent = "Open in REPL ↓";
    repl.title = "Load this example into the REPL bar and continue there";
    repl.onclick = () => document.dispatchEvent(new CustomEvent("cubist-repl-fork",
      { detail: { base: source, inputs: [], label: "Loaded the example:" } }));
    open.before(repl);
  }
  pre.after(bar);
  if (code.dataset.elaborate !== undefined) {
    const panel = element("details", "elaboration");
    const summary = element("summary", null, "Elaboration: each declaration, step by step");
    panel.append(summary);
    panel.addEventListener("toggle", () => {
      if (!panel.open || panel.dataset.loaded) return;
      panel.dataset.loaded = "true";
      const waiting = element("p", "elaboration-body", "Elaborating…");
      panel.append(waiting);
      elaborateInTurn(source).then(declarations => renderElaboration(panel, declarations),
        error => { waiting.textContent = `Elaboration failed: ${error.message}`; });
    });
    bar.after(panel);
  }
  checkInTurn(source).then(result => {
    const links = result?.links ?? [];
    if (links.length) render(code, source, links);
    const evaluations = (result?.evaluations ?? []).map(evaluation => `${evaluation.name}: ${evaluation.value}`);
    status.textContent = [links.length ? "Click a name to inspect its kernel term" : result?.error ? "Not checked" : "",
      ...evaluations.map(text => `evaluate ${text}`)].filter(Boolean).join(" · ");
  });
}

// A REPL example is a read-only transcript (see replTranscript). It runs on
// top of the example before it, as the test suite checks; Fork into REPL
// replays it in the page's REPL bar.
function renderTranscript(code) {
  const entries = replTranscript(code.textContent), pre = code.parentElement;
  const examples = [...document.querySelectorAll("pre > code[data-check]")];
  const base = examples.slice(0, examples.indexOf(code)).reverse().find(other => other.dataset.check === "accept");
  const parts = [];
  const line = (className, text, prompt) => {
    const span = document.createElement("span"), content = document.createElement("span");
    span.className = className;
    if (prompt) span.append(Object.assign(document.createElement("span"), { className: "repl-prompt", textContent: "› " }));
    render(content, text);
    span.append(content);
    return span;
  };
  for (const { input, results } of entries) {
    parts.push(line("repl-transcript-entry", input, true));
    for (const result of results) parts.push(line("repl-transcript-result", result));
  }
  code.replaceChildren(...parts);
  pre.classList.add("repl-transcript");
  const bar = document.createElement("div"), note = document.createElement("span");
  bar.className = "example-bar";
  note.textContent = base ? "A REPL session with the example above loaded" : "A REPL session";
  bar.append(note);
  // Pages with a REPL bar load its script.
  if (document.querySelector('script[src*="repl-dock"]')) {
    const fork = document.createElement("button");
    fork.type = "button";
    fork.className = "repl-fork";
    fork.textContent = "Fork into REPL ↓";
    fork.title = "Run this session in the REPL bar, where you can continue it";
    fork.onclick = () => document.dispatchEvent(new CustomEvent("cubist-repl-fork",
      { detail: { base: base?.textContent ?? null, inputs: entries.map(entry => entry.input),
        label: "Loaded the example above the transcript:" } }));
    bar.append(fork);
  }
  pre.after(bar);
}

// Every Cubist example is highlighted at once; checked ones gain links later.
enableTokenTips();
for (const code of document.querySelectorAll('pre > code[data-check]:not([data-check="cli"]):not([data-check="repl"])'))
  render(code, code.textContent);
for (const code of document.querySelectorAll('pre > code[data-check="repl"]')) renderTranscript(code);
const examples = [...document.querySelectorAll('pre > code[data-check="accept"], pre > code[data-check="reject"]')];
const observer = new IntersectionObserver(entries => {
  for (const entry of entries) if (entry.isIntersecting) {
    observer.unobserve(entry.target);
    enhance(entry.target.parentElement, entry.target);
  }
}, { rootMargin: "400px 0px" });
for (const code of examples) observer.observe(code);
