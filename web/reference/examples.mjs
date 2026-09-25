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
  pre.after(bar);
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
      { detail: { base: base?.textContent ?? null, inputs: entries.map(entry => entry.input) } }));
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
