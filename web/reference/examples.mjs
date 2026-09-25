// Checked reference examples become inspectable. Each example is checked in
// the browser by the same worker as the proof workspace; every name the
// checker links becomes clickable and opens the workspace's kernel inspector
// in a side panel, checked and inspected in the same way as in a proof.
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

// The shortest link at each start, without overlaps, as in the workspace.
function linkRanges(links) {
  const byStart = new Map();
  for (const link of links) {
    const old = byStart.get(link.start);
    if (!old || link.end - link.start < old.end - old.start) byStart.set(link.start, link);
  }
  const ranges = [];
  for (const link of [...byStart.values()].sort((a, b) => a.start - b.start))
    if (!ranges.length || link.start >= ranges.at(-1).end) ranges.push(link);
  return ranges;
}

function renderLinks(code, source, links) {
  const parts = [];
  let cursor = 0;
  for (const link of linkRanges(links)) {
    if (link.start > cursor) parts.push(document.createTextNode(source.slice(cursor, link.start)));
    const button = document.createElement("button");
    button.type = "button";
    button.className = "example-token";
    button.textContent = source.slice(link.start, link.end);
    button.title = `Inspect ${button.textContent} as a checked kernel term`;
    button.onclick = () => openInspector(source, link.start);
    parts.push(button);
    cursor = link.end;
  }
  parts.push(document.createTextNode(source.slice(cursor)));
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
    if (links.length) renderLinks(code, source, links);
    const evaluations = (result?.evaluations ?? []).map(evaluation => `${evaluation.name}: ${evaluation.value}`);
    status.textContent = [links.length ? "Click a name to inspect its kernel term" : result?.error ? "Not checked" : "",
      ...evaluations.map(text => `evaluate ${text}`)].filter(Boolean).join(" · ");
  });
}

const examples = [...document.querySelectorAll('pre > code[data-check="accept"], pre > code[data-check="reject"]')];
const observer = new IntersectionObserver(entries => {
  for (const entry of entries) if (entry.isIntersecting) {
    observer.unobserve(entry.target);
    enhance(entry.target.parentElement, entry.target);
  }
}, { rootMargin: "400px 0px" });
for (const code of examples) observer.observe(code);
