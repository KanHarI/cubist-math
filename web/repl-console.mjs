// A REPL console: a log of entries and their results, and an input box.
// Enter runs the input, unless a bracket is still open; Shift+Enter adds a
// line; ↑ and ↓ recall earlier entries. `run(text)` returns the results of
// a ReplSession (see repl-session.mjs).
import { tokenPattern, tokenStyle, numeralExpansion } from "./source-tokens.mjs";
import { replStatements, consoleCommands } from "./repl-session.mjs";

const element = (tag, className, text) => {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
};

// Source highlighted as in the proof view.
function highlighted(source) {
  const code = element("code");
  for (const [text] of source.matchAll(tokenPattern)) {
    const style = text.startsWith("//") ? "comment" : text === "typeof" ? "keyword" : tokenStyle(text, numeralExpansion(text));
    code.append(style ? element("span", style, text) : document.createTextNode(text));
  }
  return code;
}

export function createReplConsole(root, { run, reset, greeting = [], label = "REPL input" }) {
  root.classList.add("repl");
  const log = element("div", "repl-log");
  log.setAttribute("role", "log");
  log.setAttribute("aria-live", "polite");
  const form = element("form", "repl-form");
  const prompt = element("span", "repl-prompt", "›");
  prompt.setAttribute("aria-hidden", "true");
  const input = element("textarea", "repl-text");
  Object.assign(input, { rows: 1, spellcheck: false, autocapitalize: "off", autocomplete: "off",
    placeholder: "let x := 7;   typeof x;   evaluate x;   /help" });
  input.setAttribute("aria-label", label);
  const runButton = element("button", "repl-run", "Run"), clearButton = element("button", "repl-clear", "Clear");
  runButton.type = "submit";
  clearButton.type = "button";
  const restartButton = element("button", "repl-restart", "Restart");
  restartButton.type = "button";
  restartButton.title = "Start a new session: forget every name defined here";
  form.append(prompt, input, runButton, clearButton, ...reset ? [restartButton] : []);
  root.append(log, form);

  const show = ({ kind, text }) => {
    const line = element("pre", `repl-result repl-${kind}`);
    // Results are Cubist and highlighted; messages are prose.
    line.append(["error", "info", "help"].includes(kind) ? document.createTextNode(text) : highlighted(text));
    log.append(line);
  };
  const scroll = () => { log.scrollTop = log.scrollHeight; };
  for (const text of greeting) show({ kind: "info", text });

  const history = [];
  let recalled = history.length, busy = false;
  const grow = () => { input.style.height = "auto"; input.style.height = `${input.scrollHeight}px`; };
  const recall = index => {
    recalled = Math.max(0, Math.min(history.length, index));
    input.value = history[recalled] ?? "";
    grow();
  };

  // Run an entry as if typed. Without echo, only its results are shown.
  async function execute(text, { echo = true } = {}) {
    if (echo) {
      history.push(text);
      recalled = history.length;
      const entry = element("pre", "repl-entry");
      entry.append(element("span", "repl-prompt", "› "), highlighted(text));
      log.append(entry);
    }
    busy = true;
    form.classList.add("busy");
    runButton.disabled = true;
    scroll();
    try {
      const results = await run(text);
      for (const result of results) show(result);
      if (!results.length && echo) show({ kind: "info", text: "Nothing to run." });
    } catch (error) {
      show({ kind: "error", text: error.message });
    } finally {
      busy = false;
      form.classList.remove("busy");
      runButton.disabled = false;
      scroll();
    }
  }
  async function submit() {
    const text = input.value.trim();
    if (!text || busy) return;
    input.value = "";
    grow();
    // /clear and /restart act on the console itself.
    if (consoleCommands.has(text.replace(/;$/, ""))) {
      history.push(text);
      recalled = history.length;
      if (text.startsWith("/clear")) log.replaceChildren();
      else if (reset) await restart();
      else show({ kind: "error", text: "This console cannot restart." });
      return;
    }
    await execute(text);
  }
  async function restart() {
    await reset();
    log.replaceChildren();
    show({ kind: "info", text: "Started a new session." });
  }

  form.onsubmit = event => { event.preventDefault(); submit(); };
  clearButton.onclick = () => { log.replaceChildren(); input.focus(); };
  restartButton.onclick = async () => {
    if (busy) return;
    await restart();
    input.focus();
  };
  input.addEventListener("input", grow);
  input.addEventListener("keydown", event => {
    if (event.key === "Enter" && !event.shiftKey && !event.isComposing) {
      // An open bracket means the entry continues on the next line.
      if (replStatements(input.value).depth > 0) return;
      event.preventDefault();
      submit();
    } else if (event.key === "ArrowUp" && !input.value.slice(0, input.selectionStart).includes("\n")) {
      if (recalled > 0) { event.preventDefault(); recall(recalled - 1); }
    } else if (event.key === "ArrowDown" && !input.value.slice(input.selectionEnd).includes("\n")) {
      if (recalled < history.length) { event.preventDefault(); recall(recalled + 1); }
    }
  });
  return { input, log, show, focus: () => input.focus(), enter: execute, restart,
    load: text => execute(text, { echo: false }) };
}

// A REPL with its own worker and an empty program, for pages without a proof.
// The worker starts on first use.
export function standaloneRepl() {
  let worker = null, ready = null, serial = 0;
  const pending = new Map();
  const request = (command, args) => {
    if (!worker) {
      worker = new Worker(new URL("./cubical-worker.mjs", import.meta.url), { type: "module" });
      ready = new Promise(resolve => {
        worker.onmessage = ({ data }) => {
          if (data.ready) return resolve();
          const waiting = pending.get(data.id);
          if (!waiting || data.progress) return;
          pending.delete(data.id);
          if (data.error) waiting.reject(new Error(data.error.message));
          else waiting.resolve(data.result);
        };
      });
    }
    return ready.then(() => new Promise((resolve, reject) => {
      const id = ++serial;
      pending.set(id, { resolve, reject });
      worker.postMessage({ id, command, args });
    }));
  };
  return {
    run: input => request("repl", { input, fresh: true }),
    reset: () => request("repl-reset", { fresh: true }),
  };
}
