// A foldable REPL at the bottom of the reference pages. It starts closed,
// and its kernel worker starts when it is first opened, with an empty
// program: examples from the page can be typed or pasted in.
import { createReplConsole, standaloneRepl } from "../repl-console.mjs";

const remembered = "cubist:reference-repl-open";
const dock = document.createElement("section");
dock.className = "repl-dock";
dock.setAttribute("aria-label", "REPL");
const bar = document.createElement("div"), toggle = document.createElement("button");
const hint = document.createElement("span"), page = document.createElement("a");
bar.className = "repl-dock-bar";
toggle.type = "button";
toggle.className = "repl-dock-toggle";
toggle.setAttribute("aria-controls", "repl-dock-body");
hint.textContent = "Try Cubist here: let x := 7;  typeof x;  evaluate x;";
page.href = new URL("../repl.html", import.meta.url).href;
page.textContent = "Full-page REPL ↗";
bar.append(toggle, hint, page);
const body = document.createElement("div");
body.className = "repl-dock-body";
body.id = "repl-dock-body";
dock.append(bar, body);
document.body.append(dock);
document.body.classList.add("repl-docked");

let repl = null;
function setOpen(open) {
  body.hidden = !open;
  toggle.setAttribute("aria-expanded", String(open));
  toggle.textContent = open ? "REPL ▾" : "REPL ▴";
  document.body.classList.toggle("repl-open", open);
  try { localStorage.setItem(remembered, String(open)); } catch { /* Not remembered. */ }
  // The console is mounted inside, so its display never overrides hidden.
  if (open && !repl) repl = createReplConsole(body.appendChild(document.createElement("div")), {
    ...standaloneRepl(),
    greeting: ["Each entry is checked by the kernel, as in a file. import naturals; enables + and *. help lists every command."],
  });
}
toggle.onclick = () => {
  setOpen(body.hidden);
  if (!body.hidden) repl.focus();
};
let open = false;
try { open = localStorage.getItem(remembered) === "true"; } catch { /* Closed. */ }
setOpen(open);

// An example opens in this REPL, and a read-only REPL example forks into it:
// a new session loads the example and shows what it defines, then runs the
// transcript's entries (see examples.mjs).
document.addEventListener("cubist-repl-fork", async ({ detail: { base, inputs, label } }) => {
  setOpen(true);
  await repl.restart();
  if (base) {
    repl.show({ kind: "info", text: label });
    await repl.load(base);
  }
  for (const input of inputs) await repl.enter(input);
  repl.focus();
});
