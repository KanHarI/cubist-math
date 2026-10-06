import { createReplConsole, standaloneRepl } from "./repl-console.mjs";

// The REPL page starts from an empty program.
createReplConsole(document.getElementById("repl"), {
  ...standaloneRepl(),
  greeting: ["Each entry is checked by the kernel. Try: import nat;  use nat;  let x := 7;  typeof x;  evaluate x + 3;"],
}).focus();
