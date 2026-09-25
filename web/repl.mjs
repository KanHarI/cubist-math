import { createReplConsole, standaloneRepl } from "./repl-console.mjs";

// The REPL page starts from an empty program.
createReplConsole(document.getElementById("repl"), {
  ...standaloneRepl(),
  greeting: ["Each entry is checked by the kernel. Try: let x := 7;  typeof x;  evaluate x;  or  import naturals;  then  evaluate 2 + 3;"],
}).focus();
