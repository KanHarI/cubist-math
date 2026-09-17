#!/usr/bin/env node
import { createInterface } from "node:readline";
import { readFile, writeFile, stat } from "node:fs/promises";
import createKernel from "../web/dist/kernel.mjs";
import { Session } from "../web/session.mjs";
import {
  layout,
  selectedText,
  pathFromNames,
  pathFromMarked,
  atPath,
  roles,
} from "../web/expressions.mjs";
const module = await createKernel();
const session = new Session(module);
let active = null,
  selection = null,
  token = null;
const input = createInterface({
  input: process.stdin,
  output: process.stdout,
  terminal: !!process.stdin.isTTY,
  completer: (line) => {
    const word = line.split(/\s+/).at(-1);
    const choices = [
      "help",
      "demo",
      "list",
      "use",
      "show",
      "select",
      "parent",
      "children",
      "down",
      "reduce",
      "pass",
      "unfold",
      "rewrite",
      "preview",
      "accept",
      "reject",
      "undo",
      "history",
      "goto",
      "check",
      "source",
      "stats",
      "ops",
      "save",
      "load",
      "run",
      "axioms",
      "quit",
      ...session.engine.bindings.keys(),
      "expr",
      "type",
      "expr.argument",
      "expr.function",
      "type.domain",
      "type.codomain",
    ];
    return [choices.filter((x) => x.startsWith(word)), word];
  },
});
const say = (s) => process.stdout.write(s + "\n");
function show(name = active) {
  if (!name) throw new Error("Choose a judgement with use NAME.");
  active = name;
  const v = session.inspect(name);
  say(`${name} [${v.kind}]`);
  if (v.expression)
    say(
      "  expr: " +
        (selection?.name === name && selection.side === "expression"
          ? selectedText(v.expression, selection.path, v.contextNames)
          : layout(v.expression, v.contextNames).text),
    );
  say(
    "  type: " +
      (selection?.name === name && selection.side === "type"
        ? selectedText(v.type, selection.path, v.contextNames)
        : layout(v.type, v.contextNames).text),
  );
  say(
    "  assumptions: " +
      (v.assumptions.map((c) => c.names.join("/") || `c${c.id}`).join(", ") ||
        "none"),
  );
}
function preview(p) {
  token = p.token;
  say("PREVIEW (live proof unchanged)");
  say(p.source);
  say(
    "  result: " +
      layout(p.result.expression || p.result.type, p.result.contextNames).text,
  );
  say("  type: " + layout(p.result.type, p.result.contextNames).text);
  say("accept / reject");
}
const help = `demo                         Load the identity example into an empty session
list                         List mathematical objects
use NAME / show [NAME]        Inspect an object
select expr.argument         Select by mathematical role or numeric path
select type.1                Select part of its type
select expr --paren TEXT     Copy expr, adding ONE extra pair of parentheses
select type --paren TEXT     The same for the type; [[ ]] also works
parent / children / down N   Navigate the selected subtree directly
reduce [RESULT]               Preview one reduction at the selection
pass [RESULT]                 Preview one recursive reduction pass
unfold [RESULT]               Preview definition-enabled pointed reduction
rewrite WITNESS [RESULT]      Preview substitution within the selection
preview NAME = OP(...)       Preview any named kernel instruction(s)
accept / reject              Commit or discard the pending preview
undo / history / goto ID     Replay an earlier revision; branches are retained
check PROPOSITION PROOF      Check the closed theorem against its proof
source / stats / ops          Show instructions, metrics, or all 67 operations
save FILE / load FILE        Save or replay the active proof branch as JSON
run FILE.math               Preview a source program before accepting it
axioms on / axioms off       Explicitly change the axiom policy
help / quit`;
async function command(line) {
  const text = line.trim();
  if (!text || text.startsWith("#")) return;
  const [cmd, ...words] = text.split(/\s+/);
  const rest = text.slice(cmd.length).trim();
  switch (cmd) {
    case "help":
      say(help);
      break;
    case "demo":
      if (session.program().length)
        throw new Error("Demo requires an empty session (goto 0).");
      session.loadDemo();
      active = "nested";
      selection = { name: active, side: "expression", path: [1] };
      show();
      break;
    case "list":
      for (const b of session.snapshot().bindings.filter((b) => !b.hidden))
        say(`${b.name.padEnd(20)} ${b.kind}`);
      break;
    case "use":
      active = rest;
      selection = null;
      show();
      break;
    case "show":
      show(rest || active);
      break;
    case "select": {
      if (!active) throw new Error("Use a judgement first.");
      const match = rest.match(
        /^(expr|expression|type)(?:\s+--paren\s+([\s\S]+)|\.([A-Za-z0-9_.]+))?$/,
      );
      if (!match)
        throw new Error(
          "Use select expr.argument or select expr --paren TEXT.",
        );
      const side = match[1] === "type" ? "type" : "expression",
        tree = session.inspect(active)[side];
      if (!tree)
        throw new Error("Contexts have a type, but no term expression.");
      let marked = match[2];
      if (
        marked &&
        ((marked.startsWith('"') && marked.endsWith('"')) ||
          (marked.startsWith("'") && marked.endsWith("'")))
      )
        marked = marked.slice(1, -1);
      const path = marked
        ? pathFromMarked(tree, marked, session.inspect(active).contextNames)
        : pathFromNames(tree, match[3]?.split(".") || []);
      selection = { name: active, side, path };
      show();
      break;
    }
    case "children": {
      if (!selection) throw new Error("Select a subtree first.");
      const tree = session.inspect(active)[selection.side],
        n = atPath(tree, selection.path);
      n.children.forEach((child, i) =>
        say(`${i} ${(roles[n.kind] || [])[i] || ""}: ${layout(child).text}`),
      );
      break;
    }
    case "down": {
      if (!selection) throw new Error("Select a subtree first.");
      const n = atPath(session.inspect(active)[selection.side], selection.path);
      selection.path = [...selection.path, ...pathFromNames(n, [rest])];
      show();
      break;
    }
    case "run": {
      if ((await stat(rest)).size > 1000000)
        throw new Error("Source exceeds 1 MB.");
      preview(
        session.previewSource(await readFile(rest, "utf8"), "Source: " + rest),
      );
      break;
    }
    case "parent":
      if (!selection?.path.length)
        throw new Error("Already at the root or nothing selected.");
      selection.path = selection.path.slice(0, -1);
      show();
      break;
    case "reduce":
    case "pass":
    case "unfold":
    case "rewrite": {
      if (!selection) throw new Error("Select an expression first.");
      const operation = {
        reduce: "BetaReducePointed",
        pass: "BetaReduceGrossKnuth",
        unfold: "DefReducePointed",
        rewrite: "HighSubs",
      }[cmd];
      preview(
        session.previewFocus({
          ...selection,
          operation,
          witness: cmd === "rewrite" ? words[0] : undefined,
          resultName: cmd === "rewrite" ? words[1] : words[0],
        }),
      );
      break;
    }
    case "preview":
      preview(session.previewSource(rest));
      break;
    case "accept": {
      const name = session.draft?.steps.at(-1).name;
      session.accept(token);
      token = null;
      active = name;
      selection = null;
      say("ACCEPTED");
      show();
      break;
    }
    case "reject":
      session.discard();
      token = null;
      say("Preview discarded.");
      break;
    case "undo":
      session.undo();
      selection = null;
      active = null;
      token = null;
      say(`Revision ${session.revision}`);
      break;
    case "goto":
      session.checkout(Number(rest));
      selection = null;
      active = null;
      token = null;
      say(`Revision ${session.revision}`);
      break;
    case "history":
      for (const r of session.snapshot().history)
        say(
          `${r.id === session.revision ? "*" : " "} ${r.id} <- ${r.parent ?? "-"} ${r.title}`,
        );
      break;
    case "source":
      say(session.snapshot().source);
      break;
    case "stats":
      say(JSON.stringify(session.engine.stats(), null, 2));
      break;
    case "axioms":
      if (!["on", "off"].includes(rest))
        throw new Error("Use axioms on or axioms off.");
      session.setPolicy(rest === "on");
      token = null;
      say("Axioms " + rest);
      break;
    case "ops":
      for (const m of session.metadata)
        say(
          `${m.name}: ${m.judgements} judgements, ${Number(m.context)} context, ${m.free} optional context slots -> ${m.returnsContext ? "context" : "judgement"}`,
        );
      break;
    case "check":
      say(session.verify(words[0], words[1]) ? "VERIFIED" : "NOT VERIFIED");
      break;
    case "save":
      if (!rest) throw new Error("Specify a filename.");
      await writeFile(rest, JSON.stringify(session.export(), null, 2) + "\n");
      say("Saved " + rest);
      break;
    case "load": {
      if ((await stat(rest)).size > 2000000)
        throw new Error("File exceeds 2 MB.");
      const data = await readFile(rest, "utf8");
      session.import(JSON.parse(data));
      active = null;
      selection = null;
      token = null;
      say("Loaded and checked " + rest);
      break;
    }
    case "quit":
    case "exit":
      input.close();
      break;
    default:
      if (text.includes("=")) preview(session.previewSource(text));
      else throw new Error("Unknown command. Type help.");
  }
}
say("THTH Math • checked WASM kernel • type help or demo");
if (process.stdin.isTTY) (input.setPrompt("math> "), input.prompt());
for await (const line of input) {
  try {
    await command(line);
  } catch (e) {
    say("ERROR: " + e.message);
    if (e.details) say(JSON.stringify(e.details, null, 2));
  }
  if (process.stdin.isTTY) input.prompt();
}
session.dispose();
