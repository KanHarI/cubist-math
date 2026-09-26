// The workbench's kernel graph: the judgement graph of a checked view, as the
// instruction kernel derives it, with the premises and consumers of each
// judgement, its context entries, and each step's highlighted subterm. Term
// and type handles lead into the syntax graph (the assembly view).
import { cubicalText } from "./cubical-notation.mjs";
import { InstructionDriver } from "./cubical-instruction-driver.mjs";
import { ththNames } from "./cubical-instructions.mjs";

export function judgementGraph(program, view, checked, { limit = 1500 } = {}) {
  const kernel = program.kernel, checker = program.checker, dimensions = new Map(view.dimensions ?? []);
  const driver = new InstructionDriver(kernel), graph = driver.graph;
  const encode = term => checker.syntax.encode(term, dimensions);
  const decode = handle => checker.syntax.decode(handle, dimensions);
  const context = view.context.map(entry => [kernel.symbol(entry.name), encode(entry.type)]);
  const root = driver.check(checked.expression, encode(view.type), context);

  // Every judgement the conclusion rests on, through premises and the
  // judgements that justify its context entries, in the order derived.
  const judgements = new Map(), entries = new Map(), stack = [root];
  while (stack.length && judgements.size < limit) {
    const id = stack.pop();
    if (judgements.has(id)) continue;
    const judgement = graph.judgement(id);
    judgements.set(id, judgement);
    stack.push(...judgement.premises);
    for (const entry of [...judgement.context, judgement.entry].filter(Boolean)) {
      if (entries.has(entry)) continue;
      const info = graph.entry(entry);
      entries.set(entry, info);
      if (info.source) stack.push(info.source);
    }
  }
  const ids = [...judgements.keys()].sort((a, b) => a - b);
  const number = new Map(ids.map((id, index) => [id, index + 1]));
  const usedBy = new Map(ids.map(id => [id, []]));
  for (const id of ids) for (const premise of judgements.get(id).premises) usedBy.get(premise)?.push(number.get(id));
  for (const info of entries.values()) info.sourceNumber = number.get(info.source);

  // Terms in mathematical notation over the judgement's context, written
  // {x : A, …}; one renaming keeps the names in agreement. Each entry is
  // shown under the name it first appears with.
  const shownNames = new Map();
  const text = (judgement, first, second = null) => {
    const scope = new Map(), terms = [];
    for (const entry of judgement.context) {
      const info = entries.get(entry);
      if (!info.dimension) { scope.set(info.name, decode(info.type)); terms.push(entry); }
    }
    const shown = checker.displayGoal(scope, decode(first), second ? decode(second) : null, 240, cubicalText, false);
    terms.forEach((entry, index) => { if (!shownNames.has(entry)) shownNames.set(entry, shown.locals[index]?.name); });
    const names = judgement.context.map(entry => {
      const info = entries.get(entry), index = terms.indexOf(entry);
      return info.dimension ? `${info.name} : 𝕀` : `${shown.locals[index]?.name ?? info.name} : ${shown.locals[index]?.type ?? "…"}`;
    });
    return { scope: `{${names.join(", ")}}`, first: shown.goal, second: shown.built };
  };
  const rows = ids.map(id => {
    const j = judgements.get(id);
    const typing = text(j, j.type, j.term);
    const statement = j.kind === "typing" ? `${typing.scope} ⊢ ${typing.second} : ${typing.first}`
      : `${typing.scope} ⊢ ${typing.second} ≡ ${text(j, j.type, j.other).second} : ${typing.first}`;
    const row = { id, number: number.get(id), rule: j.rule, label: ththNames[j.rule] ?? j.rule, statement,
      premises: j.premises.map(premise => number.get(premise)), usedBy: usedBy.get(id),
      entry: j.entry ? entries.get(j.entry) : null, context: j.context.map(entry => entries.get(entry)),
      term: j.term, type: j.type, other: j.other ?? null };
    if (j.rule === "step" || j.rule === "replace") {
      // The highlighted subterm, on the side of the premise it rewrote.
      const premise = judgements.get(j.premises[0]);
      let handle = premise[j.side === "term" ? "term" : j.side === "other" ? "other" : "type"];
      for (const child of j.position) handle = kernel.node(handle).children[child];
      row.highlight = { side: j.side, position: j.position, rule: j.stepRule ?? "replace", text: text(premise, handle).first };
    }
    return row;
  });
  for (const info of entries.values()) info.shown = info.dimension ? info.name : shownNames.get(info.id) ?? info.name;
  for (const row of rows) if (row.entry) row.entry = entries.get(row.entry.id);
  return { root: number.get(root), rows, truncated: stack.length > 0,
    entries: [...entries.values()].sort((a, b) => a.id - b.id) };
}

export function renderJudgementGraph(container, listing, { jumpNode } = {}) {
  const make = (tag, className, text) => {
    const element = document.createElement(tag);
    if (className) element.className = className;
    if (text !== undefined) element.textContent = text;
    return element;
  };
  const link = number => {
    const button = make("button", "graph-link", `#${number}`);
    button.type = "button";
    button.onclick = () => jump(number);
    return button;
  };
  const jump = number => {
    container.querySelectorAll(".graph-row.selected").forEach(row => row.classList.remove("selected"));
    const row = container.querySelector(`#judgement-${number}`);
    row?.classList.add("selected");
    row?.scrollIntoView({ block: "nearest" });
  };
  const links = (label, numbers) => {
    const span = make("span", "graph-links");
    if (!numbers.length) return span;
    span.append(`${label} `);
    numbers.forEach((number, index) => { if (index) span.append(" "); span.append(link(number)); });
    return span;
  };
  const list = make("ol", "graph-listing");
  for (const row of listing.rows) {
    const item = make("li", "graph-row");
    item.id = `judgement-${row.number}`;
    if (row.number === listing.root) item.classList.add("graph-root");
    const head = make("div", "graph-head");
    head.append(make("span", "graph-number", `${row.number}`), make("span", "graph-rule", row.label));
    head.append(links("from", row.premises));
    if (row.entry) head.append(make("span", "graph-entry", `${row.rule === "variable" ? "uses" : "binds"} ${row.entry.shown}`));
    item.append(head, make("div", "graph-statement", row.statement));
    if (row.highlight) {
      const where = row.highlight.position.length ? `[${row.highlight.position.join(", ")}]` : "the root";
      item.append(make("div", "graph-highlight", `${row.highlight.rule} on the ${row.highlight.side} at ${where}: ${row.highlight.text}`));
    }
    const foot = make("div", "graph-foot");
    foot.append(links("used by", row.usedBy));
    if (jumpNode) {
      for (const [label, handle] of [["term", row.term], ["other", row.other], ["type", row.type]]) {
        if (!handle) continue;
        const button = make("button", "graph-node", `${label} %${handle}`);
        button.type = "button";
        button.title = "Show this node in the kernel assembly (the syntax graph)";
        button.onclick = () => jumpNode(handle);
        foot.append(button);
      }
    }
    item.append(foot);
    list.append(item);
  }
  const entries = make("div", "graph-entries");
  entries.append(make("h3", null, "Context entries"));
  const table = make("ul", "graph-entry-list");
  for (const entry of listing.entries) {
    const item = make("li", null, entry.dimension ? `${entry.shown} : 𝕀, an interval dimension` : `${entry.shown}, of the type derived at `);
    if (!entry.dimension && entry.sourceNumber) item.append(link(entry.sourceNumber));
    table.append(item);
  }
  entries.append(table);
  container.replaceChildren(list, ...(listing.entries.length ? [entries] : []));
  return { jump };
}
