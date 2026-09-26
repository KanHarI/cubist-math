// Read the native arena directly. Source names are labels only; they never
// replace handles, payloads, or constructor operands in this listing.
import { cubicalKinds } from "./cubical-kernel.mjs";

export const operandNames = {
  Pi: ["domain", "body"], Lam: ["domain", "body"], Sigma: ["domain", "body"], W: ["domain", "body"],
  App: ["function", "argument"], Pair: ["type", "first", "second"], Fst: ["pair"], Snd: ["pair"], Succ: ["value"],
  NatRec: ["motive", "zero", "step", "value"], Path: ["family", "left", "right"], PLam: ["family", "body"],
  PApp: ["path", "checked annotation"], Comp: ["family", "tubes", "base"], Tube: ["partial term", "next tube"],
  Abort: ["type", "impossible"], Sup: ["W type", "label", "children"], WRec: ["motive", "step", "value"],
  Sum: ["left", "right"], Inl: ["sum type", "value"], Inr: ["sum type", "value"],
  SumRec: ["motive", "left", "right", "value"], UnitRec: ["motive", "point", "value"],
  Glue: ["base", "system"], GlueSystem: ["partial type", "equivalence", "next"],
  GlueTerm: ["Glue type", "base", "tubes"], Unglue: ["Glue type", "value"],
  Pushout: ["center", "left", "right", "maps"], PushLeft: ["pushout", "value"], PushRight: ["pushout", "value"],
  PushPath: ["pushout", "value"], PushElim: ["motive", "left", "right", "bridge"],
  HComp: ["type", "tubes", "base"], Trans: ["family", "face tube", "base"],
};
export const opcodeName = kind => "CC_" + ({ GlueSystem: "GLUE_SYSTEM", GlueTerm: "GLUE_TERM",
  PushLeft: "PUSH_LEFT", PushRight: "PUSH_RIGHT", PushPath: "PUSH_PATH", PushElim: "PUSH_ELIM" }[kind] ?? kind.toUpperCase());

export function kernelAssembly(program, view, checked, { limit = 400, expanded = [], focus = [] } = {}) {
  const kernel = program.kernel, syntax = program.checker.syntax, dimensions = new Map(view.dimensions ?? []);
  const roots = [
    { label: "Expression", handle: checked.expression },
    { label: "Checked type", handle: syntax.encode(view.type, dimensions) },
  ];
  const inferredType = syntax.encode(checked.type, dimensions);
  if (inferredType !== roots[1].handle) roots.push({ label: "Inferred type", handle: inferredType });
  const context = view.context.map(entry => ({ name: entry.name, label: entry.label ?? entry.name,
    symbol: kernel.symbol(entry.name), handle: syntax.encode(entry.type, dimensions) }));
  const queue = [...focus, ...roots.map(root => root.handle), ...context.map(entry => entry.handle)];
  const seen = new Set(), nodes = [], formulas = new Map(), expand = new Set(expanded);
  for (let index = 0; index < queue.length && nodes.length < limit; index++) {
    const id = queue[index]; if (!id || seen.has(id)) continue;
    seen.add(id);
    const native = kernel.node(id), opcode = cubicalKinds.indexOf(native.kind);
    const node = { id, opcode, mnemonic: opcodeName(native.kind), kind: native.kind, payload: native.payload,
      operands: native.children.map((handle, i) => ({ slot: "abcd"[i], label: operandNames[native.kind]?.[i] ?? "unused", handle })) };
    if (["Var", "Pi", "Lam", "Sigma", "W"].includes(native.kind)) {
      const name = kernel.symbolName(native.payload), label = view.symbols[name]?.name;
      node.annotation = `symbol #${native.payload}: ${label && label !== name ? `${label} (${name})` : name}`;
    } else if (["Path", "PLam", "Comp", "HComp", "Trans"].includes(native.kind)) node.annotation = `dimension #${native.payload}`;
    else if (native.kind === "U") node.annotation = `universe level ${native.payload}`;
    else if (["PApp", "PushPath", "Tube", "GlueSystem"].includes(native.kind)) {
      node.formula = native.payload;
      if (!formulas.has(native.payload)) {
        const formula = kernel.inspectFormula(native.payload);
        formulas.set(native.payload, { id: native.payload, sort: formula.sort,
          clauses: formula.clauses.map(([positive, negative]) => ({
            positive: "0x" + positive.toString(16).padStart(16, "0"),
            negative: "0x" + negative.toString(16).padStart(16, "0"),
          })) });
      }
      node.annotation = `${formulas.get(native.payload).sort} formula @${native.payload}`;
    } else if (native.kind === "DefRef") {
      node.definition = kernel.definition(id);
      node.annotation = view.symbols[node.definition.name]?.name ?? node.definition.name;
      if (node.annotation !== node.definition.name) node.annotation += ` (${node.definition.name})`;
      node.annotation += ` · registry #${native.payload}`;
      if (expand.has(id)) queue.push(node.definition.value, node.definition.type);
    }
    nodes.push(node); queue.push(...native.children.filter(Boolean));
  }
  return { roots, context, specialization: view.expression.tag === "Var" && view.expression.name === view.specialization?.binding ? view.specialization : null, dimensions: [...dimensions], nodes, formulas: [...formulas.values()],
    pending: new Set(queue.filter(id => id && !seen.has(id))).size };
}

export function assemblyText(listing) {
  const lines = ["; Cubical C native term arena — handles are local to this replay session.",
    ...listing.roots.map(root => `; ${root.label}: %${root.handle}`),
    ...listing.context.map(entry => `; Context #${entry.symbol} ${entry.label} (${entry.name}) : %${entry.handle}`),
    ...listing.dimensions.map(([name, slot]) => `; Interval ${name}: dimension #${slot}`), ""];
  if (listing.specialization) {
    const origin = listing.specialization;
    lines.push(`; Elaborator specialization: ${origin.schema}(U), U := ${origin.universe}.`,
      `; The resulting ${origin.schema}(${origin.universe}) is an explicit context assumption (CC_VAR).`,
      "; No universe-generic kernel term or CC_APP for the universe argument is claimed.", "");
  }
  for (const node of listing.nodes) {
    lines.push(`%${node.id} = ${node.mnemonic} [${node.opcode}] payload=${node.payload} `
      + node.operands.map(operand => `${operand.slot}=${operand.handle ? "%" + operand.handle : "0"}`).join(" ")
      + (node.annotation ? ` ; ${node.annotation}` : ""));
    if (node.definition) lines.push(`;   definition body=%${node.definition.value} type=%${node.definition.type}`);
  }
  for (const formula of listing.formulas) lines.push(`@${formula.id} ${formula.sort} `
    + (formula.clauses.map(c => `(+${c.positive}, -${c.negative})`).join(" OR ") || "0 (no clauses)"));
  if (listing.pending) lines.push(`; Partial listing: ${listing.pending} discovered nodes remain to be shown.`);
  return lines.join("\n") + "\n";
}

export function renderAssembly(container, listing, { jump, expand, inspect }) {
  const doc = container.ownerDocument;
  const el = (tag, text, className) => {
    const node = doc.createElement(tag); if (text !== undefined) node.textContent = text;
    if (className) node.className = className; return node;
  };
  const reference = id => {
    if (!id) return doc.createTextNode("0");
    const button = el("button", `%${id}`, "assembly-reference");
    button.dataset.handle = String(id); button.onclick = () => jump(id); return button;
  };
  container.replaceChildren();
  const roots = el("div", undefined, "assembly-roots");
  for (const root of listing.roots) { const row = el("div", `${root.label}: `); row.append(reference(root.handle)); roots.append(row); }
  for (const entry of listing.context) {
    const row = el("div", `Context #${entry.symbol} ${entry.label} (${entry.name}) : `);
    row.append(reference(entry.handle)); roots.append(row);
  }
  if (!listing.context.length) roots.append(el("div", "Empty context"));
  for (const [name, slot] of listing.dimensions) roots.append(el("div", `Interval ${name}: dimension #${slot}`));
  container.append(roots);
  const scroll = el("div", undefined, "assembly-scroll"), table = el("table", undefined, "assembly-table");
  const head = el("thead"), headings = el("tr");
  for (const title of ["Handle", "Opcode", "Payload", "Operands", "Meaning / source name"]) headings.append(el("th", title));
  head.append(headings); table.append(head);
  const body = el("tbody");
  for (const node of listing.nodes) {
    const row = el("tr"); row.id = `assembly-node-${node.id}`; row.tabIndex = -1;
    row.dataset.opcode = node.mnemonic;
    row.append(el("td", `%${node.id}`), el("td", `${node.mnemonic} [${node.opcode}]`), el("td", String(node.payload)));
    const operands = el("td");
    for (const operand of node.operands) {
      const line = el("div", `${operand.slot} (${operand.label}) = `); line.append(reference(operand.handle)); operands.append(line);
    }
    const annotation = el("td", node.annotation ?? "");
    if (node.definition) {
      const actions = el("div", undefined, "assembly-definition-actions");
      const open = el("button", "Show body and type"); open.dataset.expandDefinition = String(node.id);
      open.onclick = () => expand(node.id, node.definition.value); actions.append(open);
      const named = el("button", "Inspect definition"); named.onclick = () => inspect(node.definition.name); actions.append(named);
      annotation.append(actions);
      const bodyLink = el("div", "body = "); bodyLink.append(reference(node.definition.value));
      const typeLink = el("div", "type = "); typeLink.append(reference(node.definition.type)); annotation.append(bodyLink, typeLink);
    }
    row.append(operands, annotation); body.append(row);
  }
  table.append(body); scroll.append(table); container.append(scroll);
  if (listing.formulas.length) {
    container.append(el("h3", "Interval and face formulas"));
    const pre = el("pre", listing.formulas.map(formula => `@${formula.id} ${formula.sort}: `
      + (formula.clauses.map(c => `(+${c.positive}, -${c.negative})`).join(" OR ") || "0 (no clauses)")).join("\n"));
    container.append(pre, el("p", "Each clause stores positive and negative 64-bit dimension masks. Clauses are joined by OR.", "hint"));
  }
}
