// The elaboration of each declaration of a checked module, step by step: its
// source, its type, each proof statement with the goal it faced and the term
// it built, the finished term, and the kernel's term and checked type as
// trees of native opcodes. The reference's Elaboration panels show it.
import { operandNames, opcodeName } from "./cubical-assembly.mjs";

const leaves = new Set(["U", "Var", "DefRef", "Nat", "Zero", "Unit", "Point", "Void"]);
const binders = new Set(["Pi", "Lam", "Sigma", "W"]);
// Operands that need no label: a binder's body, and an application's parts.
const unlabeled = { Pi: [1], Lam: [1], Sigma: [1], W: [1], App: [0, 1], Succ: [0] };
// Generated names show their stem: n for n11, x for native69.
const stem = name => /^native\d+$/.test(name) ? "x" : name.replace(/\d+$/, "") || name;

// A native term as indented lines, `CC_LAM n : CC_NAT` over its body. Small
// subterms stay on one line; definitions are leaves, shown by name.
export function opcodeTree(kernel, handle, { names = {}, limit = 300 } = {}) {
  const lines = [];
  let budget = limit;
  const label = native => {
    if (["Var", ...binders].includes(native.kind)) return stem(kernel.symbolName(native.payload));
    if (native.kind === "DefRef") {
      const name = kernel.definition(native.id).name;
      return names[name]?.name ?? name.slice(name.indexOf("__") + 2);
    }
    if (native.kind === "U") return String(native.payload);
    return "";
  };
  const operands = native => (operandNames[native.kind] ?? []).map((name, index) => ({ name, index, handle: native.children[index] }))
    .filter(operand => operand.handle);
  // One line for a leaf, or a node of leaves, when it is short.
  const inline = (handle, depth = 0) => {
    const native = kernel.node(handle), head = [opcodeName(native.kind), label(native)].filter(Boolean).join(" ");
    if (leaves.has(native.kind)) return head;
    if (depth > 1 || binders.has(native.kind) || !["App", "Succ"].includes(native.kind)) return null;
    const parts = operands(native).map(operand => inline(operand.handle, depth + 1));
    if (parts.some(part => part === null)) return null;
    const text = `${head} ${parts.map(part => part.includes(" ") ? `(${part})` : part).join(" ")}`;
    return text.length <= 56 ? text : null;
  };
  const walk = (handle, depth, prefix) => {
    if (--budget < 0) { if (budget === -1) lines.push({ depth, text: "…" }); return; }
    const short = inline(handle);
    if (short) { lines.push({ depth, text: prefix + short }); return; }
    const native = kernel.node(handle);
    let head = [opcodeName(native.kind), label(native)].filter(Boolean).join(" ");
    const children = operands(native);
    // A binder's domain, when short, follows its name: CC_LAM n : CC_NAT.
    if (binders.has(native.kind) && children[0]) {
      const domain = inline(children[0].handle);
      if (domain) { head += ` : ${domain}`; children.shift(); }
    }
    lines.push({ depth, text: prefix + head });
    for (const operand of children)
      walk(operand.handle, depth + 1, unlabeled[native.kind]?.includes(operand.index) ? "" : `${operand.name}: `);
  };
  walk(handle, 0, "");
  return lines;
}

// What each rule checks, for the step-by-step kernel view.
const rules = {
  Lam: "function: check the domain is a type, extend the context, infer the body",
  Pi: "function type: the domain and the body are types",
  Sigma: "pair type: both components are types",
  App: "application: the function's type is a Π; check the argument against its domain",
  Pair: "pair: check each component against the pair type",
  Var: "variable: its type is in the context",
  DefRef: "definition: its type was checked when it was defined",
  U: "universe: U(n) has type U(n+1)",
  Nat: "natural numbers", Zero: "zero", Succ: "successor of a natural number",
  Path: "path type: both endpoints have the family's type",
  PLam: "path: check the body at every point of the interval",
  NatRec: "recursion on a natural number", SumRec: "case analysis on a sum",
};

// The kernel's check of a declaration, step by step: each rule it applied to
// a node, with the type it found, and the context extensions, conversions and
// reductions inside. Check reuse is off, so every node is checked.
export function kernelDerivation(program, view, { limit = 400 } = {}) {
  const kernel = program.kernel, checker = program.checker, dimensions = new Map(view.dimensions ?? []);
  const context = view.context.map(entry => [entry.name, entry.type]);
  const saved = kernel.optimizations ?? { shareSyntax: true, reuseChecks: true, compactPaths: true };
  kernel.setOptimizations({ ...saved, reuseChecks: false });
  let traced;
  try { traced = kernel.traced(() => checker.syntax.check(view.expression, view.type, context, dimensions)); }
  finally { kernel.setOptimizations(saved); }
  const shown = handle => { try { return checker.displayText(checker.syntax.decode(handle, dimensions), 160); } catch { return `%${handle}`; } };
  const lines = [], open = [];
  let rulesApplied = 0;
  for (const event of traced.events) {
    if (lines.length >= limit) break;
    if (event.kind === "infer") {
      rulesApplied++;
      const kind = kernel.node(event.a).kind;
      const line = { depth: event.depth, kind: "rule", text: nodeSummary(kernel, event.a, view.symbols), note: rules[kind] ?? "" };
      lines.push(line);
      open.push(line);
    } else if (event.kind === "inferred") {
      const line = open.pop();
      if (line) line.result = event.c ? shown(event.c) : "rejected";
    } else if (event.kind === "reused")
      lines.push({ depth: event.depth, kind: "rule", text: nodeSummary(kernel, event.a, view.symbols), result: shown(event.c), note: "already checked" });
    else if (event.kind === "extend")
      lines.push({ depth: event.depth, kind: "extend", text: `${stem(kernel.symbolName(event.a))} : ${shown(event.b)}` });
    else if (event.kind === "convert")
      lines.push({ depth: event.depth, kind: "convert", text: `${shown(event.a)} ≡ ${shown(event.b)}`, result: event.c ? "equal" : "different" });
    else if (event.kind === "reduce")
      lines.push({ depth: event.depth, kind: "reduce", text: `${shown(event.a)} ⟶ ${shown(event.b)}` });
  }
  return { lines, rulesApplied, truncated: lines.length >= limit || traced.dropped > 0 };
}

// One node: its opcode and name, or the whole node when it is short.
function nodeSummary(kernel, handle, names = {}) {
  const [line] = opcodeTree(kernel, handle, { names, limit: 1 });
  return line.text;
}

// Every declaration of `module`, in source order.
export function elaboration(program, module) {
  const source = program.sources[module] ?? "";
  const declarations = Object.values(program.symbols)
    .filter(info => info.binding?.startsWith(`${module}__`) && Number.isInteger(info.start))
    .sort((a, b) => a.start - b.start);
  return declarations.map(info => {
    const result = { name: info.name, source: source.slice(info.start, info.end), verified: !!info.verified };
    if (!info.verified) return { ...result, reason: info.reason };
    const steps = program.steps(module, info.name).map(step => ({ ...step, text: source.slice(step.start, step.end) }));
    try {
      const view = program.inspect(info.binding), checker = program.checker, dimensions = new Map(view.dimensions ?? []);
      const checked = checker.syntax.check(view.expression, view.type, view.context.map(entry => [entry.name, entry.type]), dimensions);
      const names = view.symbols ?? {};
      return { ...result, steps,
        type: checker.displayText(view.type, 600), term: checker.displayText(view.expression, 600),
        kernelTerm: opcodeTree(program.kernel, checked.expression, { names }),
        kernelType: opcodeTree(program.kernel, checker.syntax.encode(view.type, dimensions), { names }),
        checkingSteps: checked.checkingSteps, derivation: kernelDerivation(program, view) };
    } catch (error) {
      return { ...result, steps, reason: error.message };
    }
  });
}
