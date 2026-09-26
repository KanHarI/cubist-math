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
        checkingSteps: checked.checkingSteps };
    } catch (error) {
      return { ...result, steps, reason: error.message };
    }
  });
}
