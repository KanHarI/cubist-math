import { kernelBinderCount } from "./expressions.mjs";
import { axiomLabels } from "./axiom-labels.mjs";
const mathNamespace = "http://www.w3.org/1998/Math/MathML";

// Read only actual checked AST constructors. Names annotate definition nodes;
// binder labels are cosmetic. The upstream kernel counts a binder in *both*
// children of Pi/Sigma, including the domain (see src/kernel/ast.c).
export function kernelMathTree(tree, references = {}, contextNames = {}, contextReferences = {}, declarations = {}, axiomNotation = {}) {
  const usesBinder = (node, depth = 0) => node.kind === "VRef" ? node.parameter === depth
    : node.children.some(child => usesBinder(child, depth + kernelBinderCount(node.kind)));
  // The current Pi/Sigma owns slot 0 even in its domain. Positive free
  // indices in that domain refer to preceding binders; inner constructors
  // contribute their own slots before those references are interpreted.
  function domainMetadata(domain, env) {
    const dependencies = new Set(), freeNames = new Set();
    const outerDepth = env.length;
    let complete = true;
    function key(node, depth = 0) {
      if (node.truncated) { complete = false; return null; }
      if (node.kind === "VRef") {
        const preceding = node.parameter - depth;
        if (preceding > 0) {
          dependencies.add(preceding);
          if (env[preceding - 1]) freeNames.add(env[preceding - 1]);
        }
        return preceding < 0 ? ["inner", node.parameter] : ["outer", outerDepth - preceding];
      }
      if (["CRef", "UCRef"].includes(node.kind) && contextNames[node.parameter]) freeNames.add(contextNames[node.parameter]);
      if (node.kind === "DRef" && references[node.id]?.name) freeNames.add(references[node.id].name);
      return [node.kind, node.parameter, ...node.children.map(child => key(child, depth + kernelBinderCount(node.kind)))];
    }
    const canonical = key(domain);
    return { domainDependencies: complete ? [...dependencies] : null, domainFreeNames: complete ? [...freeNames] : null,
      domainKey: complete ? JSON.stringify(canonical) : null };
  }
  const named = name => ({ kind: "Name", name });
  function visit(node, env = []) {
    if (node.truncated) return named("…");
    if (node.kind === "DRef" && references[node.id]) return { kind: "Name", ...references[node.id] };
    if (node.kind === "Axiom") {
      const binding = declarations[node.id];
      return { kind: "Name", name: axiomNotation[node.id] === "truncation" ? "TruncateAt"
        : binding ? axiomLabels[binding] ?? binding : "axiom",
        axiomParameter: node.parameter, ...(binding ? { binding } : {}),
        ...(axiomNotation[node.id] ? { axiomNotation: axiomNotation[node.id] } : {}) };
    }
    if (node.kind === "U") return { kind: "Universe", level: node.parameter };
    if (node.kind === "VRef") return { kind: "Name", name: env[node.parameter] ?? `#${node.parameter | 0}`, local: true };
    if (["CRef", "UCRef"].includes(node.kind)) return { kind: "Name", name: contextNames[node.parameter] ?? `c${node.parameter}`, local: true,
      ...(contextReferences[node.parameter] ? { contextId: node.parameter, contextBinding: contextReferences[node.parameter].binding } : {}) };
    if (["Nat", "Unit", "Void"].includes(node.kind)) return named(node.kind);
    if (node.kind === "ZN") return { kind: "Number", value: 0 };
    if (node.kind === "SN") {
      const predecessor = visit(node.children[0], env);
      return predecessor.kind === "Number" ? { kind: "Number", value: predecessor.value + 1 }
        : { kind: "Call", fn: named("succ"), args: [predecessor] };
    }
    if (node.kind === "Singleton") return named("⋆");
    if (node.kind === "Refl") return { kind: "Call", fn: named("refl"), args: [visit(node.children[0], env)] };
    if (node.kind === "DRef") return named(`def${node.parameter}`);
    if (["Pi", "Sigma"].includes(node.kind)) {
      const name = node.binderName && node.binderName !== "_" ? node.binderName : `x${env.length}`;
      const extended = [name, ...env];
      const domain = visit(node.children[0], extended), body = visit(node.children[1], extended);
      return node.binderName === "_" && !usesBinder(node.children[1])
        ? { kind: node.kind === "Pi" ? "Arrow" : "Product", left: domain, right: body }
        : { kind: node.kind, name, domain, body, ...domainMetadata(node.children[0], env) };
    }
    if (node.kind === "Lambda") {
      const name = node.binderName ?? `x${env.length}`;
      return { kind: "Lambda", name, body: visit(node.children[0], [name, ...env]) };
    }
    if (node.kind === "Ap") {
      const args = [];
      let fn = node;
      while (fn.kind === "Ap") { args.unshift(visit(fn.children[1], env)); fn = fn.children[0]; }
      return { kind: "Call", fn: visit(fn, env), args };
    }
    if (node.kind === "Eq") return { kind: "Identity", carrier: visit(node.children[0], env),
      left: visit(node.children[1], env), right: visit(node.children[2], env) };
    if (["Tuple", "Sum", "DefEq"].includes(node.kind)) return { kind: { Tuple: "Pair", Sum: "Sum", DefEq: "DefEq" }[node.kind],
      left: visit(node.children[0], env), right: visit(node.children[1], env) };
    const extra = Array.from({ length: kernelBinderCount(node.kind) }, (_, i) => node.binderNames?.[i] ?? `x${env.length + i}`);
    if (node.kind === "IndNat") return { kind: "NatElim", names: extra,
      args: node.children.map(child => visit(child, [...extra].reverse().concat(env))) };
    const call = { kind: "Call", fn: named(node.kind), args: node.children.map(child => visit(child, [...extra].reverse().concat(env))) };
    return extra.length ? { kind: "Scope", names: extra, body: call } : call;
  }
  return visit(tree);
}

// This is shorthand for an unchanged ordered sequence of Pi/Sigma binders,
// not a replacement of its domain by a product type.
export function independentBinderGroups(tree, enabled = true) {
  const groups = [];
  let tail = tree;
  while (["Pi", "Sigma"].includes(tail.kind)) {
    const group = groups.at(-1);
    const independent = enabled && group && group[0].kind === tail.kind
      && !group.some(binder => binder.name === tail.name)
      && group.every(binder => Array.isArray(binder.domainDependencies))
      && !group.some(binder => tail.domainFreeNames?.includes(binder.name) || binder.domainFreeNames?.includes(tail.name))
      && Array.isArray(tail.domainDependencies)
      && !tail.domainDependencies.some(distance => distance >= 1 && distance <= group.length);
    if (independent) group.push(tail);
    else groups.push([tail]);
    tail = tail.body;
  }
  return { groups, tail };
}

export function isTruncationApplication(node) {
  return node.kind === "Call" && node.fn.kind === "Name" && node.fn.axiomNotation === "truncation"
    && ((node.fn.axiomParameter !== undefined && node.args.length === 2)
      || (node.fn.truncationArgument === 0 && node.args.length === 1));
}

// Native MathML provides mathematical typesetting without a CDN, TeX input,
// HTML interpolation, or a change to the stored proof.
export function renderMathNotation(container, tree, { resolve = () => null, inspect = () => {}, truncationSugar = false, groupIndependentBinders = false, identitySugar = true } = {}) {
  const doc = container.ownerDocument;
  const element = (tag, ...children) => {
    const node = doc.createElementNS(mathNamespace, tag);
    for (const child of children) node.append(typeof child === "string" ? doc.createTextNode(child) : child);
    return node;
  };
  const row = (...children) => element("mrow", ...children);
  const operator = text => element("mo", text);
  const fenced = node => row(operator("("), node, operator(")"));
  function reference(symbol, node) {
    const target = node.contextBinding ? resolve(node.contextBinding)
      : node.binding && !node.local ? resolve(node.binding) : null;
    if (target) {
      symbol.dataset.name = node.name;
      if (node.contextBinding) symbol.dataset.contextId = node.contextId;
      if (node.axiomParameter !== undefined) symbol.dataset.axiom = node.binding;
      symbol.setAttribute("class", "math-reference");
      symbol.setAttribute("role", "button");
      symbol.setAttribute("tabindex", "0");
      symbol.setAttribute("aria-label", `Inspect ${node.name}`);
      symbol.setAttribute("title", node.axiomParameter !== undefined
        ? `Axiom ${node.axiomParameter}: ${node.binding}. Inspect its checked type and source`
        : node.contextBinding
        ? `Inspect context assumption ${node.name} and view its source`
        : `Inspect ${node.name} and view its source`);
      symbol.addEventListener("click", () => inspect(target));
      symbol.addEventListener("keydown", event => {
        if (event.key === "Enter" || event.key === " ") { event.preventDefault(); inspect(target); }
      });
    }
    return symbol;
  }
  function binderPrefix(group) {
    const symbol = operator(group[0].kind === "Pi" ? "Π" : "Σ");
    if (group.length === 1) {
      const binder = group[0];
      return element("msub", symbol, row(element("mi", binder.name), operator(":"), visit(binder.domain)));
    }
    const labels = [];
    for (let i = 0; i < group.length;) {
      if (i) labels.push(operator(";"));
      const binder = group[i++];
      labels.push(element("mi", binder.name));
      while (i < group.length && binder.domainKey !== null && binder.domainKey === group[i].domainKey)
        labels.push(operator(","), element("mi", group[i++].name));
      labels.push(operator(":"), visit(binder.domain));
    }
    const prefix = row(symbol, fenced(row(...labels)), operator("."));
    prefix.dataset.binderGroup = group.map(binder => binder.name).join(",");
    prefix.setAttribute("title", "Shorthand for these consecutive independent binders, in the displayed order");
    return prefix;
  }
  function visit(node) {
    if (node.kind === "Name") {
      const symbol = element("mi", node.name);
      if (!node.local) symbol.setAttribute("mathvariant", "normal");
      reference(symbol, node);
      return node.axiomParameter === undefined ? symbol
        : element("msub", symbol, element("mtext", `Axiom ${node.axiomParameter}`));
    }
    if (node.kind === "Universe") return element("msub", element("mi", "𝒰"), element("mn", String(node.level)));
    if (node.kind === "NatElim") {
      const scope = row(operator("["), element("mi", node.names[0]), operator(","), element("mi", node.names[1]), operator("]"));
      return row(element("msub", element("mi", "nat.elim"), scope),
        fenced(row(visit(node.args[0]), operator(","), visit(node.args[1]), operator(","), visit(node.args[2]))));
    }
    if (node.kind === "Scope") return row(operator("["), element("mtext", node.names.join(", ")), operator("]"), operator("."), visit(node.body));
    if (node.kind === "Number") return element("mn", String(node.value));
    if (["Pi", "Sigma", "Lambda"].includes(node.kind)) {
      if (node.kind === "Lambda") return row(operator("λ"), node.domain
        ? fenced(row(element("mi", node.name), operator(":"), visit(node.domain))) : element("mi", node.name), operator("."), visit(node.body));
      const group = independentBinderGroups(node, groupIndependentBinders).groups[0];
      const tail = group.at(-1).body, body = visit(tail);
      const space = element("mspace"); space.setAttribute("width", "0.3em");
      return row(binderPrefix(group), space,
        ["Product", "Sum", "Arrow", "Equality"].includes(tail.kind) ? fenced(body) : body);
    }
    if (node.kind === "Call") {
      if (truncationSugar && isTruncationApplication(node)) {
        const formula = row(reference(operator("‖"), node.fn), visit(node.args[node.fn.truncationArgument ?? 1]), reference(operator("‖"), node.fn));
        formula.dataset.truncationSugar = "true";
        return formula;
      }
      const args = [];
      node.args.forEach((arg, i) => { if (i) args.push(operator(",")); args.push(visit(arg)); });
      const fn = visit(node.fn);
      return row(["Name", "Call"].includes(node.fn.kind) ? fn : fenced(fn), fenced(row(...args)));
    }
    if (node.kind === "Pair") return row(operator("⟨"), visit(node.left), operator(","), visit(node.right), operator("⟩"));
    if (node.kind === "Identity") {
      if (identitySugar) {
        // Keep the carrier explicit, including for nested identities. This is
        // only notation for Eq, never a conversion to definitional equality.
        const formula = fenced(row(visit(node.left),
          element("msub", operator("="), visit(node.carrier)), visit(node.right)));
        formula.dataset.identitySugar = "true";
        return formula;
      }
      return row(element("msub", element("mi", "Id"), visit(node.carrier)),
        fenced(row(visit(node.left), operator(","), visit(node.right))));
    }
    const symbols = { Product: "×", Sum: "+", Arrow: "→", Equality: "=", DefEq: "≡" };
    const precedence = { Pi: 0, Sigma: 0, Lambda: 0, Arrow: 1, Sum: 2, Product: 3, Equality: 4, DefEq: 4 };
    if (symbols[node.kind]) {
      const operand = (child, left) => {
        const view = visit(child);
        const p = precedence[child.kind] ?? 9, parent = precedence[node.kind];
        return p < parent || (p === parent && (left || node.kind === "Equality")) ? fenced(view) : view;
      };
      return row(operand(node.left, true), operator(symbols[node.kind]), operand(node.right, false));
    }
    throw new Error(`Unknown mathematical display node: ${node.kind}`);
  }
  let content;
  const { groups, tail } = independentBinderGroups(tree, groupIndependentBinders);
  if (groups.reduce((count, group) => count + group.length, 0) > 3) {
    content = element("mtable");
    content.setAttribute("columnalign", "left");
    content.setAttribute("rowspacing", "0.35em");
    for (const group of groups)
      content.append(element("mtr", element("mtd", binderPrefix(group))));
    content.append(element("mtr", element("mtd", visit(tail))));
  } else content = visit(tree);
  const math = element("math", content);
  math.setAttribute("display", "block");
  container.replaceChildren(math);
}
