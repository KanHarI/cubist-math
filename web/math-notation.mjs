import { kernelBinderCount } from "./expressions.mjs";
const mathNamespace = "http://www.w3.org/1998/Math/MathML";

// Read only actual checked AST constructors. Names annotate definition nodes;
// binder labels are cosmetic. The upstream kernel counts a binder in *both*
// children of Pi/Sigma, including the domain (see src/kernel/ast.c).
export function kernelMathTree(tree, references = {}, contextNames = {}) {
  const usesBinder = (node, depth = 0) => node.kind === "VRef" ? node.parameter === depth
    : node.children.some(child => usesBinder(child, depth + kernelBinderCount(node.kind)));
  const named = name => ({ kind: "Name", name });
  function visit(node, env = []) {
    if (node.truncated) return named("…");
    if (node.kind === "DRef" && references[node.id]) return { kind: "Name", ...references[node.id] };
    if (node.kind === "U") return { kind: "Universe", level: node.parameter };
    if (node.kind === "VRef") return { kind: "Name", name: env[node.parameter] ?? `#${node.parameter | 0}`, local: true };
    if (["CRef", "UCRef"].includes(node.kind)) return { kind: "Name", name: contextNames[node.parameter] ?? `c${node.parameter}`, local: true };
    if (["Nat", "Unit", "Void"].includes(node.kind)) return named(node.kind);
    if (node.kind === "ZN") return { kind: "Number", value: 0 };
    if (node.kind === "Singleton") return named("⋆");
    if (node.kind === "DRef") return named(`def${node.parameter}`);
    if (["Pi", "Sigma"].includes(node.kind)) {
      const name = node.binderName && node.binderName !== "_" ? node.binderName : `x${env.length}`;
      const extended = [name, ...env];
      const domain = visit(node.children[0], extended), body = visit(node.children[1], extended);
      return node.binderName === "_" && !usesBinder(node.children[1])
        ? { kind: node.kind === "Pi" ? "Arrow" : "Product", left: domain, right: body }
        : { kind: node.kind, name, domain, body };
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
    const extra = Array.from({ length: kernelBinderCount(node.kind) }, (_, i) => `x${env.length + i}`);
    const call = { kind: "Call", fn: named(node.kind), args: node.children.map(child => visit(child, [...extra].reverse().concat(env))) };
    return extra.length ? { kind: "Scope", names: extra, body: call } : call;
  }
  return visit(tree);
}

// Native MathML provides mathematical typesetting without a CDN, TeX input,
// HTML interpolation, or a change to the stored proof.
export function renderMathNotation(container, tree, { resolve = () => null, inspect = () => {} } = {}) {
  const doc = container.ownerDocument;
  const element = (tag, ...children) => {
    const node = doc.createElementNS(mathNamespace, tag);
    for (const child of children) node.append(typeof child === "string" ? doc.createTextNode(child) : child);
    return node;
  };
  const row = (...children) => element("mrow", ...children);
  const operator = text => element("mo", text);
  const fenced = node => row(operator("("), node, operator(")"));
  function visit(node) {
    if (node.kind === "Name") {
      const symbol = element("mi", node.name);
      if (!node.local) symbol.setAttribute("mathvariant", "normal");
      const target = node.binding && !node.local ? resolve(node.binding) : null;
      if (target) {
        symbol.dataset.name = node.name;
        symbol.setAttribute("class", "math-reference");
        symbol.setAttribute("role", "button");
        symbol.setAttribute("tabindex", "0");
        symbol.setAttribute("aria-label", `Inspect ${node.name}`);
        symbol.setAttribute("title", `Inspect ${node.name} and view its source`);
        symbol.addEventListener("click", () => inspect(target));
        symbol.addEventListener("keydown", event => {
          if (event.key === "Enter" || event.key === " ") { event.preventDefault(); inspect(target); }
        });
      }
      return symbol;
    }
    if (node.kind === "Universe") return element("msub", element("mi", "𝒰"), element("mn", String(node.level)));
    if (node.kind === "Scope") return row(operator("["), element("mtext", node.names.join(", ")), operator("]"), operator("."), visit(node.body));
    if (node.kind === "Number") return element("mn", String(node.value));
    if (["Pi", "Sigma", "Lambda"].includes(node.kind)) {
      if (node.kind === "Lambda") return row(operator("λ"), element("mi", node.name), operator("."), visit(node.body));
      const binder = row(element("mi", node.name), operator(":"), visit(node.domain));
      const symbol = operator({ Pi: "Π", Sigma: "Σ", Lambda: "λ" }[node.kind]);
      const body = visit(node.body);
      const space = element("mspace"); space.setAttribute("width", "0.3em");
      return row(element("msub", symbol, binder), space,
        ["Product", "Sum", "Arrow", "Equality"].includes(node.body.kind) ? fenced(body) : body);
    }
    if (node.kind === "Call") {
      const args = [];
      node.args.forEach((arg, i) => { if (i) args.push(operator(",")); args.push(visit(arg)); });
      const fn = visit(node.fn);
      return row(["Name", "Call"].includes(node.fn.kind) ? fn : fenced(fn), fenced(row(...args)));
    }
    if (node.kind === "Pair") return row(operator("⟨"), visit(node.left), operator(","), visit(node.right), operator("⟩"));
    if (node.kind === "Identity") return row(element("msub", element("mi", "Id"), visit(node.carrier)),
      fenced(row(visit(node.left), operator(","), visit(node.right))));
    const symbols = { Product: "×", Sum: "⊎", Arrow: "→", Equality: "=", DefEq: "≡" };
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
  const binders = [];
  let tail = tree;
  while (["Pi", "Sigma"].includes(tail.kind)) { binders.push(tail); tail = tail.body; }
  if (binders.length > 3) {
    content = element("mtable");
    content.setAttribute("columnalign", "left");
    content.setAttribute("rowspacing", "0.35em");
    for (const binder of binders) {
      const label = row(element("mi", binder.name), operator(":"), visit(binder.domain));
      content.append(element("mtr", element("mtd", element("msub", operator(binder.kind === "Pi" ? "Π" : "Σ"), label))));
    }
    content.append(element("mtr", element("mtd", visit(tail))));
  } else content = visit(tree);
  const math = element("math", content);
  math.setAttribute("display", "block");
  container.replaceChildren(math);
}
