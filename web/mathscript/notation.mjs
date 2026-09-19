import { parse } from "./parser.mjs";

// Folding proposals from successfully checked syntax. These nodes are NEVER
// displayed directly: kernel-folding.mjs must construct and certify an actual
// kernel term first. Bindings identify the original checked declarations;
// the plan's shape is only a hint and is not trusted as proof evidence.
export function notationFromSyntax(node, globals = new Map(), bound = new Set()) {
  const visit = (n, scope = bound) => notationFromSyntax(n, globals, scope);
  const name = value => ({ kind: "Name", name: value,
    ...(bound.has(value) ? { local: true } : globals.get(value)?.binding ? { binding: globals.get(value).binding } : {}) });
  const call = (fn, args) => ({ kind: "Call", fn, args });
  if (node.kind === "name") {
    if (!bound.has(node.name) && /^U[0-9]+$/.test(node.name))
      return { kind: "Universe", level: Number(node.name.slice(1)) };
    return name(node.name);
  }
  if (node.kind === "number") return { kind: "Number", value: node.value };
  if (node.kind === "induction") {
    const scope = new Set(bound).add(node.index.text);
    return { kind: "Induction", index: node.index.text, hypothesis: node.hypothesis.text,
      value: visit(node.value), type: visit(node.type, scope), base: visit(node.base),
      step: visit(node.step, new Set(scope).add(node.hypothesis.text)) };
  }
  if (["forall", "exists", "lambda"].includes(node.kind)) {
    const scope = new Set(bound).add(node.name.text);
    return { kind: { forall: "Pi", exists: "Sigma", lambda: "Lambda" }[node.kind],
      name: node.name.text, domain: visit(node.domain), body: visit(node.body, scope) };
  }
  if (node.kind === "call") return call(visit(node.fn), node.args.map(n => visit(n)));
  if (node.kind === "pair") return { kind: "Pair", left: visit(node.left), right: visit(node.right) };
  if (node.kind === "binary") {
    const left = visit(node.left), right = visit(node.right);
    const kind = { and: "Product", or: "Sum", "->": "Arrow", "=": "Equality" }[node.operator];
    if (kind === "Equality" && node.carrier)
      return { kind: "Identity", carrier: visit(node.carrier), left, right };
    if (kind) return { kind, left, right };
    if (node.operator === "<") {
      // Match the elaborator: isLt when in scope; otherwise le(succ(n), p).
      return globals.has("isLt") || bound.has("isLt")
        ? call(name("isLt"), [left, right])
        : call(name("le"), [call(name("succ"), [left]), right]);
    }
    const operation = { "+": "add", "*": "mul", "<=": "le" }[node.operator];
    if (operation) return call(name(operation), [left, right]);
  }
  // Unsupported eliminator syntax and tactic blocks retain the stored term.
  // Do not invent a folded term when its translation is not represented here.
  throw new Error(`No folded notation for ${node.kind}`);
}

export function inferredType(T, globals, bound = new Set()) {
  // The full type's spelling includes substitutions performed by induction
  // and application. Nested descriptor templates can still contain the old
  // motive variables (e.g. a2 instead of a in nat_le_total).
  try { return notationFromSyntax(parse(T.pretty, true), globals, bound); } catch {}
  // An alias retains its name even when the elaborator knows its Pi/Sigma body.
  if (/^[A-Za-z_][A-Za-z_0-9]*(?:\(|$)/.test(T.pretty))
    return notationFromSyntax(parse(T.pretty, true), globals, bound);
  if (["pi", "sigma"].includes(T.kind)) {
    const name = T.binder.label;
    const domain = inferredType(T.domain, globals, bound);
    const body = inferredType(T.template, globals, new Set(bound).add(name));
    return name === "_"
      ? { kind: T.kind === "pi" ? "Arrow" : "Product", left: domain, right: body }
      : { kind: T.kind === "pi" ? "Pi" : "Sigma", name, domain, body };
  }
  if (T.kind === "sum") return { kind: "Sum", left: inferredType(T.left, globals, bound), right: inferredType(T.right, globals, bound) };
  return notationFromSyntax(parse(T.pretty, true), globals, bound);
}

export function declarationNotation(decl, type, globals) {
  const present = fn => { try { return fn(); } catch { return null; } };
  let signature = decl.type;
  if (signature) for (const p of [...decl.params].reverse())
    signature = { kind: "forall", name: p.name, domain: p.type, body: signature };
  return {
    expression: decl.kind === "def" && decl.value
      ? present(() => notationFromSyntax(decl.value, globals))
      : { kind: "Name", name: decl.name.text, binding: globals.get(decl.name.text)?.binding },
    type: present(() => signature ? notationFromSyntax(signature, globals) : inferredType(type, globals)),
  };
}
