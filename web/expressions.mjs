// One renderer supplies text, occurrence ranges, and CLI selection semantics.
// A path identifies an occurrence even when several occurrences share an AST ID.
export const roles = {
  Pi: ["domain", "codomain"],
  Sigma: ["domain", "codomain"],
  W: ["labels", "arity"],
  Lambda: ["body"],
  Ap: ["function", "argument"],
  Tuple: ["first", "second"],
  Eq: ["carrier", "left", "right"],
  DefEq: ["left", "right"],
  Inl: ["value"],
  Inr: ["value"],
  Refl: ["value"],
  SN: ["predecessor"],
};
const leafNames = {
  Unit: "Unit",
  Singleton: "⋆",
  Void: "Void",
  Nat: "Nat",
  ZN: "0",
  UUOmega: "Uω",
  UUKappa: "Uκ",
};
const operators = {
  SN: "succ",
  Inl: "inl",
  Inr: "inr",
  Refl: "refl",
  WSup: "sup",
  IndNat: "nat.elim",
  IndSigma: "sigma.elim",
  IndSum: "sum.elim",
  IndEq: "eq.elim",
  IndVoid: "void.elim",
  IndUnit: "unit.elim",
  IndW: "w.elim",
};
export function layout(tree, contextNames = {}) {
  let text = "";
  const spans = [];
  const emit = (s) => {
    text += s;
  };
  function visit(n, path, env = []) {
    if (!n) {
      emit("?");
      return;
    }
    const start = text.length;
    const child = (i, e = env) => visit(n.children[i], [...path, i], e);
    if (n.truncated) emit("…");
    else if (leafNames[n.kind]) emit(leafNames[n.kind]);
    else if (n.kind === "U") emit(`U${n.parameter}`);
    else if (n.kind === "VRef") emit(env[n.parameter] ?? `#${n.parameter | 0}`);
    else if (n.kind === "CRef" || n.kind === "UCRef")
      emit(contextNames[n.parameter] ?? `c${n.parameter}`);
    else if (n.kind === "DRef") emit(`def${n.parameter}`);
    else if (n.kind === "Axiom") emit(`axiom${n.parameter}`);
    else if (n.kind === "Lambda") {
      const x = `x${env.length}`;
      emit(`(λ ${x}. `);
      child(0, [x, ...env]);
      emit(")");
    } else if (["Pi", "Sigma", "W"].includes(n.kind)) {
      const x = `x${env.length}`,
        extended = [x, ...env];
      emit(`(${n.kind === "Pi" ? "Π" : n.kind === "Sigma" ? "Σ" : "W"} ${x}: `);
      child(0, extended);
      emit(". ");
      child(1, extended);
      emit(")");
    } else if (n.kind === "Ap") {
      emit("(");
      child(0);
      emit(" ");
      child(1);
      emit(")");
    } else if (n.kind === "Tuple") {
      emit("⟨");
      child(0);
      emit(", ");
      child(1);
      emit("⟩");
    } else if (n.kind === "DefEq") {
      emit("(");
      child(0);
      emit(" ≡ ");
      child(1);
      emit(")");
    } else if (n.kind === "Sum") {
      emit("(");
      child(0);
      emit(" + ");
      child(1);
      emit(")");
    } else {
      emit((operators[n.kind] || n.kind) + "(");
      n.children.forEach((_, i) => {
        if (i) emit(", ");
        child(i);
      });
      emit(")");
    }
    spans.push({ start, end: text.length, path, node: n });
  }
  visit(tree, []);
  return { text, spans };
}
export function atPath(tree, path) {
  let n = tree;
  for (const i of path) {
    if (!n || n.truncated || !n.children[i])
      throw new Error("Selection is outside the displayed expression.");
    n = n.children[i];
  }
  if (!n || n.truncated)
    throw new Error(
      "Expand or select a smaller expression; this subtree was truncated.",
    );
  return n;
}
export function pathFromNames(tree, parts) {
  const path = [];
  let n = tree;
  for (const part of parts) {
    const i = /^[0-3]$/.test(part)
      ? Number(part)
      : (roles[n.kind] || []).indexOf(part);
    if (i < 0 || !n.children[i])
      throw new Error(
        `No child ${part} on ${n.kind}. Available: ${(roles[n.kind] || n.children.map((_, j) => String(j))).join(", ")}`,
      );
    path.push(i);
    n = n.children[i];
  }
  atPath(tree, path);
  return path;
}
export function pathFromMarked(tree, marked, contextNames = {}) {
  const { text, spans } = layout(tree, contextNames);
  const matches = [];
  for (const span of spans)
    if (!span.node.truncated) {
      for (const [left, right] of [
        ["(", ")"],
        ["[[", "]]"],
      ]) {
        const candidate =
          text.slice(0, span.start) +
          left +
          text.slice(span.start, span.end) +
          right +
          text.slice(span.end);
        if (candidate === marked.trim()) matches.push(span.path);
      }
    }
  const distinct = [
    ...new Map(matches.map((p) => [JSON.stringify(p), p])).values(),
  ];
  if (distinct.length !== 1)
    throw new Error(
      distinct.length
        ? "Ambiguous parentheses; use a path or [[selection]]."
        : "Copy the displayed expression unchanged, adding one pair of parentheses or [[ ]] around an existing subtree.",
    );
  return distinct[0];
}
export function selectedText(tree, path, contextNames = {}) {
  const { text, spans } = layout(tree, contextNames);
  const s = spans.find((s) => JSON.stringify(s.path) === JSON.stringify(path));
  return s
    ? text.slice(0, s.start) +
        "⟦" +
        text.slice(s.start, s.end) +
        "⟧" +
        text.slice(s.end)
    : text;
}
