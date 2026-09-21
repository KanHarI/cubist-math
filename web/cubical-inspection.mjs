// Presentation annotations for checked cubical syntax. The original terms are
// retained for raw inspection/export. Local names abbreviate their actual
// elaborated terms, not new variables or unchecked source assertions.
export function stripAscriptions(term) {
  while (term?.tag === "App" && term.fn.tag === "Lam" && term.fn.body.tag === "Var"
    && term.fn.body.name === term.fn.name) term = term.arg;
  return term;
}

export function foldedInspection(view, aliases = []) {
  const memo = new WeakMap(), intern = new Map();
  const key = term => {
    if (!term || typeof term !== "object") return `literal:${JSON.stringify(term)}`;
    term = stripAscriptions(term);
    if (memo.has(term)) return memo.get(term);
    const result = Array.isArray(term) ? `[${term.map(key).join(",")}]`
      : `{${Object.entries(term).map(([name, value]) => `${name}:${key(value)}`).join(",")}}`;
    if (!intern.has(result)) intern.set(result, intern.size + 1);
    const id = `node:${intern.get(result)}`; memo.set(term, id); return id;
  };
  const names = new Map();
  // Source aliases are selected from the lexical environment of this occurrence.
  // Exact checked syntax matches need no normalization or proof search.
  for (const alias of aliases) {
    if (alias.term.tag === "Var") continue;
    const entry = { tag: "DisplayRef", name: alias.name, binding: alias.binding };
    if (!names.has(key(alias.term))) names.set(key(alias.term), entry);
  }
  const visited = [new WeakMap(), new WeakMap()];
  const visit = (raw, root = false, bound = new Set()) => {
    if (!raw || typeof raw !== "object") return raw;
    const term = stripAscriptions(raw);
    if (Array.isArray(term)) return term.map(child => visit(child, false, bound));
    // Aliases only apply outside term binders: their meaning belongs to the
    // checked local telescope, not a potentially shadowing internal binder.
    const alias = !bound.size && names.size && names.get(key(term));
    if (alias && !(root && (alias.binding === view.name || alias.binding === view.sourceBinding))) return alias;
    const cache = visited[bound.size ? 1 : 0];
    if (!root && cache.has(term)) return cache.get(term);
    const result = {};
    if (!root) cache.set(term, result);
    for (const [field, value] of Object.entries(term)) {
      const binds = (field === "body" && ["Pi", "Sigma", "Lam", "W"].includes(term.tag))
        || ["Path", "PLam", "Comp", "HComp", "Trans"].includes(term.tag);
      result[field] = visit(value, false, binds ? new Set(bound).add(term.name ?? term.dim) : bound);
    }
    return result;
  };
  const expression = visit(view.expression, true), type = visit(view.type);
  return { expression, type, context: view.context.map(entry => ({ ...entry, type: visit(entry.type) })) };
}
