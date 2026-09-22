// Display the native checked syntax itself. Definition references stay named;
// this does not reconstruct an unchecked expression from Cubist source.
export function cubicalMathTree(term, symbols = {}, limit = 1200, { paths = false } = {}) {
  let remaining = limit;
  const boundNames = new Map(), freeCache = new WeakMap();
  const free = (term, variable) => {
    if (!term || typeof term !== "object") return false;
    let cache = freeCache.get(term);
    if (!cache) { cache = new Map(); freeCache.set(term, cache); }
    if (cache.has(variable)) return cache.get(variable);
    const found = term.tag === "Var" ? term.name === variable
      : ["Pi", "Sigma", "Lam", "W"].includes(term.tag)
        ? free(term.domain, variable) || (term.name !== variable && free(term.body, variable))
        : Object.values(term).some(child => free(child, variable));
    cache.set(variable, found); return found;
  };
  const sourceNames = new Map();
  for (const [variable, symbol] of Object.entries(symbols)) {
    if (!symbol.local) continue;
    if (!sourceNames.has(symbol.name)) sourceNames.set(symbol.name, []);
    sourceNames.get(symbol.name).push(variable);
  }
  const label = value => boundNames.get(value) ?? symbols[value]?.name ?? value;
  const underBinder = (variable, body, renderBody) => {
    let spelling = symbols[variable]?.name ?? variable;
    while ([...boundNames].some(([key, name]) => key !== variable && name === spelling)
      || (sourceNames.get(spelling) ?? []).some(key => key !== variable && !boundNames.has(key) && free(body, key))) spelling += "′";
    const previous = boundNames.get(variable); boundNames.set(variable, spelling);
    const result = renderBody();
    if (previous === undefined) boundNames.delete(variable); else boundNames.set(variable, previous);
    return { name: spelling, body: result };
  };
  const name = value => ({ kind: "Name", name: value });
  const call = (fn, args) => ({ kind: "Call", fn: name(fn), args });
  const formula = value => name(value.length ? value.map(c => c.length ? c.join(" ∧ ") : "1").join(" ∨ ") : "0");
  const depends = (value, dim) => typeof value === "string" ? value === `${dim}:0` || value === `${dim}:1`
    : value && typeof value === "object" && Object.values(value).some(v => depends(v, dim));
  function visit(t, path = []) {
    const child = (value, ...keys) => visit(value, [...path, ...keys]);
    const tree = build(t, child);
    return paths ? { ...tree, sourcePath: path } : tree;
  }
  function build(t, child) {
    if (!t || --remaining < 0) return name("…");
    if (t.tag === "DisplayRef") return { ...name(t.name), contextBinding: t.binding, local: true };
    if (t.tag === "DefRef") return { ...name(symbols[t.name]?.name ?? t.name), binding: t.name };
    if (t.tag === "Var") return { ...name(label(t.name)), local: symbols[t.name]?.kind !== "axiom",
      ...(symbols[t.name]?.kind === "axiom" ? { binding: t.name, axiomNotation: t.name.startsWith("__assumption_Truncate_U") ? "truncation" : undefined }
        : symbols[t.name]?.binding ? { contextBinding: symbols[t.name].binding } : {}) };
    if (t.tag === "U") return { kind: "Universe", level: t.level };
    if (["Nat", "Unit", "Void"].includes(t.tag)) return name(t.tag);
    if (t.tag === "Zero") return { kind: "Number", value: 0 };
    if (t.tag === "Point") return name("⋆");
    if (t.tag === "Succ") {
      const value = child(t.value, "value");
      return value.kind === "Number" ? { kind: "Number", value: value.value + 1 } : call("succ", [value]);
    }
    if (["Pi", "Sigma"].includes(t.tag)) {
      if (!free(t.body, t.name)) return { kind: t.tag === "Pi" ? "Arrow" : "Product", left: child(t.domain, "domain"), right: child(t.body, "body") };
      const domain = child(t.domain, "domain"), binder = underBinder(t.name, t.body, () => child(t.body, "body"));
      return { kind: t.tag, ...binder, domain, domainDependencies: null, domainKey: null };
    }
    if (t.tag === "Lam") { const domain = child(t.domain, "domain"); return { kind: "Lambda", domain, ...underBinder(t.name, t.body, () => child(t.body, "body")) }; }
    if (t.tag === "App") {
      if (paths) return { kind: "Call", fn: child(t.fn, "fn"), args: [child(t.arg, "arg")] };
      const args = []; let fn = t;
      while (fn.tag === "App" && remaining-- > 0) { args.unshift(visit(fn.arg)); fn = fn.fn; }
      const head = visit(fn);
      if (head.axiomNotation === "truncation") head.truncationArgument = 0;
      return { kind: "Call", fn: head, args };
    }
    if (t.tag === "Pair" && paths) return call("pair", [child(t.as, "as"), child(t.first, "first"), child(t.second, "second")]);
    if (t.tag === "Pair") return { kind: "Pair", left: child(t.first, "first"), right: child(t.second, "second") };
    if (t.tag === "Sum") return { kind: "Sum", left: child(t.left, "left"), right: child(t.right, "right") };
    if (["Fst", "Snd"].includes(t.tag)) return call(t.tag.toLowerCase(), [child(t.pair, "pair")]);
    if (t.tag === "Path" && !depends(t.family, t.dim))
      return { kind: "Identity", carrier: child(t.family, "family"), left: child(t.left, "left"), right: child(t.right, "right") };
    if (t.tag === "Path") return call("PathP", [{ kind: "Lambda", name: t.dim, body: child(t.family, "family") }, child(t.left, "left"), child(t.right, "right")]);
    if (t.tag === "PLam" && paths) return call("path", [
      { kind: "Lambda", name: t.dim, body: child(t.family, "family") },
      { kind: "Lambda", name: t.dim, body: child(t.body, "body") }]);
    if (t.tag === "PLam") return !depends(t.family, t.dim) && !depends(t.body, t.dim)
      ? call("refl", [child(t.body, "body")]) : call("path", [{ kind: "Lambda", name: t.dim, body: child(t.body, "body") }]);
    if (t.tag === "PApp") return call("at", [child(t.path, "path"), formula(t.arg)]);
    if (t.tag === "PushPath") return call("push_path_at", [child(t.as, "as"), child(t.value, "value"), formula(t.arg)]);
    if (t.tag === "W") return call("W", [child(t.domain, "domain"), { kind: "Lambda", name: t.name, body: child(t.body, "body") }]);
    if (t.tag === "Comp") return { kind: "Scope", names: [t.dim], body: call("comp", [child(t.family, "family"),
      ...t.system.map((p, index) => call("face", [formula(p.face), child(p.term, "system", index, "term")])), child(t.base, "base")]) };
    if (t.tag === "HComp") return call("hcomp", [child(t.family, "family"), ...t.system.map((p, index) => call("face", [formula(p.face),
      { kind: "Lambda", name: t.dim, body: child(p.term, "system", index, "term") }])), child(t.base, "base")]);
    if (t.tag === "Trans") return call("transp", [{ kind: "Lambda", name: t.dim, body: child(t.family, "family") }, formula(t.face), child(t.base, "base")]);
    if (t.tag === "Glue") return call("Glue", [child(t.base, "base"), ...t.system.map((p, index) => call("face", [formula(p.face), child(p.type, "system", index, "type"), child(p.equiv, "system", index, "equiv")]))]);
    if (t.tag === "GlueTerm") return call("glue", [child(t.as, "as"), child(t.base, "base"), ...t.system.map((p, index) => call("face", [formula(p.face), child(p.term, "system", index, "term")]))]);
    const fields = { NatRec: ["motive", "zero", "step", "value"], UnitRec: ["motive", "point", "value"],
      SumRec: ["motive", "left", "right", "value"], WRec: ["motive", "step", "value"],
      Sup: ["as", "label", "children"], Inl: ["as", "value"], Inr: ["as", "value"],
      Abort: ["as", "impossible"], Unglue: ["as", "value"],
      Pushout: ["center", "left", "right", "maps"], PushLeft: ["as", "value"],
      PushRight: ["as", "value"], PushElim: ["motive", "left", "right", "bridge"] };
    if (!fields[t.tag]) throw new Error(`Unsupported cubical notation: ${t.tag}`);
    return call(t.tag, fields[t.tag].map(key => child(t[key], key)));
  }
  return visit(term);
}

// Text fragments wrap naturally in narrow statement panels while keeping each
// reference attached to its checked binding (not a lookup by printed spelling).
export function cubicalTextParts(tree) {
  const literal = text => [{ text }];
  const join = (parts, separator) => parts.flatMap((part, index) => index ? [...literal(separator), ...part] : part);
  const show = t => {
    if (t.kind === "Name") return [{ text: t.name, binding: t.contextBinding ?? t.binding }];
    if (t.kind === "Number") return literal(String(t.value));
    if (t.kind === "Universe") return literal(`U${t.level}`);
    if (t.kind === "Call") return [...(t.fn.kind === "Lambda" ? [...literal("("), ...show(t.fn), ...literal(")")] : show(t.fn)),
      ...literal("("), ...join(t.args.map(show), ", "), ...literal(")")];
    if (t.kind === "Lambda") return [...literal(`λ ${t.domain ? "(" : ""}${t.name}`),
      ...(t.domain ? [...literal(" : "), ...show(t.domain), ...literal(")")] : []), ...literal(". "), ...show(t.body)];
    if (["Pi", "Sigma"].includes(t.kind)) return [...literal(`${t.kind === "Pi" ? "Π" : "Σ"} (${t.name} : `), ...show(t.domain), ...literal("), "), ...show(t.body)];
    if (t.kind === "Identity") return [...literal("("), ...show(t.left), ...literal(" =["), ...show(t.carrier), ...literal("] "), ...show(t.right), ...literal(")")];
    if (t.kind === "Scope") return [...literal(`[${t.names.join(", ")}]. `), ...show(t.body)];
    const operator = { Arrow: "→", Product: "×", Sum: "+", Pair: "," }[t.kind];
    return [...literal("("), ...show(t.left), ...literal(` ${operator} `), ...show(t.right), ...literal(")")];
  };
  return show(tree);
}

export function cubicalText(term, symbols = {}) {
  return cubicalTextParts(cubicalMathTree(term, symbols)).map(part => part.text).join("");
}
