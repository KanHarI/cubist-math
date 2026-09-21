// Display the native checked syntax itself. Definition references stay named;
// this does not reconstruct an unchecked expression from MathScript source.
export function cubicalMathTree(term, symbols = {}, limit = 1200) {
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
  const underBinder = (variable, body) => {
    let spelling = symbols[variable]?.name ?? variable;
    while ([...boundNames].some(([key, name]) => key !== variable && name === spelling)
      || (sourceNames.get(spelling) ?? []).some(key => key !== variable && !boundNames.has(key) && free(body, key))) spelling += "′";
    const previous = boundNames.get(variable); boundNames.set(variable, spelling);
    const result = visit(body);
    if (previous === undefined) boundNames.delete(variable); else boundNames.set(variable, previous);
    return { name: spelling, body: result };
  };
  const name = value => ({ kind: "Name", name: value });
  const call = (fn, args) => ({ kind: "Call", fn: name(fn), args });
  const formula = value => name(value.length ? value.map(c => c.length ? c.join(" ∧ ") : "1").join(" ∨ ") : "0");
  const depends = (value, dim) => typeof value === "string" ? value === `${dim}:0` || value === `${dim}:1`
    : value && typeof value === "object" && Object.values(value).some(v => depends(v, dim));
  function visit(t) {
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
      const value = visit(t.value);
      return value.kind === "Number" ? { kind: "Number", value: value.value + 1 } : call("succ", [value]);
    }
    if (["Pi", "Sigma"].includes(t.tag)) {
      if (!free(t.body, t.name)) return { kind: t.tag === "Pi" ? "Arrow" : "Product", left: visit(t.domain), right: visit(t.body) };
      const domain = visit(t.domain), binder = underBinder(t.name, t.body);
      return { kind: t.tag, ...binder, domain, domainDependencies: null, domainKey: null };
    }
    if (t.tag === "Lam") { const domain = visit(t.domain); return { kind: "Lambda", domain, ...underBinder(t.name, t.body) }; }
    if (t.tag === "App") {
      const args = []; let fn = t;
      while (fn.tag === "App" && remaining-- > 0) { args.unshift(visit(fn.arg)); fn = fn.fn; }
      const head = visit(fn);
      if (head.axiomNotation === "truncation") head.truncationArgument = 0;
      return { kind: "Call", fn: head, args };
    }
    if (t.tag === "Pair") return { kind: "Pair", left: visit(t.first), right: visit(t.second) };
    if (t.tag === "Sum") return { kind: "Sum", left: visit(t.left), right: visit(t.right) };
    if (["Fst", "Snd"].includes(t.tag)) return call(t.tag.toLowerCase(), [visit(t.pair)]);
    if (t.tag === "Path" && !depends(t.family, t.dim))
      return { kind: "Identity", carrier: visit(t.family), left: visit(t.left), right: visit(t.right) };
    if (t.tag === "Path") return call("PathP", [{ kind: "Lambda", name: t.dim, body: visit(t.family) }, visit(t.left), visit(t.right)]);
    if (t.tag === "PLam") return !depends(t.family, t.dim) && !depends(t.body, t.dim)
      ? call("refl", [visit(t.body)]) : call("path", [{ kind: "Lambda", name: t.dim, body: visit(t.body) }]);
    if (t.tag === "PApp") return call("at", [visit(t.path), formula(t.arg)]);
    if (t.tag === "PushPath") return call("push_path_at", [visit(t.as), visit(t.value), formula(t.arg)]);
    if (t.tag === "W") return call("W", [visit(t.domain), { kind: "Lambda", name: t.name, body: visit(t.body) }]);
    if (t.tag === "Comp") return { kind: "Scope", names: [t.dim], body: call("comp", [visit(t.family),
      ...t.system.map(p => call("face", [formula(p.face), visit(p.term)])), visit(t.base)]) };
    if (t.tag === "HComp") return call("hcomp", [visit(t.family), ...t.system.map(p => call("face", [formula(p.face),
      { kind: "Lambda", name: t.dim, body: visit(p.term) }])), visit(t.base)]);
    if (t.tag === "Trans") return call("transp", [{ kind: "Lambda", name: t.dim, body: visit(t.family) }, formula(t.face), visit(t.base)]);
    if (t.tag === "Glue") return call("Glue", [visit(t.base), ...t.system.map(p => call("face", [formula(p.face), visit(p.type), visit(p.equiv)]))]);
    if (t.tag === "GlueTerm") return call("glue", [visit(t.as), visit(t.base), ...t.system.map(p => call("face", [formula(p.face), visit(p.term)]))]);
    const fields = { NatRec: ["motive", "zero", "step", "value"], UnitRec: ["motive", "point", "value"],
      SumRec: ["motive", "left", "right", "value"], WRec: ["motive", "step", "value"],
      Sup: ["as", "label", "children"], Inl: ["as", "value"], Inr: ["as", "value"],
      Abort: ["as", "impossible"], Unglue: ["as", "value"],
      Pushout: ["center", "left", "right", "maps"], PushLeft: ["as", "value"],
      PushRight: ["as", "value"], PushElim: ["motive", "left", "right", "bridge"] };
    if (!fields[t.tag]) throw new Error(`Unsupported cubical notation: ${t.tag}`);
    return call(t.tag, fields[t.tag].map(key => visit(t[key])));
  }
  return visit(term);
}

export function cubicalText(term, symbols = {}) {
  const show = t => {
    if (t.kind === "Name") return t.name;
    if (t.kind === "Number") return String(t.value);
    if (t.kind === "Universe") return `U${t.level}`;
    if (t.kind === "Call") return `${show(t.fn)}(${t.args.map(show).join(", ")})`;
    if (t.kind === "Lambda") return `λ ${t.name}. ${show(t.body)}`;
    if (["Pi", "Sigma"].includes(t.kind)) return `${t.kind === "Pi" ? "Π" : "Σ"} (${t.name} : ${show(t.domain)}), ${show(t.body)}`;
    if (t.kind === "Identity") return `(${show(t.left)} =[${show(t.carrier)}] ${show(t.right)})`;
    if (["Arrow", "Product"].includes(t.kind)) return `(${show(t.left)} ${t.kind === "Arrow" ? "→" : "×"} ${show(t.right)})`;
    if (t.kind === "Scope") return `[${t.names.join(", ")}]. ${show(t.body)}`;
    return `(${show(t.left)} ${t.kind === "Sum" ? "+" : ","} ${show(t.right)})`;
  };
  return show(cubicalMathTree(term, symbols));
}
