import { cubicalText } from "./cubical-notation.mjs";

// Print a checked term in Cubist source syntax, for messages and the command
// line: `A -> B`, `forall x : A. B`, `A and B`, `exists x : A. B`, `A or B`,
// `x = y`, `p @ i`, `fun (x, y : A) => b`, `f(a, b)`, `(a, b)`, `left(a)`, `tt`,
// numerals and binary numerals, and `+`, `*`, `<`, `<=` for the arithmetic
// library. Forms without a source spelling fall back to the inspector's
// notation. Parentheses follow the
// parser's precedence: binders < -> < or < and < = < + < * < @; `->`, `or` and
// `and` group to the right, `+` and `*` to the left.
const LEVEL = { binder: 0, arrow: 1, or: 2, and: 3, compare: 4, plus: 5, times: 6, at: 7, atom: 9 };
const infix = { add: ["+", LEVEL.plus], mul: ["*", LEVEL.times], le: ["<=", LEVEL.compare], isLt: ["<", LEVEL.compare] };
const arithmetic = /^(?:naturals|primes)__(add|mul|le|isLt)$/;

// `symbols` maps kernel names to their display names, as for cubicalText.
// Without an entry, a definition shows its name without the module prefix.
export function sourceText(term, symbols = {}, limit = 4000) {
  let budget = limit;
  const label = binding => symbols[binding]?.name
    ?? (binding.includes("__") && !binding.startsWith("__") ? binding.slice(binding.indexOf("__") + 2) : binding);
  // Terms share subterms, so each scan visits a node once.
  const mentions = (t, variable, seen = new Set()) => {
    if (!t || typeof t !== "object" || seen.has(t)) return false;
    seen.add(t);
    if (t.tag === "Var") return t.name === variable;
    if (["Pi", "Lam", "Sigma", "W"].includes(t.tag) && t.name === variable) return mentions(t.domain, variable, seen);
    return Object.values(t).some(child => mentions(child, variable, seen));
  };
  const numeral = t => {
    let n = 0;
    while (t?.tag === "Succ") { n++; t = t.value; }
    return t?.tag === "Zero" ? n : null;
  };
  // A dimension occurs in a term through interval literals `i:1` and `i:0`.
  const varies = (t, dim, seen = new Set()) => {
    if (typeof t === "string") return t === `${dim}:0` || t === `${dim}:1`;
    if (!t || typeof t !== "object" || seen.has(t)) return false;
    seen.add(t);
    return Object.values(t).some(child => varies(child, dim, seen));
  };
  // Interval formulas are disjunctions of conjunctions of literals; `i:0` is
  // the reversed coordinate.
  const literal = text => text.endsWith(":0") ? `flip(${text.slice(0, -2)})` : text.replace(/:1$/, "");
  const conjunction = clause => clause.length ? clause.map(literal).reduce((a, b) => `meet(${a}, ${b})`) : "1";
  const interval = value => value.length ? value.map(conjunction).reduce((a, b) => `join(${a}, ${b})`) : "0";
  // A binary number from the library's binary_naturals, in normal form:
  // left(tt) is 0b0, and right(p) a W tree whose leaf is the leading 1 and
  // whose unary nodes are the trailing digits, the last digit outermost.
  const binary = t => {
    const shape = t.as;
    if (shape?.tag !== "Sum" || shape.left?.tag !== "Unit" || shape.right?.tag !== "W") return null;
    if (t.tag === "Inl") return t.value?.tag === "Point" ? "0b0" : null;
    let digits = "", p = t.value;
    while (p?.tag === "Sup") {
      const label = p.label;
      if (label?.tag === "Inl" && label.value?.tag === "Point") return `0b1${digits}`;
      const digit = { Inl: "0", Inr: "1" }[label?.value?.tag];
      if (label?.tag !== "Inr" || !digit || label.value.value?.tag !== "Point"
        || p.children?.tag !== "Lam" || mentions(p.children.body, p.children.name)) return null;
      digits = digit + digits;
      p = p.children.body;
    }
    return null;
  };
  // A motive's variable shown under another name; a binder of the same name
  // inside shadows the renaming.
  const renames = new Map();
  const renaming = (from, to, fn) => {
    if (from === to) return fn();
    renames.set(from, to);
    try { return fn(); } finally { renames.delete(from); }
  };
  const under = (names, fn) => {
    const shadowed = [names].flat().filter(name => renames.has(name)).map(name => [name, renames.get(name)]);
    for (const [name] of shadowed) renames.delete(name);
    try { return fn(); } finally { for (const [name, to] of shadowed) renames.set(name, to); }
  };
  // A bound name that also occurs in `outside` gets a numbered variant.
  const apart = (name, outside, whole) => {
    if (!mentions(outside, name)) return name;
    for (let i = 1; ; i++) if (!mentions(whole, `${name}${i}`)) return `${name}${i}`;
  };
  const show = t => print(t)[0];
  const sub = (t, needed) => { const [text, level] = print(t); return level < needed ? `(${text})` : text; };
  const atom = text => [text, LEVEL.atom];
  const fallback = t => { const text = cubicalText(t, symbols); return atom(/^[[λΠΣ]/.test(text) ? `(${text})` : text); };
  // The text of a term and the precedence level of its outermost form.
  function print(t) {
    if (--budget < 0) return atom("…");
    switch (t?.tag) {
      case "U": return atom(`U${t.level}`);
      case "Nat": case "Unit": case "Void": return atom(t.tag);
      case "Point": return atom("tt");
      case "Zero": case "Succ": {
        const n = numeral(t);
        return atom(n !== null ? String(n) : `succ(${show(t.value)})`);
      }
      case "Var": return atom(renames.get(t.name) ?? label(t.name));
      case "DefRef": return atom(label(t.name));
      case "Pi": case "Sigma": {
        const pi = t.tag === "Pi";
        if (mentions(t.body, t.name))
          return [`${pi ? "forall" : "exists"} ${t.name} : ${show(t.domain)}. ${under(t.name, () => show(t.body))}`, LEVEL.binder];
        const level = pi ? LEVEL.arrow : LEVEL.and;
        return [`${sub(t.domain, level + 1)} ${pi ? "->" : "and"} ${under(t.name, () => sub(t.body, level))}`, level];
      }
      case "Sum": return [`${sub(t.left, LEVEL.or + 1)} or ${sub(t.right, LEVEL.or)}`, LEVEL.or];
      case "Lam": {
        // fun (x, y : A, z : B) => body
        const groups = [];
        let body = t;
        while (body.tag === "Lam") {
          const last = groups.at(-1), domain = show(body.domain);
          if (last?.domain === domain && !last.names.some(name => mentions(body.domain, name))) last.names.push(body.name);
          else groups.push({ names: [body.name], domain });
          body = body.body;
        }
        const binders = groups.map(group => `${group.names.join(", ")} : ${group.domain}`).join(", ");
        return [`fun (${binders}) => ${under(groups.flatMap(group => group.names), () => show(body))}`, LEVEL.binder];
      }
      // Eliminators print as the source forms that build them. The motive's
      // bound name is shown as the one the branches bind: `as k` binds both.
      case "NatRec": {
        const { motive, step } = t;
        if (motive?.tag !== "Lam" || step?.tag !== "Lam" || step.body?.tag !== "Lam") return fallback(t);
        // `induction k as k` would be correct but hard to read.
        const k = apart(step.name, t.value, t), h = apart(step.body.name, t.value, t);
        const type = under(motive.name, () => renaming(motive.name, k, () => show(motive.body)));
        const successor = under([step.name, step.body.name], () =>
          renaming(step.name, k, () => renaming(step.body.name, h, () => show(step.body.body))));
        return [`induction ${show(t.value)} as ${k} return ${type} { zero => ${show(t.zero)}; `
          + `succ ${h} => ${successor}; }`, LEVEL.binder];
      }
      case "SumRec": {
        const { motive, left, right } = t;
        if ([motive, left, right].some(branch => branch?.tag !== "Lam")) return fallback(t);
        return [`match ${show(t.value)} as ${motive.name} return ${under(motive.name, () => show(motive.body))} { `
          + `left ${left.name} => ${under(left.name, () => show(left.body))}; `
          + `right ${right.name} => ${under(right.name, () => show(right.body))}; }`, LEVEL.binder];
      }
      case "App": {
        const args = [];
        let head = t;
        while (head.tag === "App") { args.unshift(head.arg); head = head.fn; }
        const operator = head.tag === "DefRef" && args.length === 2 && arithmetic.exec(head.name)?.[1];
        if (operator) {
          const [symbol, level] = infix[operator], left = level === LEVEL.compare ? level + 1 : level;
          return [`${sub(args[0], left)} ${symbol} ${sub(args[1], level + 1)}`, level];
        }
        return atom(`${sub(head, LEVEL.atom)}(${args.map(show).join(", ")})`);
      }
      case "Pair": {
        const items = [show(t.first)];
        let rest = t.second;
        while (rest?.tag === "Pair") { items.push(show(rest.first)); rest = rest.second; }
        return atom(`(${[...items, show(rest)].join(", ")})`);
      }
      case "PApp": return [`${sub(t.path, LEVEL.at + 1)} @ ${interval(t.arg)}`, LEVEL.at];
      case "Inl": case "Inr": return atom(binary(t) ?? `${t.tag === "Inl" ? "left" : "right"}(${show(t.value)})`);
      case "W": return atom(`W(${show(t.domain)}, ${show({ tag: "Lam", name: t.name, domain: t.domain, body: t.body })})`);
      case "Sup": return atom(`sup(${show(t.as)}, ${show(t.label)}, ${show(t.children)})`);
      case "Abort": return atom(`absurd(${show(t.impossible)})`);
      case "Fst": return atom(`first(${show(t.pair)})`);
      case "Snd": return atom(`second(${show(t.pair)})`);
      case "Path":
        // An equality: a path whose type does not vary along it.
        if (!varies(t.family, t.dim))
          return [`${sub(t.left, LEVEL.compare + 1)} = ${sub(t.right, LEVEL.compare + 1)}`, LEVEL.compare];
        return fallback(t);
      default: return fallback(t);
    }
  }
  return show(term);
}
