import { cubicalText } from "./cubical-notation.mjs";
import { renameLevel, universeText } from "./cubical-levels.mjs";
import { localName, numberedName } from "./translator/names.mjs";
import {numeralValue} from "./translator/numerals.mjs";

// Print a checked term in Cubist source syntax, for messages and the command
// line: `A -> B`, `forall x : A. B`, `A and B`, `exists x : A. B`, `A or B`,
// `x = y`, `p @ i`, `fun (x, y : A) => b`, `f(a, b)`, `(a, b)`, `p.1`, `left(a)`, `tt`,
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
    ?? localName(binding);
  // Terms share subterms, so each scan visits a node once.
  const mentions = (t, variable, seen = new Set()) => {
    if (!t || typeof t !== "object" || seen.has(t)) return false;
    seen.add(t);
    if (t.tag === "Var") return t.name === variable;
    if (["Pi", "Lam", "Sigma", "LPi", "LLam"].includes(t.tag) && t.name === variable) return mentions(t.domain, variable, seen);
    return Object.values(t).some(child => mentions(child, variable, seen));
  };
  const numeral = numeralValue;
  // A dimension occurs in a term through interval literals `i:1` and `i:0`.
  const varies = (t, dim, seen = new Set()) => {
    if (typeof t === "string") return t === `${dim}:0` || t === `${dim}:1`;
    if (!t || typeof t !== "object" || seen.has(t)) return false;
    seen.add(t);
    return Object.values(t).some(child => varies(child, dim, seen));
  };
  // Interval formulas are disjunctions of conjunctions of literals; `i:0` is
  // the reversed coordinate. They print in the source's notation: -i, i & j
  // and i | j, where & binds tighter than |, and both tighter than @.
  const literal = text => text.endsWith(":0") ? `-${text.slice(0, -2)}` : text.replace(/:1$/, "");
  const conjunction = clause => clause.length ? clause.map(literal).join(" & ") : "1";
  const interval = value => value.length ? value.map(conjunction).join(" | ") : "0";
  // A face formula is a disjunction of conjunctions too, of equations `i:0`.
  // A Glue piece or a glue value on one equation is face(i, 0, …), and on any
  // other face face_when(on(i, 0) and on(j, 1) or …, …).
  const equation = text => `${text.slice(0, text.lastIndexOf(":"))}, ${text.slice(-1)}`;
  const onFace = (formula, parts) => formula.length === 1 && formula[0].length === 1
    ? `face(${equation(formula[0][0])}, ${parts.join(", ")})`
    : `face_when(${formula.length ? formula.map(clause => clause.length ? clause.map(text => `on(${equation(text)})`).join(" and ") : "1").join(" or ") : "0"}, ${parts.join(", ")})`;
  // A binary number from the archive's binary_naturals, in normal form:
  // binary_zero is 0b0, and binary_positive(p) holds binary_bit0 and
  // binary_bit1 digits, the last digit outermost, around the leading binary_one.
  const constructorOf = (t, signature) => {
    const head = t?.tag === "App" ? t.fn : t;
    return head?.tag === "Con" && head.sort?.tag === "Sort" && head.sort.signature === signature ? head.index : null;
  };
  const binary = t => {
    const natural = constructorOf(t, "binary_naturals__BinaryNat");
    if (natural === 0 && t.tag === "Con") return "0b0";
    if (natural !== 1 || t.tag !== "App") return null;
    let digits = "", p = t.arg;
    for (;;) {
      const index = constructorOf(p, "binary_naturals__BinaryPositive");
      if (index === 0 && p.tag === "Con") return `0b1${digits}`;
      if ((index !== 1 && index !== 2) || p.tag !== "App") return null;
      digits = (index === 1 ? "0" : "1") + digits;
      p = p.arg;
    }
  };
  // A motive's variable shown under another name; a binder of the same name
  // inside shadows the renaming.
  const renames = new Map();
  const renaming = (from, to, fn) => {
    if (from === to) return fn();
    renames.set(from, to);
    try { return fn(); } finally { renames.delete(from); }
  };
  // The variables bound where the printer is. A bound variable shows as its
  // binder does; only a free one is a definition or an assumption, shown by
  // its label: a binder a__b is not shown as b.
  const bound = new Map();
  const under = (names, fn) => {
    const list = [names].flat();
    const shadowed = list.filter(name => renames.has(name)).map(name => [name, renames.get(name)]);
    for (const [name] of shadowed) renames.delete(name);
    for (const name of list) bound.set(name, (bound.get(name) ?? 0) + 1);
    try { return fn(); } finally {
      for (const name of list) bound.set(name, bound.get(name) - 1);
      for (const [name, to] of shadowed) renames.set(name, to);
    }
  };
  const variable = name => renames.get(name) ?? (bound.get(name) ? name : label(name));
  // A bound name that also occurs in `outside` gets a numbered variant.
  const apart = (name, outside, whole) => {
    if (!mentions(outside, name)) return name;
    for (let i = 1; ; i++) if (!mentions(whole, numberedName(name, i))) return numberedName(name, i);
  };
  const show = t => print(t)[0];
  const sub = (t, needed) => { const [text, level] = print(t); return level < needed ? `(${text})` : text; };
  const atom = text => [text, LEVEL.atom];
  // A form without a source spelling is cubicalText's. It is given the
  // variables bound around it, and the renamed ones, as this printer shows
  // them: it shows them alike, and keeps its own binders apart from those
  // free in their bodies. Definitions keep their labels.
  const fallback = t => {
    const scope = new Map([...renames.keys(), ...[...bound.keys()].filter(name => bound.get(name))]
      .map(name => [name, variable(name)]));
    const text = cubicalText(t, symbols, { scope });
    return atom(/^[[λΠΣ]/.test(text) ? `(${text})` : text);
  };
  // A declared type's eliminator applied to a value, as the match or the
  // induction that builds it, when the printer knows the type's
  // constructors: one clause per constructor, `c(x, y) => body`, a path
  // constructor's written as the point it covers, `loop @ i => body`. A
  // clause takes the constructor's data and positions, then a recursive
  // result for each position, then its dimensions. Where a clause uses a
  // recursive result, the eliminator is an induction, and that clause names
  // its hypotheses after its arguments: `cons(head, tail, ih) => …`.
  const declaredMatch = (elim, value) => {
    const constructors = symbols[elim.signature]?.constructors, motive = elim.motive;
    if (!constructors || constructors.length !== elim.clauses?.length || motive?.tag !== "Lam") return null;
    const clauses = [];
    for (const [c, clause] of elim.clauses.entries()) {
      const { name, data, positions, dimensions } = constructors[c];
      const args = [], results = [], dims = [];
      let body = clause;
      // A clause that evaluation eta-reduced, as `succ` for fun (ih) =>
      // succ(ih), is applied to new names instead.
      const take = (into, stem) => {
        if (body?.tag === "Lam") { into.push(body.name); body = body.body; return; }
        const name = apart(stem, body, body);
        into.push(name);
        body = { tag: "App", fn: body, arg: { tag: "Var", name } };
      };
      for (let i = 0; i < data + positions; i++) take(args, "x");
      for (let i = 0; i < positions; i++) take(results, "ih");
      for (let i = 0; i < dimensions; i++) { if (body?.tag !== "PLam") return null; dims.push(body.dim); body = body.body; }
      clauses.push({ name, args, results, dims, body });
    }
    // `as z` is written only where the return type uses z, as the linter asks.
    const named = mentions(motive.body, motive.name);
    const hypotheses = clause => clause.results.some(result => mentions(clause.body, result));
    const shown = clauses.map(clause => {
      const { name, args, results, dims, body } = clause, names = hypotheses(clause) ? [...args, ...results] : args;
      return `${name}${names.length ? `(${names.join(", ")})` : ""}${dims.map(dim => ` @ ${dim}`).join("")} => `
        + `${under([...args, ...results], () => show(body))};`;
    });
    return `${clauses.some(hypotheses) ? "induction" : "match"} ${show(value)}${named ? ` as ${motive.name}` : ""} `
      + `return ${under(motive.name, () => show(motive.body))} { ${shown.join(" ")} }`;
  };
  // The text of a term and the precedence level of its outermost form.
  function print(t) {
    if (--budget < 0) return atom("…");
    switch (t?.tag) {
      case "U": return atom(universeText(renameLevel(t.level, variable)));
      // A universe variable's bound, in place of a context entry's type.
      case "LBound": return atom(universeText({ tag: "LConst", tier: t.tier, value: 0 }));
      case "Unit": case "Void": return atom(t.tag);
      case "Point": return atom("tt");
      case "Var": return atom(variable(t.name));
      case "DefRef": return atom(label(t.name));
      case "Pi": case "Sigma": {
        const pi = t.tag === "Pi";
        if (mentions(t.body, t.name))
          return [`${pi ? "forall" : "exists"} ${t.name} : ${show(t.domain)}. ${under(t.name, () => show(t.body))}`, LEVEL.binder];
        const level = pi ? LEVEL.arrow : LEVEL.and;
        return [`${sub(t.domain, level + 1)} ${pi ? "->" : "and"} ${under(t.name, () => sub(t.body, level))}`, level];
      }
      case "Sum": return [`${sub(t.left, LEVEL.or + 1)} or ${sub(t.right, LEVEL.or)}`, LEVEL.or];
      // Level quantification (G0) in its source syntax: the bound is UU0.
      case "LPi": return [`forall ${t.name} < UU0. ${under(t.name, () => show(t.body))}`, LEVEL.binder];
      case "LLam": return [`fun (${t.name} < UU0) => ${under(t.name, () => show(t.body))}`, LEVEL.binder];
      case "Lam": {
        // fun (x, y : A, z : B) => body, each domain in the scope of the
        // binders before it
        const groups = [], names = [];
        let body = t;
        while (body.tag === "Lam") {
          const last = groups.at(-1), domain = under(names, () => show(body.domain));
          if (last?.domain === domain && !last.names.some(name => mentions(body.domain, name))) last.names.push(body.name);
          else groups.push({ names: [body.name], domain });
          names.push(body.name);
          body = body.body;
        }
        const binders = groups.map(group => `${group.names.join(", ")} : ${group.domain}`).join(", ");
        return [`fun (${binders}) => ${under(names, () => show(body))}`, LEVEL.binder];
      }
      // Eliminators print as the source forms that build them. The motive's
      // bound name is shown as the one the branches bind: `as k` binds both.
      // NatInduction is no term: it is the source Nat's eliminator, applied,
      // in the shape its `induction` spelling reads.
      case "NatInduction": {
        const { motive, step } = t;
        if (motive?.tag !== "Lam" || step?.tag !== "Lam" || step.body?.tag !== "Lam") return fallback(t);
        // `induction k as k` would be correct but hard to read.
        const k = apart(step.name, t.value, t), h = apart(step.body.name, t.value, t);
        const type = under(motive.name, () => renaming(motive.name, k, () => show(motive.body)));
        const successor = under([step.name, step.body.name], () =>
          renaming(step.name, k, () => renaming(step.body.name, h, () => show(step.body.body))));
        // `as k` is written only where the motive or the successor clause uses k.
        const named = mentions(motive.body, motive.name) || mentions(step.body, step.name);
        return [`induction ${show(t.value)}${named ? ` as ${k}` : ""} return ${type} { zero => ${show(t.zero)}; `
          + `succ ${h} => ${successor}; }`, LEVEL.binder];
      }
      case "SumRec": {
        const { motive, left, right } = t;
        if ([motive, left, right].some(branch => branch?.tag !== "Lam")) return fallback(t);
        // `as z` is written only where the return type uses z, as the linter asks.
        const named = mentions(motive.body, motive.name);
        return [`match ${show(t.value)}${named ? ` as ${motive.name}` : ""} return ${under(motive.name, () => show(motive.body))} { `
          + `left ${left.name} => ${under(left.name, () => show(left.body))}; `
          + `right ${right.name} => ${under(right.name, () => show(right.body))}; }`, LEVEL.binder];
      }
      // A declared type's eliminator on its own, as evaluation leaves a
      // function by cases after eta reduction, is the function that applies
      // it: fun (n : Nat) => induction n …, or fun (x : T) => match x …, which
      // the application case below prints.
      case "Elim": {
        if (t.motive?.tag !== "Lam") return fallback(t);
        const nat = t.signature === "nat__Nat" && t.clauses?.length === 2 && t.clauses[1]?.tag === "Lam";
        const x = apart(nat ? "n" : "x", t, t), arg = { tag: "Var", name: x };
        const text = under(x, () => nat ? show({ tag: "App", fn: t, arg }) : declaredMatch(t, arg));
        return text ? [`fun (${x} : ${show(t.motive.domain)}) => ${text}`, LEVEL.binder] : fallback(t);
      }
      case "App": case "LApp": {
        const number=numeral(t);
        if(number!==null)return atom(String(number));
        const bits=binary(t);
        if(bits)return atom(bits);
        // The standard source Nat's eliminator has the existing induction
        // spelling. Eta reduction may leave its successor clause curried.
        if(t.tag==="App"&&t.fn.tag==="Elim"&&t.fn.signature==="nat__Nat"
          &&t.fn.motive?.tag==="Lam"&&t.fn.clauses?.length===2&&t.fn.clauses[1]?.tag==="Lam") {
          let step=t.fn.clauses[1];
          if(step.body.tag!=="Lam") {
            const h=apart("h",t,t);
            step={...step,body:{tag:"Lam",name:h,domain:t.fn.motive.body,
              body:{tag:"App",fn:step.body,arg:{tag:"Var",name:h}}}};
          }
          return print({tag:"NatInduction",motive:t.fn.motive,zero:t.fn.clauses[0],step,value:t.arg});
        }
        if(t.tag==="App"&&t.fn.tag==="Elim"){const text=declaredMatch(t.fn,t.arg);if(text)return [text,LEVEL.binder];}
        // An instantiation is an application to a universe.
        const args = [];
        let head = t;
        while (head.tag === "App" || head.tag === "LApp") { args.unshift(head.tag === "App" ? head.arg : { tag: "U", level: head.level }); head = head.fn; }
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
      case "Inl": case "Inr": return atom(`${t.tag === "Inl" ? "left" : "right"}(${show(t.value)})`);
      case "Abort": return atom(`absurd(${show(t.impossible)})`);
      case "Fst": case "Snd": return atom(`${sub(t.pair, LEVEL.atom)}.${t.tag === "Fst" ? 1 : 2}`);
      // Declared types (H1): an instance is its name applied to its recorded
      // levels, as universes, and its parameters; a constructor is its name.
      // An eliminator has no source form before `match`: it falls back.
      // Where the declared type's parameters are known, an erased universe,
      // which an instance does not carry, is written __U: whoever writes the
      // instance out supplies it, and the elaborator says so.
      case "Sort": {
        const universes = (t.levels ?? []).map(level => universeText(renameLevel(level, variable)));
        const parameters = (t.parameters ?? []).map(show), slots = symbols[t.signature]?.slots;
        const fits = slots && slots.filter(slot => slot === "recorded").length === universes.length
          && slots.filter(slot => slot === "parameter").length === parameters.length;
        const args = fits ? slots.map(slot => slot === "erased" ? "__U" : slot === "recorded" ? universes.shift() : parameters.shift())
          : [...universes, ...parameters];
        return atom(args.length ? `${label(t.signature)}(${args.join(", ")})` : label(t.signature));
      }
      case "Con": {const n=numeral(t);return n!==null?atom(String(n)):binary(t)?atom(binary(t)):t.name ? atom(t.name) : fallback(t);}
      case "Path":
        // An equality: a path whose type does not vary along it.
        if (!varies(t.family, t.dim))
          return [`${sub(t.left, LEVEL.compare + 1)} = ${sub(t.right, LEVEL.compare + 1)}`, LEVEL.compare];
        // A dependent path type, as the source writes it.
        return atom(`PathP(fun (${t.dim} : Interval) => ${show(t.family)}, ${show(t.left)}, ${show(t.right)})`);
      // A path, as the source writes it where its type is known; one that
      // does not vary is refl.
      case "PLam":
        if (!varies(t.body, t.dim) && !varies(t.family, t.dim)) return atom(`refl(${show(t.body)})`);
        return [`path ${t.dim} => ${show(t.body)}`, LEVEL.binder];
      // Glue, as the source writes it; a glue term without its type, which
      // the place it is checked at gives.
      case "Glue":
        return atom(`Glue(${[show(t.base), ...t.system.map(piece => onFace(piece.face, [show(piece.type), show(piece.equiv)]))].join(", ")})`);
      case "GlueTerm":
        return atom(`glue(${[show(t.base), ...t.system.map(part => onFace(part.face, [show(part.term)]))].join(", ")})`);
      case "Unglue": return atom(`unglue(${show(t.value)})`);
      default: return fallback(t);
    }
  }
  return show(term);
}
