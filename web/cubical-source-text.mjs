import { displayFreeNames } from "./translator/display-names.mjs";
import { termBinders, dimensionScope } from "./translator/term-shape.mjs";
import { cubicalText } from "./cubical-notation.mjs";
import { renameLevel, universeText } from "./cubical-levels.mjs";
import { localName } from "./translator/names.mjs";
import {numeralValue} from "./translator/numerals.mjs";
import {binaryDigits as binary, parsedLiteral} from "./translator/numeral-printing.mjs";

// Print a checked term in Cubist source syntax, for messages and the command
// line: `A -> B`, `forall x : A. B`, `A and B`, `exists x : A. B`, `A or B`,
// `x = y`, `p @ i`, `fun (x, y : A) => b`, `f(a, b)`, `f{{U0, A}}(a)`, `(a, b)`, `p.1`, `left(a)`, `tt`,
// numerals and binary numerals, and `+`, `*`, `<`, `<=` for the arithmetic
// library. Forms without a source spelling fall back to the inspector's
// notation. Parentheses follow the
// parser's precedence: binders < -> < or < and < = < + < * < @; `->`, `or` and
// `and` group to the right, `+` and `*` to the left.
const LEVEL = { binder: 0, arrow: 1, or: 2, and: 3, compare: 4, plus: 5, times: 6, power: 6.5, at: 7, atom: 9 };
const infix = { add: ["+", LEVEL.plus], mul: ["*", LEVEL.times], le: ["<=", LEVEL.compare], isLt: ["<", LEVEL.compare] };
const arithmetic = /^unat__(add|mul|le|isLt)$/;
// A notation's operator's level (L2.10b).
const operatorLevel = { "+": LEVEL.plus, "-": LEVEL.plus, "*": LEVEL.times, "/": LEVEL.times, "^": LEVEL.power,
  "<": LEVEL.compare, "<=": LEVEL.compare };
// `symbols` maps kernel names to their display names, as for cubicalText.
// Without an entry, a definition shows its name without the module prefix.
// `context.selection` names the notation selected where the text is read
// (L2.10d): an operation prints with its notation's operator only where
// that notation is selected, and is qualified, as nat.(x + y), elsewhere,
// even where nothing is selected (L2.10j).
// The printer chooses no name. A display names its term first
// (display-naming.mjs, forSource): every binder the text shows is in the
// term, a folded motive's and an eta-reduced clause's too, named apart from
// what it would capture. A form the term does not spell out, as a clause
// with fewer binders than its constructor takes in a term not named so,
// prints in kernel notation instead of under invented names: inventing them
// here, where names are settled, was the source of #310's captures
// (web/README.md, "Displaying terms").
export function sourceText(term, symbols = {}, limit = 4000, context = {}) {
  let budget = limit, selection = context.selection ?? null, selectionIdentity = context.selectionIdentity;
  const label = binding => symbols[binding]?.name
    ?? localName(binding);
  // Terms share subterms, so each scan visits a node once.
  const free = displayFreeNames();
  const mentions = (term, variable) => free(term).has(variable);
  const numeral = numeralValue;
  // A dimension occurs in a term through interval literals `i:1` and `i:0`.
  const varies = (t, dim, seen = new Set()) => {
    if (typeof t === "string") return t === `${dim}:0` || t === `${dim}:1`;
    if (!t || typeof t !== "object" || seen.has(t)) return false;
    seen.add(t);
    return Object.values(t).some(child => varies(child, dim, seen));
  };
  // Interval formulas are disjunctions of conjunctions of literals; `i:0` is
  // the reversed coordinate. They print in the source's notation: ~i, i & j
  // and i | j, where & binds tighter than |, and both tighter than @.
  const literal = text => text.endsWith(":0") ? `~${text.slice(0, -2)}` : text.replace(/:1$/, "");
  const conjunction = clause => clause.length ? clause.map(literal).join(" & ") : "1";
  const interval = value => value.length ? value.map(conjunction).join(" | ") : "0";
  // A face formula is a disjunction of conjunctions too, of equations `i:0`.
  // A Glue piece or a glue value on one equation is face(i, 0, …), and on any
  // other face face_when(on(i, 0) and on(j, 1) or …, …).
  const equation = text => `${text.slice(0, text.lastIndexOf(":"))}, ${text.slice(-1)}`;
  const onFace = (formula, parts) => formula.length === 1 && formula[0].length === 1
    ? `face(${equation(formula[0][0])}, ${parts.join(", ")})`
    : `face_when(${formula.length ? formula.map(clause => clause.length ? clause.map(text => `on(${equation(text)})`).join(" and ") : "1").join(" or ") : "0"}, ${parts.join(", ")})`;
  // A natural number reads back where a notation is selected, and as nat's
  // where none is; a binary number, where binary is (L2.10j).
  const natural = n => {
    const unary = symbols.unat__UNat;
    const own = !unary && selection === "unat" || unary?.printing?.some(entry => entry.identityNumeral
      && entry.notation === selection && (selectionIdentity === undefined || entry.identity === selectionIdentity));
    return atom(own ? String(n) : `unat.(${n})`);
  };
  const bits = text => atom(selection === "binary" ? text : `binary.(${text})`);
  // The rebuilt binary carrier prints decimal magnitudes directly from its
  // bits. Use a notation known to read this exact parser, including aliases;
  // without such a reader, retain the constructor spelling. BigInt here is
  // display arithmetic only: the checked term remains ordinary constructors.
  const binaryNatural = t => {
    const readings = symbols.bnat_notation__bnat_literal?.printing;
    const reading = readings?.find(entry => entry.literal && entry.notation === selection)
      ?? readings?.find(entry => entry.literal);
    if (!reading) return null;
    const digits = binary(t, "bnat__BNat", "bnat__BPositive");
    if (digits === null) return null;
    const text = BigInt(digits).toString(10);
    return atom(selection === reading.notation ? text : `${reading.notation}.(${text})`);
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
  // Whether `from` can be shown as `to` throughout a term: `to` is free in
  // it nowhere, and no binder or dimension named `to` in it has `from` free
  // in its scope, which it would capture. A binder's scope is the children
  // it binds in: a Pi's domain is outside it, and a binder of `from` hides
  // `from` only there. Induction's `as k` shows the motive's variable by the
  // predecessor's name only so.
  const renamable = (term, from, to) => {
    if (from === to) return true;
    if (mentions(term, to)) return false;
    const seen = new WeakSet();
    const capture = t => {
      if (!t || typeof t !== "object" || seen.has(t)) return false;
      seen.add(t);
      const binder = termBinders.has(t.tag) ? { name: t.name, keys: ["body"] }
        : dimensionScope.has(t.tag) ? { name: t.dim, keys: dimensionScope.get(t.tag) } : null;
      return Object.entries(t).some(([key, child]) => !binder?.keys.includes(key) ? capture(child)
        : termBinders.has(t.tag) && binder.name === from ? false
        : binder.name === to && mentions(child, from) || capture(child));
    };
    return !capture(term);
  };
  const show = t => print(t)[0];
  const sub = (t, needed) => { const [text, level] = print(t); return level < needed ? `(${text})` : text; };
  // An operation printed with its notation's operator, at its level: ^
  // groups to the right, a comparison not at all, the others to the left.
  // Each operand is read in the view its rule gives it, as nat.(n) in
  // x ^ nat.(n), and otherwise in the notation `own` (L2.10b).
  const infixText = (printing, [left, right], own) => {
    const level = operatorLevel[printing.operator], recipe = printing.recipe ?? {};
    const levels = printing.operator === "^" ? [level + 1, level] : [level === LEVEL.compare ? level + 1 : level, level + 1];
    const operand = (arg, view, at) => {
      const saved = selection, savedIdentity = selectionIdentity;
      selection = view ?? own;
      selectionIdentity = view ? undefined : printing.identity;
      try { return sub(arg, at); } finally { selection = saved; selectionIdentity = savedIdentity; }
    };
    return [`${operand(left, recipe.left, levels[0])} ${printing.operator} ${operand(right, recipe.right, levels[1])}`, level];
  };
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
  // its hypotheses after with: `cons(head, tail) with ih => …`.
  const declaredMatch = (elim, value) => {
    const constructors = symbols[elim.signature]?.constructors, motive = elim.motive;
    if (!constructors || constructors.length !== elim.clauses?.length || motive?.tag !== "Lam") return null;
    const clauses = [];
    for (const [c, clause] of elim.clauses.entries()) {
      const { name, data, positions, dimensions, order } = constructors[c];
      const args = [], results = [], dims = [];
      let body = clause;
      // A clause binds its constructor's data and positions, a recursive
      // result for each position, then its dimensions; spelledOut
      // spells out a clause that binds fewer (display-naming.mjs).
      const take = into => {
        if (body?.tag !== "Lam") return false;
        into.push(body.name);
        body = body.body;
        return true;
      };
      for (let i = 0; i < data + positions; i++) if (!take(args)) return null;
      for (let i = 0; i < positions; i++) if (!take(results)) return null;
      for (let i = 0; i < dimensions; i++) {
        if (body?.tag !== "PLam") return null;
        dims.push(body.dim);
        body = body.body;
      }
      const fields = order ? order.map((_, sourceIndex) => args[order.indexOf(sourceIndex)]) : args;
      clauses.push({ name, args: fields, results, dims, body });
    }
    // `as z` is written only where the return type uses z, as the linter asks.
    const named = mentions(motive.body, motive.name);
    const hypotheses = clause => clause.results.some(result => mentions(clause.body, result));
    const shown = clauses.map(clause => {
      const { name, args, results, dims, body } = clause;
      return `${name}${args.length ? `(${args.join(", ")})` : ""}${dims.map(dim => ` @ ${dim}`).join("")}`
        + `${hypotheses(clause) ? ` with ${results.join(", ")}` : ""} => `
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
      // A part an evaluation did not compute, or stopped at (evaluation.mjs).
      case "Marker": return atom(t.text);
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
        // A binder of no domain, as spelledOut gives a function whose
        // domain no type it reads gives, stands alone: fun x => body, its
        // type given by where it is checked.
        if (!t.domain) return [`fun ${t.name} => ${under(t.name, () => show(t.body))}`, LEVEL.binder];
        // fun (x, y : A, z : B) => body, each domain in the scope of the
        // binders before it
        const groups = [], names = [];
        let body = t;
        while (body.tag === "Lam" && body.domain) {
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
      // in the shape its `induction` spelling reads, `shared` the name the
      // application case below found for both, which neither captures.
      case "NatInduction": {
        const { motive, step, shared: k } = t, h = step.body.name;
        const type = under(motive.name, () => renaming(motive.name, k, () => show(motive.body)));
        const successor = under([step.name, h], () => renaming(step.name, k, () => show(step.body.body)));
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
      // it, fun (x : T) => match x …, which spelledOut writes into the
      // term; one that reaches the printer unwritten is shown as it is.
      case "Elim": return fallback(t);
      case "App": case "LApp": {
        const number=numeral(t);
        if(number!==null)return natural(number);
        const digits=binary(t);
        if(digits)return bits(digits);
        const decimal=binaryNatural(t);
        if(decimal)return decimal;
        // The standard source Nat's eliminator has the existing induction
        // spelling, where `as k` binds the motive's variable and the
        // predecessor as one: only where the motive shows the predecessor's
        // name for nothing else. Otherwise it prints as the declared match.
        const elim=t.tag==="App"&&t.fn.tag==="Elim"?t.fn:null,step=elim?.clauses?.[1];
        if(elim?.signature==="unat__UNat"&&elim.clauses.length===2&&elim.motive?.tag==="Lam"&&step?.tag==="Lam"&&step.body?.tag==="Lam") {
          // The predecessor's name, where the motive takes it; else the
          // motive's, where the successor clause takes it.
          const shared=renamable(elim.motive.body,elim.motive.name,step.name)?step.name
            :renamable(step.body,step.name,elim.motive.name)?elim.motive.name:null;
          if(shared)return print({tag:"NatInduction",motive:elim.motive,zero:elim.clauses[0],step,value:t.arg,shared});
        }
        if(t.tag==="App"&&t.fn.tag==="Elim"){const text=declaredMatch(t.fn,t.arg);if(text)return [text,LEVEL.binder];}
        // An instantiation is an application to a universe.
        const args = [];
        let head = t;
        while (head.tag === "App" || head.tag === "LApp") { args.unshift(head.tag === "App" ? head.arg : { tag: "U", level: head.level }); head = head.fn; }
        // An eliminator applied to its value and more prints as the match
        // or induction on the value, applied to the rest: its function alone
        // would be written untyped where no type reaches it.
        if (head.tag === "Elim" && args.length > 1) {
          const [text, level] = print({ tag: "App", fn: head, arg: args[0] });
          return atom(`${level < LEVEL.atom ? `(${text})` : text}(${args.slice(1).map(show).join(", ")})`);
        }
        // The notation that prints this function: the selected one's
        // entry, or the first declared (L2.10d).
        const entries = head.tag === "DefRef" ? symbols[head.name]?.printing : undefined;
        const printing = entries?.find(entry => entry.notation === selection) ?? entries?.[0];
        // A notation's operation, in its notation where it is selected, and
        // qualified elsewhere; its operands are read in it.
        if (printing?.operator && !printing.model && args.length === 2) {
          const [text, level] = infixText(printing, args, printing.notation);
          const own = selection === printing.notation;
          return own ? [text, level] : atom(`${printing.notation}.(${text})`);
        }
        // A literal read from its characters prints as it was written, in
        // its notation (L2.10c): parsed_value(parse(lexeme), tt).
        const parsed = parsedLiteral(t, symbols, selection);
        if (parsed) return atom(selection === parsed.reading.notation ? parsed.text
          : `${parsed.reading.notation}.(${parsed.text})`);
        // A numeral rule's application to a numeral, as int(3, 0), prints as
        // the numeral where its notation is selected.
        if (printing?.numeral && selection === printing.notation && args.length >= printing.numeral.length) {
          // Each place of the numeral holds the same one, and each fixed
          // argument its own.
          const values = args.slice(args.length - printing.numeral.length).map(numeral);
          const value = values[printing.numeral.indexOf(null)];
          if (values.every((v, k) => v !== null && v === (printing.numeral[k] ?? value)))
            return atom(String(value));
        }
        const operator = head.tag === "DefRef" && args.length === 2 && !printing && arithmetic.exec(head.name)?.[1];
        if (operator) {
          const [symbol, level] = infix[operator], left = level === LEVEL.compare ? level + 1 : level;
          const saved = selection;
          selection = "unat";
          const text = `${sub(args[0], left)} ${symbol} ${sub(args[1], level + 1)}`;
          selection = saved;
          return selection === "unat" ? [text, level] : atom(`unat.(${text})`);
        }
        // A theory's projection of a model is m.f, and applied further,
        // m.f(x, y), as the source writes it (L2.4).
        const projection = head.tag === "DefRef" ? symbols[head.name]?.projection : undefined;
        if (projection) {
          const at = (symbols[head.name].assumed ?? 0) + (symbols[head.name].implicit ?? 0), model = args[at];
          if (model) {
            const rest = args.slice(at + 1);
            // Where the model is selected, its operation prints with its
            // notation's operator (L2.10d).
            if (printing?.operator && rest.length === 2 && selection !== null && selection === show(model))
              return infixText(printing, rest, selection);
            return atom(`${sub(model, LEVEL.atom)}.${projection}${rest.length ? `(${rest.map(show).join(", ")})` : ""}`);
          }
        }
        // A definition's implicit arguments are in double braces, as a call
        // writes them, after the assumptions applied to it:
        // append{{U0, Nat}}(xs, ys).
        const implicit = head.tag === "DefRef" ? symbols[head.name]?.implicit : 0;
        if (implicit) {
          const assumed = symbols[head.name].assumed ?? 0, braced = args.slice(assumed, assumed + implicit);
          const rest = [...args.slice(0, assumed), ...args.slice(assumed + implicit)];
          if (braced.length)
            return atom(`${sub(head, LEVEL.atom)}{{${braced.map(show).join(", ")}}}${rest.length ? `(${rest.map(show).join(", ")})` : ""}`);
        }
        const order = head.tag === "Con" ? symbols[head.sort?.signature]?.constructors?.[head.index]?.order : null;
        const sourceArgs = order && args.length >= order.length
          ? [...order.map((_, sourceIndex) => args[order.indexOf(sourceIndex)]), ...args.slice(order.length)] : args;
        return atom(`${sub(head, LEVEL.atom)}(${sourceArgs.map(show).join(", ")})`);
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
      // A projection of a pair as written: the pair has no type to be checked
      // at there, so it is given its own.
      case "Fst": case "Snd": {
        const pair = t.pair?.tag === "Pair" && t.pair.as ? `typed(${show(t.pair.as)}, ${show(t.pair)})` : sub(t.pair, LEVEL.atom);
        return atom(`${pair}.${t.tag === "Fst" ? 1 : 2}`);
      }
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
      case "Con": {
        const n=numeral(t);
        if(n!==null)return natural(n);
        const digits=binary(t);
        if(digits)return bits(digits);
        return binaryNatural(t) ?? (t.name ? atom(t.name) : fallback(t));
      }
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
      // A composition, as the source writes it: its family and each wall a
      // line along its dimension, the base between them.
      // A composition prints as its box (L2.8), as the source writes it.
      case "Comp": {
        const face = formula => formula.length ? formula.map(clause => clause.length
          ? clause.map(text => `${text.slice(0, text.lastIndexOf(":"))} = ${text.slice(-1)}`).join(" and ") : "1").join(" or ") : "0";
        const walls = t.system.map(tube => `on ${face(tube.face)} => ${show(tube.term)}; `).join("");
        return atom(`compose ${t.dim} in ${show(t.family)} from ${show(t.base)} { ${walls}}`);
      }
      default: return fallback(t);
    }
  }
  return show(term);
}
