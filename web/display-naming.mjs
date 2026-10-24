import { termBinders } from "./translator/term-shape.mjs";
import { displayFreeNames } from "./translator/display-names.mjs";
import { betaReduce as reduceRedexes, substituteDimension, substituteTerm } from "./translator/core.mjs";
import { localName, numberedName, stem } from "./translator/names.mjs";

// How a display names a term (web/README.md, "Displaying terms").
//
// Source text and kernel notation show binders, variables, dimensions and
// the labels of definitions, types and constructors in one namespace, as the
// source reads them. The rule: in the text, every name means what the term
// means by it. No binder captures a name it does not bind, and two things
// the term tells apart never read alike where both are in scope.
//
// Source text is named in four passes, in this order (forSource):
//  1. explicitBinders writes into the term every binder the printer would
//     otherwise have to invent: a folded motive, as a function of the domain
//     its type gives, a clause's arguments and dimensions, an eliminator
//     written as a function. Their names are new, settled below.
//  2. apartFromDimensions shows a definition named as a dimension of the
//     term or of its context by its value: no source spelling tells the two
//     apart, and a dimension the context names keeps its name.
//  3. displayTerm names every term and level binder apart from the labels
//     and dimensions the term shows and from the variables in its scope.
//  4. readableDimensions names the dimensions decoding left unnamed apart
//     from every name shown.
// The printer, sourceText, then chooses no name. A pass that adds what can
// print a name runs before 3 and 4: added after them, it put printed names
// under binders already named, a capture #310's review found again for each
// kind of binder.
//
// Kernel notation (cubicalText) adds no binder, and names its binders as it
// prints, since the views spell kernel variables by their source names; it
// keeps them apart from the labels a body shows (labelsShown) and shows a
// definition named as a dimension (dimensionNames) by its kernel name.

const namedBinders = new Set(["Var", ...termBinders]);

// For messages only: reduce beta-redexes, within a budget, and give generated
// names back their source stems (`A3` → `A`, `native10` → `x`) where no two
// names would clash. The result is never checked or stored.
// 3. This is where a display's names are settled, apart from every label
// and dimension the term shows; readableDimensions settles its dimensions
// after it. Whatever adds to the term what can print a name does so before
// both, as explicitBinders does (see the head of this module).
// `names` maps free variables to the names they show, where the caller knows
// their source names, as an inspection does: a stem cannot tell the source's
// x1 (x1_4) from x1_ (x1_4 too). Every other name keeps apart from those.
export function displayTerm(term, budget = 256, names = new Map()) {
  const shown = betaReduce(term, budget);
  return scopedNames(shown, names) ?? globalNames(shown, names);
}

// Dimensions a message has no source name for, bound or free, which decoding
// calls d0, d1, …: renamed together in several terms, after their display
// names are settled, to i, j, k, … (then i1, j1, …), names none of them
// shows: not a variable's, a dimension's, or a definition's without its
// module. The terms are shared graphs, so each node is visited and copied
// once, and sharing is kept.
export function readableDimensions(terms) {
  const used = new Set(), seen = new WeakSet();
  const visit = t => {
    if (typeof t === "string") {
      const literal = /^(.+):[01]$/.exec(t);
      if (literal) used.add(literal[1]);
      return;
    }
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    if (typeof t.dim === "string") used.add(t.dim);
    // Every name the printer shows: variables, definitions and constructors,
    // and declared types, which a sort or an eliminator names by signature.
    for (const name of [t.name, t.signature])
      if (typeof name === "string") {
        used.add(name);
        used.add(localName(name));
      }
    Object.values(t).forEach(visit);
  };
  terms.forEach(visit);
  const unnamed = [...used].filter(name => /^d[0-9]+_*$/.test(name))
    .sort((a, b) => parseInt(a.slice(1)) - parseInt(b.slice(1)) || a.length - b.length);
  if (!unnamed.length) return terms;
  const names = (function* () {
    for (let round = 0; ; round++)
      for (const letter of "ijklmn") {
        const name = round ? `${letter}${round}` : letter;
        if (!used.has(name)) yield name;
      }
  })();
  const renaming = new Map(unnamed.map(name => [name, names.next().value]));
  const copies = new WeakMap();
  const rename = t => {
    if (typeof t === "string") {
      const literal = /^(.+):([01])$/.exec(t);
      return literal && renaming.has(literal[1]) ? `${renaming.get(literal[1])}:${literal[2]}` : t;
    }
    if (!t || typeof t !== "object") return t;
    if (copies.has(t)) return copies.get(t);
    const copy = Array.isArray(t) ? [] : {};
    copies.set(t, copy);
    for (const [key, value] of Object.entries(t)) copy[key] = rename(value);
    if (!Array.isArray(t) && typeof t.dim === "string" && renaming.has(t.dim)) copy.dim = renaming.get(t.dim);
    return copy;
  };
  return terms.map(rename);
}

// Beta-reduce within a budget of substitutions, keeping every name.
export function betaReduce(term, budget = 256) {
  const reduced = new WeakMap();
  const beta = t => {
    if (!t || typeof t !== "object") return t;
    if (reduced.has(t)) return reduced.get(t);
    let result = Array.isArray(t) ? t.map(beta) : Object.fromEntries(Object.entries(t).map(([key, value]) => [key, beta(value)]));
    while (result.tag === "App" && result.fn?.tag === "Lam" && budget-- > 0)
      result = beta(substituteTerm(result.fn.body, result.fn.name, result.arg));
    reduced.set(t, result);
    return result;
  };
  return beta(term);
}

// The names a term prints without binding them: a declared type or an
// eliminator by its signature, a constructor, and a definition, each as the
// printer labels it, without its module. A binder must not take one, and no
// variable is shown by a stem that is one.
export function printedLabels(term) {
  const labels = new Set(), seen = new WeakSet();
  const visit = t => {
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    const label = t.tag === "Sort" || t.tag === "Elim" ? t.signature : t.tag === "Con" || t.tag === "DefRef" ? t.name : null;
    if (typeof label === "string") labels.add(localName(label));
    Object.values(t).forEach(visit);
  };
  visit(term);
  return labels;
}

// The dimensions a term names, bound or free: a variable shown by one of
// these names would read as the dimension where both are in scope, and
// readableDimensions renames only the dimensions decoding left unnamed.
export function dimensionNames(term) {
  const names = new Set(), seen = new WeakSet();
  const visit = t => {
    if (typeof t === "string") {
      const literal = /^(.+):[01]$/.exec(t);
      if (literal) names.add(literal[1]);
      return;
    }
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    if (typeof t.dim === "string") names.add(t.dim);
    Object.values(t).forEach(visit);
  };
  visit(term);
  return names;
}

// Each binder shows its stem, n for n11, unless a binder around it already
// shows that name or its body uses the name for another variable; then it
// shows the stem numbered from 1, n1. The copy is a tree, so a term that
// shares much structure is left to globalNames.
// A name shown as a label would read as that label: a variable a term shows
// by a declared type's, a constructor's or a definition's name is numbered
// instead, apart from every other name shown.
function apartFromLabels(shownAs, labels) {
  const taken = new Set([...shownAs.keys(), ...shownAs.values(), ...labels]);
  for (const [name, shown] of shownAs) {
    if (!labels.has(shown)) continue;
    let index = 1, renamed;
    do renamed = numberedName(stem(name), index++); while (taken.has(renamed));
    taken.add(renamed);
    shownAs.set(name, renamed);
  }
  return shownAs;
}

function scopedNames(term, names, limit = 2000) {
  let work = 0;
  const free = displayFreeNames();
  const go = (t, shownAs, inScope) => {
    if (++work > limit) throw scopedNames;
    if (!t || typeof t !== "object") return t;
    if (Array.isArray(t)) return t.map(item => go(item, shownAs, inScope));
    if (t.tag === "Var") return shownAs.has(t.name) ? { ...t, name: shownAs.get(t.name) } : t;
    const result = {};
    if (termBinders.has(t.tag) && typeof t.name === "string") {
      const others = new Set([...free(t.body)].filter(name => name !== t.name).map(name => shownAs.get(name) ?? name));
      const taken = candidate => inScope.has(candidate) || others.has(candidate);
      let name = stem(t.name);
      for (let index = 1; taken(name); index++) name = numberedName(stem(t.name), index);
      for (const [key, value] of Object.entries(t))
        result[key] = key === "body" ? go(value, new Map(shownAs).set(t.name, name), new Set(inScope).add(name))
          : key === "name" ? name : go(value, shownAs, inScope);
      return result;
    }
    for (const [key, value] of Object.entries(t)) result[key] = go(value, shownAs, inScope);
    return result;
  };
  // Free variables, such as a goal's context, show their stems when no two
  // share one, and the names given them as given; binders then avoid those
  // names.
  const outer = [...free(term)], count = new Map(), labels = new Set([...printedLabels(term), ...dimensionNames(term)]);
  const given = outer.filter(name => names.has(name)), loose = outer.filter(name => !names.has(name));
  const avoid = new Set([...labels, ...given.map(name => names.get(name))]);
  for (const name of loose) count.set(stem(name), (count.get(stem(name)) ?? 0) + 1);
  const shownAs = apartFromLabels(new Map(loose.map(name => [name,
    count.get(stem(name)) === 1 && !(outer.includes(stem(name)) && stem(name) !== name) && !avoid.has(stem(name))
      ? stem(name) : name])), avoid);
  for (const name of given) shownAs.set(name, names.get(name));
  try { return go(term, shownAs, new Set([...shownAs.values(), ...labels])); }
  catch (error) { if (error === scopedNames) return null; throw error; }
}

// Every generated name whose stem no other name shares shows its stem, and a
// free variable given a name shows that name. Names are renamed wherever
// they occur, so a name some binder binds is never given one: two binders
// given the same name could capture each other's variables.
function globalNames(shown, given) {
  const names = new Set(), bound = new Set(), seen = new WeakSet();
  const collect = t => {
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    if (namedBinders.has(t.tag) && typeof t.name === "string") {
      names.add(t.name);
      if (t.tag !== "Var") bound.add(t.name);
    }
    Object.values(t).forEach(collect);
  };
  collect(shown);
  const fixed = new Set([...names].filter(name => given.has(name) && !bound.has(name))), loose = [...names].filter(name => !fixed.has(name));
  const count = new Map(), labels = new Set([...printedLabels(shown), ...dimensionNames(shown)]), avoid = new Set([...labels, ...[...fixed].map(name => given.get(name))]);
  for (const name of loose) count.set(stem(name), (count.get(stem(name)) ?? 0) + 1);
  const renames = apartFromLabels(new Map(loose.map(name => [name, count.get(stem(name)) === 1
    && !(names.has(stem(name)) && stem(name) !== name) && !avoid.has(stem(name)) ? stem(name) : name])), avoid);
  for (const name of fixed) renames.set(name, given.get(name));
  const rename = name => renames.get(name) ?? name;
  const renamed = new WeakMap();
  const apply = t => {
    if (!t || typeof t !== "object") return t;
    if (renamed.has(t)) return renamed.get(t);
    const result = Array.isArray(t) ? t.map(apply) : Object.fromEntries(Object.entries(t).map(([key, value]) => [key, apply(value)]));
    if (namedBinders.has(t.tag) && typeof t.name === "string") result.name = rename(t.name);
    renamed.set(t, result);
    return result;
  };
  return apply(shown);
}

// 1. Every binder the printer would otherwise invent, written into the term
// under a new name that displayTerm and readableDimensions settle:
//  - a motive that is no function, as a folded normal form keeps one that is
//    a definition (docs/roadmaps/runtime/folded-normal-forms.md), is
//    λ (z : D). M(z), D the domain M's type gives where it can be read
//    (motiveDomain), so that the eliminator can print typed;
//  - a clause with fewer arguments, hypotheses or dimensions than its
//    constructor takes, as evaluation eta-reduces one and a folded normal
//    form keeps one that is a definition, is applied to new ones, and so are
//    a sum's clauses and motive;
//  - an eliminator written where no function is applied to it is the
//    function that applies it, λ (x : D). e(x).
// Each change is an eta-expansion: the term says what it said. `definitions`
// gives definitions' decoded types and values, `symbols` a declared type's
// constructors as the printer reads them (signatureDisplay).
export function explicitBinders(term, { definitions, symbols = {} }) {
  // Every name the term has, a dimension's too: a new binder is none of them.
  const used = new Set(), seen = new WeakSet();
  const collect = t => {
    if (typeof t === "string") {
      const literal = /^(.+):[01]$/.exec(t);
      if (literal) used.add(literal[1]);
      return;
    }
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    if (typeof t.name === "string") used.add(t.name);
    if (typeof t.dim === "string") used.add(t.dim);
    Object.values(t).forEach(collect);
  };
  collect(term);
  // A new variable is its stem where no name of the term is, and numbered
  // from 1 otherwise: displayTerm shows it by its stem where it can, and a
  // display too large for scoped names (globalNames) shows it as it is. A
  // new dimension, d1 and on, is named as decoding's unnamed dimensions are.
  const fresh = stem => {
    let name = stem === "d" ? "d1" : stem;
    for (let n = 1; used.has(name); n++) name = `${stem}${n}`;
    used.add(name);
    return name;
  };
  const domain = motiveDomain(definitions);
  const applied = (fn, stem, of = null) => {
    if (!fn || fn.tag === "Lam") return fn;
    const name = fresh(stem);
    return { tag: "Lam", name, domain: of, body: { tag: "App", fn, arg: { tag: "Var", name } } };
  };
  // A clause taking each of `takes` in turn: a variable of the stem given,
  // or a dimension.
  const clause = (body, takes) => {
    if (!takes.length || !body) return body;
    const [take, ...rest] = takes;
    if (take === "dimension") {
      if (body.tag === "PLam") return { ...body, body: clause(body.body, rest) };
      const dim = fresh("d");
      return { tag: "PLam", dim, family: null, body: clause({ tag: "PApp", path: body, arg: [[`${dim}:1`]] }, rest) };
    }
    if (body.tag === "Lam") return { ...body, body: clause(body.body, rest) };
    const name = fresh(take);
    return { tag: "Lam", name, domain: null, body: clause({ tag: "App", fn: body, arg: { tag: "Var", name } }, rest) };
  };
  // The source Nat's induction names its predecessor k and its hypothesis
  // h; any other declared type's clause names x and ih.
  const constructorTakes = ({ data, positions, dimensions }, signature) => {
    const [argument, result] = signature === "unat__UNat" ? ["k", "h"] : ["x", "ih"];
    return [...Array(data + positions).fill(argument), ...Array(positions).fill(result), ...Array(dimensions).fill("dimension")];
  };
  // Shared syntax is expanded once for each place it can occur in: as the
  // function an application applies, or anywhere else.
  const memo = [new WeakMap(), new WeakMap()];
  const go = (t, applying = false) => {
    if (!t || typeof t !== "object") return t;
    const table = memo[applying ? 1 : 0];
    if (table.has(t)) return table.get(t);
    let result = t;
    for (const [key, value] of Object.entries(t)) {
      const changed = go(value, t.tag === "App" && key === "fn");
      if (changed !== value) {
        if (result === t) result = Array.isArray(t) ? [...t] : { ...t };
        result[key] = changed;
      }
    }
    if (result.tag === "SumRec")
      result = { ...result, motive: applied(result.motive, "z"), left: applied(result.left, "a"), right: applied(result.right, "b") };
    if (result.tag === "Elim") {
      const motive = result.motive?.tag === "Lam" || !result.motive ? result.motive : applied(result.motive, "z", domain(result.motive));
      const constructors = symbols[result.signature]?.constructors;
      const clauses = constructors?.length === result.clauses?.length
        ? result.clauses.map((body, index) => clause(body, constructorTakes(constructors[index], result.signature))) : result.clauses;
      result = { ...result, motive, clauses };
      if (!applying) {
        const of = motive?.tag === "Lam" && motive.domain ? motive.domain
          : symbols[result.signature]?.slots?.length === 0 ? { tag: "Sort", signature: result.signature, parameters: [], levels: [] } : null;
        result = applied(result, result.signature === "unat__UNat" ? "n" : "x", of);
      }
    }
    table.set(t, result);
    return result;
  };
  return go(term);
}

// The domain of a motive, as the type of the definition at its root gives
// it after the motive's spine: `definitions` gives definitions' decoded types
// and values. A spine applies, projects or applies to a dimension the term at
// its root; each application substitutes an argument or a level, a first
// projection reads a pair type's first component, a second one its second
// with the first substituted, and a path application a path type's family
// at the point. A type with a definition at its root, as an alias of a
// function type, or a pair's component, has that definition's value there,
// reduced, until it is a type former or no definition is at its root.
export function motiveDomain(definitions) {
  const root = node => node.fn ?? node.pair ?? node.path;
  const spines = new Set(["App", "LApp", "Fst", "Snd", "PApp"]);
  const formers = new Set(["Pi", "LPi", "Sigma", "Path"]);
  const exposed = type => {
    for (let unfoldings = 0; type; unfoldings++) {
      // A substitution can leave a redex at the root, a function of types
      // applied: reduced first, as after each unfolding.
      type = reduceRedexes(type);
      if (formers.has(type.tag) || unfoldings >= 16) break;
      let head = type;
      while (spines.has(head.tag)) head = root(head);
      const value = head.tag === "DefRef" ? definitions.value(head.name) : null;
      if (!value) break;
      const rooted = node => !spines.has(node.tag) ? value
        : { ...node, [node.fn ? "fn" : node.pair ? "pair" : "path"]: rooted(root(node)) };
      type = rooted(type);
    }
    return type;
  };
  return motive => {
    if (motive?.tag === "Lam") return motive.domain;
    const spine = [];
    let head = motive;
    while (spines.has(head?.tag)) { spine.unshift(head); head = root(head); }
    let type = head?.tag === "DefRef" ? definitions.type(head.name) : null;
    for (const node of spine) {
      type = exposed(type);
      if (type?.tag !== { App: "Pi", LApp: "LPi", Fst: "Sigma", Snd: "Sigma", PApp: "Path" }[node.tag]) return null;
      type = node.tag === "App" ? substituteTerm(type.body, type.name, node.arg)
        : node.tag === "LApp" ? substituteTerm(type.body, type.name, node.level)
        : node.tag === "Fst" ? type.domain
        : node.tag === "Snd" ? substituteTerm(type.body, type.name, { tag: "Fst", pair: node.pair })
        : substituteDimension(type.family, type.dim, node.arg);
    }
    type = exposed(type);
    return type?.tag === "Pi" ? type.domain : null;
  };
}

// A definition shown by a dimension's name, as a definition i where a term
// names a dimension i, would read as that dimension; no source spelling
// qualifies it, and a dimension the context names keeps its name. Such a
// definition is shown by its value, which it equals by unfolding. This runs
// after explicitBinders: a recovered domain can bring the definition in. `definitions` gives a definition's decoded value and its label;
// `ambient` names the dimensions of the context the term is shown in, which
// the term need not use.
export function apartFromDimensions(term, definitions, ambient = []) {
  const dimensions = new Set(ambient), seen = new WeakSet();
  const collect = t => {
    if (typeof t === "string") {
      const literal = /^(.+):[01]$/.exec(t);
      if (literal) dimensions.add(literal[1]);
      return;
    }
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    if (typeof t.dim === "string") dimensions.add(t.dim);
    Object.values(t).forEach(collect);
  };
  collect(term);
  if (!dimensions.size) return term;
  const shown = new WeakMap();
  const go = (t, depth = 0) => {
    if (!t || typeof t !== "object") return t;
    if (shown.has(t)) return shown.get(t);
    let result = t;
    if (t.tag === "DefRef" && dimensions.has(definitions.label(t.name)) && depth < 16) {
      const value = definitions.value(t.name);
      if (value) result = go(value, depth + 1);
    } else {
      for (const [key, value] of Object.entries(t)) {
        const changed = go(value, depth);
        if (changed !== value) {
          if (result === t) result = Array.isArray(t) ? [...t] : { ...t };
          result[key] = changed;
        }
      }
      // A value put where the definition was applied, projected or applied
      // to a dimension, as explicitBinders applies a clause that is one, is
      // a redex the source cannot check: (path i => loop @ ~i) @ j. Reduced.
      const root = { App: "fn", LApp: "fn", Fst: "pair", Snd: "pair", PApp: "path" }[t.tag];
      if (root && result[root] !== t[root] && t[root]?.tag === "DefRef") result = reduceRedexes(result);
    }
    shown.set(t, result);
    return result;
  };
  return go(term);
}

// The labels a term's definitions, types and constructors show, as `label`
// spells a kernel name: kernel notation keeps a binder apart from those its
// body shows. Memoized per node.
export function labelsShown(label) {
  const memo = new WeakMap(), empty = new Set();
  const scan = value => {
    if (!value || typeof value !== "object") return empty;
    if (memo.has(value)) return memo.get(value);
    const names = new Set();
    memo.set(value, names);
    if (value.tag === "DefRef") names.add(label(value.name));
    else if (value.tag === "Sort") names.add(label(value.signature));
    else if (value.tag === "Con" && value.name) names.add(value.name);
    for (const child of Object.values(value)) for (const name of scan(child)) names.add(name);
    return names;
  };
  return scan;
}

// Terms named for source text, in one naming, by the four passes above.
// `definitions` gives definitions' decoded types and values and the labels
// the printer shows them by; `symbols` a declared type's constructors;
// `names` the names free variables show; `dimensions` the dimensions of the
// context the terms are shown in; `reduce` the display's beta budget.
export function forSource(terms, { definitions, symbols, names = new Map(), dimensions = [], reduce = 256 }) {
  const explicit = terms.map(term => apartFromDimensions(explicitBinders(term, { definitions, symbols }), definitions, dimensions));
  return readableDimensions(displayTerm(explicit, reduce, names));
}

