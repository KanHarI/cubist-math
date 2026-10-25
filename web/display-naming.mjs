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
// Source text is named, once the display's beta reduction (betaReduce) has
// contracted its redexes on the kernel's syntax alone, before anything is
// spelled out, since a substitution cannot read a path clause spelled
// without its family, in four passes, in this order (forSource):
//  1. spelledOut writes into the terms what the text shows and the terms do
//     not spell out: every binder the printer would otherwise have to
//     invent (a folded motive, as a function of the domain its type gives, a
//     clause's arguments and dimensions, an eliminator written as a
//     function), and the one name induction's `as k` gives its motive's
//     variable and its predecessor. Each eliminator is spelled before its
//     parts, so that no substitution meets syntax already spelled out. What
//     it adds it spells out in turn, and its new names are apart from every
//     name of the terms.
//  2. displayTerm names every term and level binder apart from the labels
//     and dimensions the terms show and from the variables in its scope.
//  3. readableDimensions names the dimensions decoding left unnamed apart
//     from every name shown, the context's dimensions kept.
//  4. qualified marks a definition, type or constructor whose label the
//     text shows for a dimension, or for a variable whose name the caller
//     gives, all of which keep their names: the printer writes it
//     module::name, which nothing in scope shadows.
// The printer, sourceText, then chooses no name. A pass that adds what can
// print a name runs before 2 and 3, and spells out what it adds: added after
// the naming, or added unspelled, it put printed names under binders already
// named, a capture #310's and #311's reviews found for each kind of binder.
// A name clash that renaming cannot settle, where the other name is fixed,
// is settled by qualifying, not by unfolding the definition: an unfolding
// makes redexes, which must be contracted where the source cannot check
// them and kept where they are the term's own, and #312's reviews found the
// tracking of which is which wrong at every stage it passed through.
//
// Kernel notation (cubicalText) adds no binder, and names its binders as it
// prints, since the views spell kernel variables by their source names; it
// keeps them apart from the labels a body shows (labelsShown) and shows a
// definition named as a dimension (dimensionNames), or marked qualified, by
// its kernel name.

const namedBinders = new Set(["Var", ...termBinders]);

// The dimensions of the context a display shows its terms in, which every
// display is given, as a scope's Map or their names, [] where there are
// none: a definition labeled as one is not shown by its label. No display
// has a default. A default is some context's, and each display #311's
// reviews found wrong had been given another context's or none (web/README.md,
// "Displaying terms").
export function contextDimensions(dimensions) {
  if (dimensions instanceof Map) return [...dimensions.keys()];
  if (Array.isArray(dimensions) && dimensions.every(name => typeof name === "string")) return dimensions;
  throw new TypeError("A display is given the dimensions of the context it shows its terms in: a Map, their names, or [] for none.");
}

// For messages only: reduce beta-redexes, within a budget, and give generated
// names back their source stems (`A3` → `A`, `native10` → `x`) where no two
// names would clash. The result is never checked or stored. forSource
// reduces before it spells a term out, and gives this no budget.
// 2. This is where a display's names are settled, apart from every label
// and dimension the term shows; readableDimensions settles its dimensions
// after it. Whatever adds to the term what can print a name does so before
// both, as spelledOut does (see the head of this module).
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
// `pinned` names the dimensions of the context the terms are shown in: they
// keep their names, even one spelled as an unnamed one is, as d0.
export function readableDimensions(terms, pinned) {
  pinned = contextDimensions(pinned);
  const used = new Set(pinned), seen = new WeakSet();
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
  const fixed = new Set(pinned), unnamed = [...used].filter(name => /^d[0-9]+_*$/.test(name) && !fixed.has(name))
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

// A spine node, its root, and the value former it takes there.
const spine = { App: ["fn", "Lam"], LApp: ["fn", "LLam"], Fst: ["pair", "Pair"], Snd: ["pair", "Pair"], PApp: ["path", "PLam"] };
// One contraction of a spine node whose root is the value former it takes.
// `place` gives the argument it substitutes, which can make a redex where
// the body puts it at a spine's root.
function contractRedex(node, place) {
  const value = node[spine[node.tag][0]];
  if (node.tag === "App") return substituteTerm(value.body, value.name, place(node.arg));
  if (node.tag === "LApp") return substituteTerm(value.body, value.name, node.level);
  if (node.tag === "PApp") return substituteDimension(value.body, value.dim, node.arg);
  return node.tag === "Fst" ? value.first : value.second;
}

// Beta-reduce within a budget of substitutions, keeping every name: every
// application of a lambda, and every other redex the reduction makes,
// where a contraction puts a path, a pair or a function at the root of a
// path application, a projection or an instantiation, as substituting
// (path j => a) for p in p @ i does. Each is marked as a copy no other
// node holds. A redex of another kind that the term has of its own is
// kept.
export function betaReduce(term, budget = 256) {
  const reduced = new WeakMap(), placed = new WeakSet();
  const place = t => {
    if (!t || typeof t !== "object") return t;
    const copy = Array.isArray(t) ? [...t] : { ...t };
    placed.add(copy);
    return copy;
  };
  const beta = t => {
    if (!t || typeof t !== "object") return t;
    if (reduced.has(t)) return reduced.get(t);
    let result = Array.isArray(t) ? t.map(beta) : Object.fromEntries(Object.entries(t).map(([key, value]) => [key, beta(value)]));
    if (placed.has(t)) placed.add(result);
    for (;;) {
      const [root, former] = spine[result.tag] ?? [];
      if (!root || result[root]?.tag !== former || result.tag !== "App" && !placed.has(result[root]) || budget <= 0) break;
      budget--;
      result = place(beta(contractRedex(result, place)));
    }
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

// The binders a source text shows as one: the source Nat's induction
// writes its motive's variable and its successor clause's predecessor as
// the one name of `as k` (sourceText's NatInduction). spelledOut gives them
// one name, so displayTerm names them alike, as two binders of one name
// over one scope; the printer writes induction only where they are named
// alike, and chooses no name itself.
export function inductionBinders(elim) {
  const step = elim?.clauses?.[1];
  return elim?.tag === "Elim" && elim.signature === "unat__UNat" && elim.clauses.length === 2 && elim.motive?.tag === "Lam"
    && step?.tag === "Lam" && step.body?.tag === "Lam" ? [elim.motive, step] : null;
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

// 1. What the source text shows that the term does not spell out, written
// into the terms before displayTerm and readableDimensions settle names:
//  - every binder the printer would otherwise invent: a motive that is no
//    function, as a folded normal form keeps one that is a definition
//    (docs/roadmaps/runtime/folded-normal-forms.md), is λ (z : D). M(z), D
//    the domain M's type gives where it can be read (motiveDomain); a clause
//    with fewer arguments, hypotheses or dimensions than its constructor
//    takes, as evaluation eta-reduces one and a folded normal form keeps one
//    that is a definition, is applied to new ones, and so are a sum's
//    clauses and motive; an eliminator written where no function is applied
//    to it is the function that applies it, λ (x : D). e(x);
//  - the source Nat's induction shows its motive's variable and its
//    predecessor by one name (inductionBinders): both binders are renamed
//    to one, apart from what either would capture.
// Whatever this adds, a recovered domain, a motive reduced to its function,
// is spelled out by the same pass, and the new names are apart from every
// name of every term shown together. Each change is an eta-expansion, a
// renaming of a bound variable or a reduction of a motive's head: the term
// says what it said.
// `definitions` gives definitions' decoded types and values and their labels;
// `symbols` a declared type's constructors as the printer reads them
// (signatureDisplay); `dimensions` the context's.
export function spelledOut(terms, { definitions, symbols = {}, dimensions }) {
  dimensions = contextDimensions(dimensions);
  // Every name the terms have, a dimension's too: a new binder is none of
  // them. Syntax added later is collected as it is added.
  const used = new Set(dimensions), seen = new WeakSet();
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
  terms.forEach(collect);
  // A new variable is its stem where no name is, and numbered from 1
  // otherwise (numberedName: U_1, not the universe U1), each stem counting
  // on: displayTerm shows it by its stem where it can, and a display too
  // large for scoped names (globalNames) as it is. A new dimension, d1 and
  // on, is named as decoding's unnamed ones are.
  const next = new Map();
  const fresh = stem => {
    let n = next.get(stem) ?? (stem === "d" ? 1 : 0), name;
    do name = n ? numberedName(stem, n) : stem, n++; while (used.has(name));
    next.set(stem, n);
    used.add(name);
    return name;
  };
  const domain = motiveDomain(definitions);
  // The domain of a function, read on syntax not yet spelled out, once its
  // head redexes are contracted (head, below): a lambda's; a definition's, as
  // its type gives it after its spine; or an eliminator's, taken as a
  // function: its motive's, else its type, where that has no parameters.
  const domainOf = t => {
    const reduced = t && head(t);
    return reduced?.tag === "Lam" ? reduced.domain : domain(reduced) ?? (reduced?.tag === "Elim" ? eliminated(reduced) : null);
  };
  const eliminated = e => domainOf(e.motive)
    ?? (symbols[e.signature]?.slots?.length === 0 ? { tag: "Sort", signature: e.signature, parameters: [], levels: [] } : null);
  const added = t => { collect(t); return t; };
  const free = displayFreeNames(), mentions = (term, name) => free(term).has(name);
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
  // A motive that is a redex of its own, as a folded normal form keeps
  // (λ u. λ m. T)(tt), is consumed by the match the text writes: its head
  // redexes along its spine are contracted, within a budget, no other part.
  const head = (t, budget = 256) => {
    const [root, former] = spine[t?.tag] ?? [];
    if (!root || budget <= 0) return t;
    const inner = head(t[root], budget - 1);
    return inner.tag === former ? head(contractRedex({ ...t, [root]: inner }, argument => argument), budget - 1) : t;
  };
  const spell = term => {
    // An eliminator or a case analysis is spelled before its parts, which
    // are then spelled in turn, so that a substitution, a motive's head or
    // induction's renaming, never meets syntax already spelled out: a path
    // clause spelled out has no family, which a substitution cannot read.
    // Shared syntax is spelled once for each place it can occur in: as the
    // function an application applies, or anywhere else.
    const memo = [new WeakMap(), new WeakMap()];
    const go = (t, applying = false) => {
      if (!t || typeof t !== "object") return t;
      const table = memo[applying ? 1 : 0];
      if (table.has(t)) return table.get(t);
      let result = t;
      if (t.tag === "SumRec")
        result = { ...t, motive: applied(t.motive, "z"), left: applied(t.left, "a"), right: applied(t.right, "b") };
      if (t.tag === "Elim") {
        let motive = t.motive;
        if (motive && motive.tag !== "Lam") {
          // A motive whose head reduces to a function is that function;
          // another is applied to a new variable of its domain.
          const reduced = head(motive);
          if (reduced.tag === "Lam") motive = added(reduced);
          else {
            const of = domainOf(motive);
            motive = applied(motive, "z", of ? added(of) : null);
          }
        }
        const constructors = symbols[t.signature]?.constructors;
        const clauses = constructors?.length === t.clauses?.length
          ? t.clauses.map((body, index) => clause(body, constructorTakes(constructors[index], t.signature)))
          : t.clauses;
        result = { ...t, motive, clauses };
        const induction = inductionBinders(result);
        if (induction) {
          // The predecessor's name, where the motive does not show it for
          // another variable; else the motive's, where the successor clause
          // does not; else a new one. Each binder is renamed apart from what
          // it would capture.
          const [motive, step] = induction;
          const name = !mentions(motive.body, step.name) ? step.name : !mentions(step.body, motive.name) ? motive.name : fresh(stem(step.name));
          const renamed = binder => binder.name === name ? binder
            : added({ ...binder, name, body: substituteTerm(binder.body, binder.name, { tag: "Var", name }) });
          result = { ...result, motive: renamed(motive), clauses: [result.clauses[0], renamed(step)] };
        }
      }
      for (const [key, value] of Object.entries(result)) {
        const changed = go(value, result.tag === "App" && key === "fn");
        if (changed !== value) {
          if (result === t) result = Array.isArray(t) ? [...t] : { ...t };
          result[key] = changed;
        }
      }
      if (result.tag === "Elim" && !applying)
        result = applied(result, result.signature === "unat__UNat" ? "n" : "x", eliminated(result));
      table.set(t, result);
      return result;
    };
    return go(term);
  };
  return terms.map(spell);
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

// Terms named for source text, in one naming: the display's beta reduction,
// then the four passes above, spelledOut, displayTerm's naming,
// readableDimensions and qualified. `definitions` gives
// definitions' decoded types and values, the labels the printer shows
// them by, and each declaration's module::name, by its key in the
// compilation's bindings (qualified, below); `symbols` a declared type's
// constructors; `names` the names free
// variables show; `dimensions` the dimensions of the context the terms are
// shown in, which the caller always gives (contextDimensions); `reduce` the
// display's beta budget.
export function forSource(terms, { definitions, symbols, names = new Map(), dimensions, reduce = 256 }) {
  const context = contextDimensions(dimensions);
  const reduced = betaReduce(terms, reduce);
  const named = readableDimensions(displayTerm(spelledOut(reduced, { definitions, symbols, dimensions: context }), 0, names), context);
  return qualified(named, new Set([...context, ...named.flatMap(term => [...dimensionNames(term)]), ...names.values()]), { definitions, symbols });
}

// 4. Once names are settled, a definition, type or constructor whose label
// the text shows for something that keeps its name, a dimension of the
// context or of the terms, or a free variable the caller names, is marked
// `qualified` with its module::name
// (web/reference/first-proof.html#qualified-names), which no binder
// shadows: its declaration's module and label, as the compilation records
// them, since a kernel name a__b__q is a's b__q or a__b's q. Kernel notation
// shows it by its kernel name, as source text does one the compilation
// declares nowhere. `shown` holds those names; the labels are the
// printer's.
export function qualified(terms, shown, { definitions, symbols = {} }) {
  if (!shown.size) return terms;
  const label = t => t.tag === "DefRef" ? definitions.label(t.name)
    : t.tag === "Sort" ? symbols[t.signature]?.name ?? localName(t.signature) : t.tag === "Con" ? t.name : null;
  const spelling = t => t.tag === "DefRef" ? definitions.qualified(t.name) ?? t.name
    : t.tag === "Sort" ? definitions.qualified(t.signature) ?? t.signature
    : definitions.qualified(`${t.sort?.signature}:constructor:${t.index}`) ?? t.name;
  const copies = new WeakMap();
  const mark = t => {
    if (!t || typeof t !== "object") return t;
    if (copies.has(t)) return copies.get(t);
    let result = t;
    for (const [key, value] of Object.entries(t)) {
      const changed = mark(value);
      if (changed !== value) {
        if (result === t) result = Array.isArray(t) ? [...t] : { ...t };
        result[key] = changed;
      }
    }
    if (!Array.isArray(result) && shown.has(label(result))) result = { ...result, qualified: spelling(result) };
    copies.set(t, result);
    return result;
  };
  return terms.map(mark);
}
