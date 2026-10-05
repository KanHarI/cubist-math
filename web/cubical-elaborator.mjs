import { CubicalSyntax } from "./cubical-syntax.mjs";
import { T, substituteTerm, withoutEmptyFaces } from "./translator/core.mjs";
import { interval as I } from "./translator/lattice.mjs";
import { NameSupply, localName, numberedName, stem } from "./translator/names.mjs";
import { sourceText } from "./cubical-source-text.mjs";
import { cubicalText } from "./cubical-notation.mjs";
import { levelNormal } from "./cubical-levels.mjs";
import { InstructionDriver } from "./cubical-instruction-driver.mjs";
import { KernelError } from "./cubical-kernel.mjs";
import { admitSignature } from "./cubical-signatures.mjs";

const speculativeFailures = new Set(["mismatch", "budget", "deadline"]);

// Binder names the instruction driver made up, such as x'1 for a context
// entry named apart from another x, taken back to their stems for display
// wherever the stem occurs nowhere in the binder's body, so nothing in it
// can tell the two apart. Syntax is shared, so each pass is memoized.
const TERM_BINDERS = new Set(["Pi", "Lam", "Sigma", "LPi", "LLam"]);
class SourceNames {
  constructor(stems) { this.stems = stems; this.results = new WeakMap(); this.mentions = new Map(); this.renamed = new Map(); }
  memo(table, key) {
    if (!table.has(key)) table.set(key, new WeakMap());
    return table.get(key);
  }
  // Whether a name occurs in syntax, free or bound.
  occurs(value, name) {
    if (!value || typeof value !== "object") return false;
    const seen = this.memo(this.mentions, name);
    if (!seen.has(value)) seen.set(value, value.name === name || Object.values(value).some(field => this.occurs(field, name)));
    return seen.get(value);
  }
  // Free occurrences of a variable renamed; the new name occurs nowhere.
  rename(value, from, to) {
    if (!value || typeof value !== "object") return value;
    const done = this.memo(this.renamed, `${from}\u0000${to}`);
    if (!done.has(value)) {
      let result = value;
      if (value.tag === "Var" && value.name === from) result = { ...value, name: to };
      else {
        // A binder of the same name hides the variable in its body.
        const shadowed = TERM_BINDERS.has(value.tag) && value.name === from;
        const copy = Array.isArray(value) ? [] : {};
        let changed = false;
        for (const [key, field] of Object.entries(value)) {
          copy[key] = shadowed && key === "body" ? field : this.rename(field, from, to);
          changed ||= copy[key] !== field;
        }
        if (changed) result = copy;
      }
      done.set(value, result);
    }
    return done.get(value);
  }
  apply(value) {
    if (!value || typeof value !== "object") return value;
    if (!this.results.has(value)) {
      let current = value;
      const stem = TERM_BINDERS.has(value.tag) && this.stems.get(value.name);
      if (stem && !this.occurs(value.body, stem))
        current = { ...value, name: stem, body: this.rename(value.body, value.name, stem) };
      const copy = Array.isArray(current) ? [] : {};
      let changed = current !== value;
      for (const [key, field] of Object.entries(current)) {
        copy[key] = this.apply(field);
        changed ||= copy[key] !== field;
      }
      this.results.set(value, changed ? copy : value);
    }
    return this.results.get(value);
  }
}
const namedBinders = new Set(["Var", "Pi", "Lam", "Sigma", "LPi", "LLam"]);

// For messages only: reduce beta-redexes, within a budget, and give generated
// names back their source stems (`A3` → `A`, `native10` → `x`) where no two
// names would clash. The result is never checked or stored.
export function displayTerm(term, budget = 256) {
  const shown = betaReduce(term, budget);
  return scopedNames(shown) ?? globalNames(shown);
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
const binders = new Set(["Pi", "Lam", "Sigma", "LPi", "LLam"]);

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

function scopedNames(term, limit = 2000) {
  let work = 0;
  const freeMemo = new WeakMap();
  const free = t => {
    if (!t || typeof t !== "object") return new Set();
    if (freeMemo.has(t)) return freeMemo.get(t);
    let names;
    if (t.tag === "Var") names = new Set([t.name]);
    else {
      names = new Set();
      for (const [key, value] of Object.entries(t)) {
        if (binders.has(t.tag) && key === "body") for (const name of free(value)) { if (name !== t.name) names.add(name); }
        else for (const name of free(value)) names.add(name);
      }
    }
    freeMemo.set(t, names);
    return names;
  };
  const go = (t, shownAs, inScope) => {
    if (++work > limit) throw scopedNames;
    if (!t || typeof t !== "object") return t;
    if (Array.isArray(t)) return t.map(item => go(item, shownAs, inScope));
    if (t.tag === "Var") return shownAs.has(t.name) ? { ...t, name: shownAs.get(t.name) } : t;
    const result = {};
    if (binders.has(t.tag) && typeof t.name === "string") {
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
  // share one; binders then avoid those names.
  const outer = [...free(term)], count = new Map(), labels = printedLabels(term);
  for (const name of outer) count.set(stem(name), (count.get(stem(name)) ?? 0) + 1);
  const shownAs = apartFromLabels(new Map(outer.map(name => [name,
    count.get(stem(name)) === 1 && !(outer.includes(stem(name)) && stem(name) !== name) && !labels.has(stem(name))
      ? stem(name) : name])), labels);
  try { return go(term, shownAs, new Set([...shownAs.values(), ...labels])); }
  catch (error) { if (error === scopedNames) return null; throw error; }
}

// Every generated name whose stem no other name shares shows its stem.
function globalNames(shown) {
  const names = new Set(), seen = new WeakSet();
  const collect = t => {
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    if (namedBinders.has(t.tag) && typeof t.name === "string") names.add(t.name);
    Object.values(t).forEach(collect);
  };
  collect(shown);
  const count = new Map(), labels = printedLabels(shown);
  for (const name of names) count.set(stem(name), (count.get(stem(name)) ?? 0) + 1);
  const renames = apartFromLabels(new Map([...names].map(name => [name, count.get(stem(name)) === 1
    && !(names.has(stem(name)) && stem(name) !== name) && !labels.has(stem(name)) ? stem(name) : name])), labels);
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

// Elaboration queries use the native checker and demand only a type's outer
// constructor. JavaScript neither normalizes proofs nor approves conversions.
export class NativeCubicalElaborator {
  constructor(kernel) {
    this.kernel = kernel;
    this.syntax = new CubicalSyntax(kernel);
    this.steps = 0;
    // Elaboration passes its own name supply and dimensions to each query;
    // these defaults serve inspection and other callers outside a source unit.
    this.names = new NameSupply({ taken: name => this.assumptions.has(name) });
    this.dimensions = new Map();
    this.assumptions = new Map();
    this.libraryAssumptions = new Map();
    this.assumptionLabels = new Map();
    this.assumptionOrigins = new Map();
    this.definitionViews = new Map();
    this.genericDefinitions = new Map();
    this.scopeDefinitions = new Set();
    // Each definition's kernel extensions under review, such as H1: the
    // `kernel extension: H1` marker (h1-signature-specification.md, 6.4).
    // Visible, and not a non-computing dependency.
    this.definitionExtensions = new Map();
    // Each declared type's lowering metadata (web/translator/inductive.mjs), by
    // the name its signature was registered under.
    this.inductives = new Map();
  }
  // The kernel extensions a term relies on: a declared type's instance,
  // constructor or eliminator whose signature was admitted experimentally,
  // and every definition that carries a marker. Since H1's release no
  // signature is admitted experimentally, so the list is empty.
  extensionsOf(...terms) {
    // No signature admitted in this session, no marker: nothing to walk.
    if (!this.kernel.signatures.size) return [];
    const found = new Set(), seen = new WeakSet(), experimental = this.experimentalSignatures ??= new WeakMap();
    const signature = name => {
      const record = this.kernel.signatures.get(name);
      if (!record) return;
      if (!experimental.has(record)) experimental.set(record, this.kernel.signature(record.index).experimental);
      if (experimental.get(record)) found.add("H1");
    };
    const visit = term => {
      if (!term || typeof term !== "object" || seen.has(term)) return;
      seen.add(term);
      if (term.tag === "Sort" || term.tag === "Elim") signature(term.signature);
      if (term.tag === "DefRef") for (const marker of this.definitionExtensions.get(term.name) ?? []) found.add(marker);
      for (const child of Object.values(term)) visit(child);
    };
    terms.forEach(visit);
    return [...found].sort();
  }
  // An admitted signature's former, Π (xs < ω). Π (ps : Ps). U(ℓ), as syntax,
  // and the kernel extensions its admission carries.
  signatureFormer(record) { return this.syntax.decode(this.kernel.signature(record.index).former); }
  signatureExtensions(record) { return this.kernel.signature(record.index).experimental ? ["H1"] : []; }
  // Whether one level lies within another at every assignment (G0 §2.4,
  // Lemma 2): coefficient by coefficient. For messages only; the kernel
  // decides levels.
  levelWithin(level, bound) {
    const read = id => this.kernel.node(id);
    const a = levelNormal(read, this.syntax.encodeLevel(level)), b = levelNormal(read, this.syntax.encodeLevel(bound));
    if (a.tier || b.tier) return a.tier < b.tier || (a.tier === b.tier && a.constant <= b.constant);
    return a.constant <= b.constant && [...a.offsets].every(([name, offset]) => (b.offsets.get(name) ?? -1) >= offset);
  }
  // Admits a declared type's signature in normal form (web/cubical-signatures.mjs),
  // one instruction at a time, as a declaration's admission is.
  admitSignature(spec) {
    try { return admitSignature(this.kernel, spec, { syntax: this.syntax, driver: this.driver }); }
    catch (error) {
      const refused = /switched off/.test(error.message)
        ? "Declared types (H1) are switched off in this kernel session."
        : error.message;
      throw this.describeMismatch(Object.assign(new Error(`Instruction kernel: ${refused}`),
        { kind: error.kind ?? "other", mismatch: error.mismatch, constructor: error.constructor }), new Map());
    } finally {
      this.kernel.instructionDriver = null;
    }
  }
  context(local = new Map()) { return new Map([...this.assumptions, ...local]); }
  assume(name, type, avoid = new Set()) {
    while (avoid.has(name) || this.kernel.names.has(name)) name += "_";
    const dimensions = this.dimensions;
    let checked;
    try { this.dimensions = new Map(); checked = this.infer(type); }
    finally { this.dimensions = dimensions; }
    if (this.nf(checked.type).tag !== "U") throw new Error("An assumption needs a checked type.");
    this.kernel.symbol(name);
    this.assumptions.set(name, type);
    return { tag: "Var", name };
  }
  requiredAssumptions(...terms) {
    const names = new Set();
    // Compute free names once per shared subtree. Removing the local binder
    // after visiting its body keeps this independent of the surrounding scope.
    const memo = new WeakMap();
    const free = term => {
      if (!term || typeof term !== "object") return new Set();
      if (memo.has(term)) return memo.get(term);
      const result = new Set();
      if (term.tag === "Var") result.add(term.name);
      else if (["Pi", "Lam", "Sigma", "LPi", "LLam"].includes(term.tag)) {
        for (const name of free(term.domain)) result.add(name);
        for (const name of free(term.body)) if (name !== term.name) result.add(name);
      } else for (const child of Object.values(term)) for (const name of free(child)) result.add(name);
      memo.set(term, result); return result;
    };
    const visit = term => { for (const name of free(term)) names.add(name); };
    terms.forEach(visit);
    // Context types can depend on earlier assumptions; close that dependency set.
    for (const [name, type] of [...this.assumptions].reverse()) if (names.has(name)) visit(type);
    return new Map([...this.assumptions].filter(([name]) => names.has(name)));
  }
  // A type mismatch names both types in Cubist source syntax. The kernel's handles
  // are read at once, before any rollback can invalidate them.
  describeMismatch(error, dimensions) {
    if (error?.kind !== "mismatch" || !error.mismatch?.found || error.described) return error;
    error.described = true;
    try {
      // Both types named together, once, so that a variable and a dimension
      // read alike in each, apart from every label either prints.
      const [found, expected] = this.displayTexts([error.mismatch.found, error.mismatch.expected]
        .map(handle => this.syntax.decode(handle, dimensions)));
      error.message = `Type mismatch: found ${found}, expected ${expected}.`;
    } catch { /* Keep the kernel's message. */ }
    return error;
  }
  // Definitions show their source names, without the module prefix, and
  // assumptions their labels. A definition with implicit parameters says how
  // many, and how many assumptions come before them, so that a call shows
  // them in double braces, as the source writes it. A theory's projection
  // names its field, so that T.f(m) shows as m.f.
  get displayNames() {
    return this.displaySymbols ??= new Proxy({}, { get: (_, name) => typeof name !== "string" ? undefined
      : this.assumptionLabels.has(name) ? { name: this.assumptionLabels.get(name), kind: "axiom" }
      : this.kernel.signatures?.has(name) ? this.signatureDisplay(name)
      : localName(name) !== name ? { name: localName(name), ...this.implicitDisplay(name),
        ...(this.theoryProjections?.has(name) ? { projection: this.theoryProjections.get(name) } : {}) } : undefined });
  }
  implicitDisplay(name) {
    const view = this.definitionViews.get(name), implicit = view?.parameters?.filter(parameter => parameter.implicit).length;
    return implicit ? { implicit, assumed: view.assumptions.size } : {};
  }
  // A declared type's name and its constructors, each with its numbers of
  // data, positions and dimensions, so that the printer can show the type's
  // eliminator as the match that builds it. A generated constructor, such as
  // a truncation's squash, is named through its type, as a clause writes it.
  // Its parameters' kinds in source order, so that an instance prints with
  // every argument the source writes: "recorded" and "erased" universes and
  // term "parameter"s. An instance carries no erased universe.
  signatureDisplay(name) {
    const record = this.kernel.signatures.get(name), shapes = this.kernel.signature(record.index).constructors;
    const inductive = this.inductives?.get(name);
    return { name: localName(name), ...(inductive ? { slots: inductive.slots.map(slot => slot.level === undefined ? "parameter"
        : inductive.levels[slot.level].recorded ? "recorded" : "erased") } : {}),
      constructors: record.constructors.map((constructor, c) => ({
      name: shapes[c].generated ? `${localName(name)}.${constructor}` : constructor,
      data: shapes[c].data, positions: shapes[c].positions, dimensions: shapes[c].dimensions })) };
  }
  displayText(term, width = 160, limit = 4000) {
    return this.printed(readableDimensions([displayTerm(term)])[0], width, limit);
  }
  // A term in kernel notation as it was checked, no redex reduced.
  kernelText(term, width = 160) {
    const text = cubicalText(readableDimensions([displayTerm(term, 0)])[0], this.displayNames);
    return text.length > width ? `${text.slice(0, width - 1)}…` : text;
  }
  // Several terms shown with one naming: a variable they share has one name
  // in all of them, apart from every label any of them prints.
  displayTexts(terms, width = 160, limit = 4000) {
    return readableDimensions(displayTerm(terms)).map(term => this.printed(term, width, limit));
  }
  // A term whose names are already settled, as source text within a width.
  printed(term, width = 160, limit = 4000) {
    const text = sourceText(term, this.displayNames, limit);
    return text.length > width ? `${text.slice(0, width - 1)}…` : text;
  }
  // A goal, and the term a statement built for it, shown with one renaming,
  // so the context's names, the target and the term agree.
  // `print` is sourceText by default; cubicalText gives mathematical notation.
  // A derivation shows its terms as they are: `reduce` false keeps redexes.
  displayGoal(context, target, built = null, width = 400, print = null, reduce = true) {
    // Goals can share large terms; the printer stops after `width` nodes too.
    const printed = term => print ? print(term, this.displayNames) : sourceText(term, this.displayNames, width);
    const show = term => { const text = printed(term); return text.length > width ? `${text.slice(0, width - 1)}…` : text; };
    let chained = { tag: "Pair", first: target, second: built ?? { tag: "Point" } };
    for (const [name, type] of [...context].reverse()) chained = T.pi(name, type, chained);
    let shown = displayTerm(chained, reduce ? 256 : 0);
    const locals = [];
    while (locals.length < context.size && shown.tag === "Pi") {
      // A universe variable's entry is its bound: U < UU0.
      locals.push({ name: shown.name, type: show(shown.domain), relation: shown.domain?.tag === "LBound" ? "<" : ":" });
      shown = shown.body;
    }
    return { locals, goal: show(shown.first), built: built ? show(shown.second) : null };
  }
  // Every check and every inference is a derivation by the instruction
  // kernel: the term the elaborator wrote, at the type it expects, over its
  // context. The result is the derived term and its type, in the elaborator's
  // names; a failure is a mismatch (or a budget or deadline) as the kernel
  // reports one, and a speculative check reads it as an answer. The term
  // checker is not consulted.
  checkSyntax(term, expected, context, dimensions, describe = true) {
    try { return this.derived(term, expected, context, dimensions); }
    catch (error) { throw describe ? this.describeMismatch(error, dimensions) : error; }
  }
  derived(term, expected, context, dimensions) {
    // A judgement derived earlier is reused without work, so the deadline is
    // polled here too, not only by the instructions the search issues.
    this.kernel.checkDeadline();
    const driver = this.driver, graph = driver.graph, before = graph.count, mask = this.dimensionMask(dimensions);
    const assumptions = [...this.context(context)].map(([name, type]) =>
      [this.kernel.symbol(name), this.syntax.encode(type, dimensions)]);
    const raw = this.syntax.encode(term, dimensions);
    let judgement;
    try {
      judgement = expected ? driver.check(raw, this.syntax.encode(expected, dimensions), assumptions, mask)
        : driver.infer(raw, assumptions, mask);
    } catch (error) {
      // The kernel's own errors pass as they are: a mismatch, or running out
      // of time or budget. Anything else is the instruction kernel's refusal.
      if (error instanceof KernelError && ["mismatch", "budget", "deadline"].includes(error.kind)) throw error;
      throw Object.assign(new KernelError(`Instruction kernel: ${error.message}`, error.kind ?? "other"), { mismatch: error.mismatch });
    }
    // An assumption the driver had to name apart takes its own name back.
    let { term: expression, type } = graph.judgement(judgement);
    for (const [symbol, entry] of driver.contextScope(assumptions, mask)) {
      if (typeof symbol !== "number") continue;
      const own = graph.entry(entry).symbol;
      if (own !== symbol) {
        expression = graph.rename(expression, false, own, symbol);
        type = graph.rename(type, false, own, symbol);
      }
    }
    const arena = this.kernel.arena(), derivedHandles = this.kernel.derivedHandles ??= new Set();
    derivedHandles.add(expression).add(type);
    const names = this.kernel.variantStems?.size ? this.sourceNames ??= new SourceNames(this.kernel.variantStems) : null;
    const display = value => names ? names.apply(value) : value;
    return { expression, typeHandle: type, term: display(this.syntax.decode(expression, dimensions)),
      type: display(this.syntax.decode(type, dimensions)), checkingSteps: graph.count - before,
      arenaNodes: arena.nodes, arenaBytes: arena.bytes };
  }
  // The type the kernel computes for the next clause of an eliminator, with
  // the motive and the clauses given so far (ClauseType_k, the H1
  // specification's 3.6): a query, as match elaborates each clause against
  // it. The eliminator is started in the kernel and never closed.
  nextClauseType(motive, clauses, context = new Map(), dimensions = this.dimensions) {
    this.kernel.checkDeadline();
    const driver = this.driver, graph = driver.graph;
    const assumptions = [...this.context(context)].map(([name, type]) =>
      [this.kernel.symbol(name), this.syntax.encode(type, dimensions)]);
    const mask = this.dimensionMask(dimensions);
    let type;
    try {
      const scope = driver.contextScope(assumptions, mask);
      let eliminator = driver.openEliminator(driver.derive(this.syntax.encode(motive, dimensions), scope));
      for (const clause of clauses) eliminator = driver.addClause(eliminator, driver.derive(this.syntax.encode(clause, dimensions), scope));
      type = graph.judgement(eliminator).type;
      for (const [symbol, entry] of scope) {
        if (typeof symbol !== "number") continue;
        const own = graph.entry(entry).symbol;
        if (own !== symbol) type = graph.rename(type, false, own, symbol);
      }
    } catch (error) {
      if (error instanceof KernelError && ["mismatch", "budget", "deadline"].includes(error.kind)) throw this.describeMismatch(error, dimensions);
      throw Object.assign(new KernelError(`Instruction kernel: ${error.message}`, error.kind ?? "other"), { mismatch: error.mismatch });
    }
    return this.syntax.decode(type, dimensions);
  }
  // A check over a context given as [name, type] pairs, for inspection.
  checkView(term, expected, context = [], dimensions = new Map()) {
    return this.checkSyntax(term, expected, new Map(context), dimensions);
  }
  infer(term, context = new Map(), dimensions = this.dimensions) {
    const checked = this.checkSyntax(term, null, context, dimensions);
    this.steps += checked.checkingSteps;
    return { term: checked.term, type: checked.type, native: { ok: true,
      arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes, axioms: [...this.requiredAssumptions(checked.term, checked.type).keys()],
      extensions: this.extensionsOf(checked.term, checked.type) } };
  }
  check(term, expected, context = new Map(), dimensions = this.dimensions, describe = true) {
    const checked = this.checkSyntax(term, expected, context, dimensions, describe);
    this.steps += checked.checkingSteps;
    return checked.term;
  }
  // The cube of a check: one bit per dimension, each at its own index.
  dimensionMask(dimensions) {
    let mask = 0n;
    for (const [name, index] of dimensions) {
      if (typeof name !== "string" || !Number.isInteger(index) || index < 0 || index >= 64)
        throw new Error("Invalid cubical dimension binding.");
      const bit = 1n << BigInt(index);
      if (mask & bit) throw new Error("Cubical dimension indices must be distinct.");
      mask |= bit;
    }
    return mask;
  }
  // The driver of this declaration's instructions, kept on the kernel, which
  // every module's checker shares: its caches hold judgements and handles, so
  // a declaration transaction's finish drops it.
  get driver() { return this.kernel.instructionDriver ??= new InstructionDriver(this.kernel); }
  ascribe(term, type, names = this.names) {
    // Application of the identity at the declared type retains that exact
    // signature in the kernel's inferred result. The next native check checks
    // the conversion; this is no unchecked annotation or new kernel rule.
    const name = names.fresh("ascription");
    return { tag: "App", fn: { tag: "Lam", name, domain: type, body: { tag: "Var", name } }, arg: term };
  }
  nf(term, dimensions = this.dimensions) {
    // Translator's nf calls ask for Pi/Sigma/Path heads, not full normal forms.
    return this.syntax.decode(this.kernel.head(this.syntax.encode(term, dimensions)), dimensions);
  }
  equal(left, right, context = new Map(), dimensions = this.dimensions, names = this.names) {
    const type = this.infer(left, context, dimensions).type;
    // This binder scopes over both terms. A generated name is not a live
    // coordinate, so it cannot capture one.
    const dim = names.fresh("conversion");
    const constant = { tag: "PLam", dim, family: type, body: left };
    const expected = { tag: "Path", dim, family: type, left, right };
    const result = this.attempt(constant, expected, context, dimensions);
    if (result.ok) return true;
    if (result.failure === "mismatch") return false;
    throw result.error;
  }
  // A speculative check answers with a value: {ok: true, term}, or
  // {ok: false, failure, error} when the kernel reports a type mismatch or
  // runs out of steps or time. Any other rejection throws, as in check().
  attempt(term, expected, context = new Map(), dimensions = this.dimensions) {
    // Speculative failures are answers, not diagnostics: they are not described.
    try { return { ok: true, term: this.check(term, expected, context, dimensions, false) }; }
    catch (error) {
      if (!speculativeFailures.has(error?.kind)) throw error;
      return { ok: false, failure: error.kind, error };
    }
  }
  expect(actual, expected, context = new Map(), dimensions = this.dimensions, names = this.names) {
    // Ask the kernel whether an arbitrary inhabitant of the actual type also
    // inhabits the expected type. This uses directed cumulative typing, while
    // equal() continues to ask for definitional equality.
    const name = names.fresh("expected");
    // A query, not a proof step: nothing is issued to the instruction kernel.
    this.check({ tag: "Var", name }, expected, new Map(context).set(name, actual), dimensions);
  }
  // `parameters` names the declaration's own parameters, as the source
  // declares them, for named arguments (L4.1a): the kernel's binders have
  // generated names.
  define(name, term, type, parameters = null) {
    const assumptions = this.requiredAssumptions(term, type);
    let body = term, signature = type;
    for (const [parameter, domain] of [...assumptions].reverse()) {
      body = { tag: "Lam", name: parameter, domain, body };
      signature = { tag: "Pi", name: parameter, domain, body: signature };
    }
    let reference, admission;
    try { ({ reference, admission } = this.admit(name, this.syntax.encode(body), this.syntax.encode(signature))); }
    catch (error) {
      // A type the kernel inferred by substitution can carry parts on the
      // face 0, which need not be well typed and the driver may fail to
      // derive. They are never used: without them, the type is the same.
      const cleaned = withoutEmptyFaces(signature);
      if (cleaned === signature) throw this.describeMismatch(error, new Map());
      try { ({ reference, admission } = this.admit(name, this.syntax.encode(body), this.syntax.encode(cleaned))); }
      catch { throw this.describeMismatch(error, new Map()); }
      type = withoutEmptyFaces(type);
    }
    this.definitionViews.set(name, { term, type, assumptions, admission, ...(parameters ? { parameters } : {}) });
    this.definitionExtensions.set(name, this.extensionsOf(term, type, ...assumptions.values()));
    let result = this.syntax.decode(reference);
    for (const parameter of assumptions.keys()) result = { tag: "App", fn: result, arg: { tag: "Var", name: parameter } };
    return result;
  }
  // The instruction kernel admits every definition. The instruction driver
  // derives the body's source syntax at its type, one kernel instruction per
  // rule, restoring annotations and splitting faces into clauses, and Define
  // registers the closed judgement. The term checker's conversion guides the
  // search and is never evidence; a body the instruction kernel cannot derive
  // is not a definition.
  admit(name, body, signature) {
    const started = performance.now();
    const driver = this.driver, graph = driver.graph, before = graph.count;
    let reference;
    try {
      const judgement = driver.check(body, signature);
      reference = graph.judgement(graph.define(name, judgement)).term;
    } catch (error) {
      throw Object.assign(new Error(`Instruction kernel: ${error.message}`), { kind: error.kind ?? "other" });
    } finally {
      // One driver per declaration: the next starts from a fresh one.
      this.kernel.instructionDriver = null;
    }
    this.kernel.definitions.set(name, reference);
    return { reference, admission: { ms: +(performance.now() - started).toFixed(3), judgements: graph.count - before } };
  }
  // A universe-generic definition the elaborator builds, such as ua's: checked
  // and named once, and instantiated at each use.
  genericDefinition(name, elaborate) {
    if (this.genericDefinitions.has(name)) return this.genericDefinitions.get(name);
    const term = elaborate(), checked = this.infer(term);
    const value = NativeCubicalElaborator.prototype.define.call(this, name, checked.term, checked.type);
    this.genericDefinitions.set(name, value);
    return value;
  }
  // `with unfolding [names] { e }`: e checked as a definition of its own. The
  // names guided the retired conversion oracle; the driver's own guide
  // unfolds what a comparison needs, so they no longer matter here.
  scopedUnfolding(elaborate, context, expected = null, dimensions = this.dimensions, supply = this.names) {
    const raw = elaborate();
    const checked = expected ? { term: this.check(raw, expected, context, dimensions), type: expected }
      : this.infer(raw, context, dimensions);
    let term = checked.term, type = checked.type;
    // Close over local variables before interval coordinates: a variable's
    // type may itself depend on a coordinate. The helper is then checked as
    // an ordinary closed definition, not installed as an unchecked promise.
    for (const [name, domain] of [...context].reverse()) {
      term = T.lam(name, domain, term); type = T.pi(name, domain, type);
    }
    for (const dim of [...dimensions.keys()].reverse()) {
      term = T.line(dim, type, term);
      type = T.path(dim, type, T.at(term, I.zero), T.at(term, I.one));
    }
    this.kernel.unfoldingSerial = (this.kernel.unfoldingSerial ?? 0) + 1;
    const name = `${this.bindingName?.("unfolding") ?? "unfolding"}_${this.kernel.unfoldingSerial}`;
    let result = NativeCubicalElaborator.prototype.define.call(this, name, this.ascribe(term, type, supply), type);
    this.scopeDefinitions.add(name);
    for (const dim of dimensions.keys()) result = T.at(result, I.variable(dim));
    for (const name of context.keys()) result = T.app(result, T.variable(name));
    return result;
  }

  verify(term, expected = null, assumptions = []) {
    const checked = this.checkSyntax(term, expected, new Map(assumptions), this.dimensions);
    const normal = this.syntax.decode(this.kernel.normalize(checked.expression), this.dimensions);
    return { ...checked, normal, native: { ok: true, arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes, axioms: [...this.requiredAssumptions(checked.term, checked.type).keys()],
      extensions: this.extensionsOf(checked.term, checked.type) } };
  }
}
