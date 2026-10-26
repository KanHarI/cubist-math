import { isResourceLimit } from "./resource-limits.mjs";
import { termBinders } from "./translator/term-shape.mjs";
import { CubicalSyntax } from "./cubical-syntax.mjs";
import { T, withoutEmptyFaces } from "./translator/core.mjs";
import { interval as I } from "./translator/lattice.mjs";
import { NameSupply, localName } from "./translator/names.mjs";
import { sourceText } from "./cubical-source-text.mjs";
import { contextDimensions, displayTerm, forSource, readableDimensions } from "./display-naming.mjs";
import { cubicalText } from "./cubical-notation.mjs";
import { levelNormal } from "./cubical-levels.mjs";
import { InstructionDriver } from "./cubical-instruction-driver.mjs";
import { KernelError } from "./cubical-kernel.mjs";
import { admitSignature } from "./cubical-signatures.mjs";

const speculativeFailure = kind => kind === "mismatch" || isResourceLimit(kind);
// A display's naming lives in display-naming.mjs; these were defined here.
export { betaReduce, dimensionNames, displayTerm, printedLabels, readableDimensions } from "./display-naming.mjs";

// Binder names the instruction driver made up, such as x'1 for a context
// entry named apart from another x, taken back to their stems for display
// wherever the stem occurs nowhere in the binder's body, so nothing in it
// can tell the two apart. Syntax is shared, so each pass is memoized.
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
        const shadowed = termBinders.has(value.tag) && value.name === from;
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
      const stem = termBinders.has(value.tag) && this.stems.get(value.name);
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
    // Theories' records, by the binding of the type each describes (a type
    // of models, of homomorphisms or of isomorphisms), and the field each
    // projection reads, which it prints as m.f (L2.4). Every
    // module's check shares them, so a theory is known where its module is
    // imported.
    this.theories = new Map();
    this.theoryProjections = new Map();
    // How notations print (L2.10d): for an operation a notation's rule
    // applies, the notation and its operator; for a literal rule's parser
    // or a numeral rule's function, the notation; for a theory's projection
    // with a notation, its operator. The printer uses them only where the
    // notation is selected, or qualified.
    this.notationPrinting = new Map();
    this.genericDefinitions = new Map();
    this.scopeDefinitions = new Set();
    // Each definition's kernel extensions under review, such as H1: the
    // `kernel extension: H1` marker (h1-signature-specification.md, 6.4).
    // Visible, and not a non-computing dependency.
    this.definitionExtensions = new Map();
    // Each declared type's lowering metadata (web/translator/inductive.mjs), by
    // the name its signature was registered under.
    this.inductives = new Map();
    // The instruction kernel's work, cumulative: how long its derivations
    // took and how many judgements they added, wherever the elaborator asks
    // for one: a part's check as it elaborates, a clause's type, a
    // signature's or a body's admission. The benchmark reads it around each
    // declaration.
    this.instructionWork = { ms: 0, judgements: 0, depth: 0 };
  }
  // A derivation by the instruction kernel, counted in instructionWork once
  // however deep, over `graph`, the driver's judgement graph.
  instructed(graph, derivation) {
    const work = this.instructionWork;
    if (work.depth++) try { return derivation(); } finally { work.depth--; }
    const started = performance.now(), before = graph.count;
    try { return derivation(); }
    finally { work.depth--; work.ms += performance.now() - started; work.judgements += graph.count - before; }
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
    const driver = this.driver;
    try { return this.instructed(driver.graph, () => admitSignature(this.kernel, spec, { syntax: this.syntax, driver })); }
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
    // after visiting its body keeps this independent of the surrounding scope,
    // and terms never change: so the names are kept from one check to the
    // next, which ask about the same parts again and again.
    const memo = this.requiredNames ??= new WeakMap();
    const free = term => {
      if (!term || typeof term !== "object") return new Set();
      if (memo.has(term)) return memo.get(term);
      const result = new Set();
      if (term.tag === "Var") result.add(term.name);
      else if (termBinders.has(term.tag)) {
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
        .map(handle => this.syntax.decode(handle, dimensions)), dimensions);
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
        ...(this.theoryProjections?.has(name) ? { projection: this.theoryProjections.get(name) } : {}),
        ...(this.notationPrinting?.has(name) ? { printing: this.notationPrinting.get(name) } : {}) } : undefined });
  }
  // How forSource (display-naming.mjs) reads this checker: definitions'
  // checked types and values from the kernel, each decoded once per display,
  // their labels, and each declaration's module::name, from its binding in
  // the compilation; declared types' constructors; and the dimensions of
  // the context a term is shown in, which the caller gives.
  displayNaming(dimensions, reduce = 256, names = new Map()) {
    const decoded = new Map();
    const part = which => name => {
      const key = `${which} ${name}`;
      if (!decoded.has(key)) {
        const reference = this.kernel.definitions.get(name);
        decoded.set(key, reference ? this.syntax.decode(this.kernel.definition(reference)[which]) : null);
      }
      return decoded.get(key);
    };
    const qualified = key => {
      const record = this.compilationBindings?.declaration(key)?.binding;
      return record ? `${record.origin.module}::${record.label}` : null;
    };
    const definitions = { type: part("type"), value: part("value"), label: name => this.displayNames[name]?.name ?? localName(name), qualified };
    return { definitions, symbols: this.displayNames, names, reduce, dimensions: contextDimensions(dimensions) };
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
    return { name: localName(name), printing: this.notationPrinting.get(name), ...(inductive ? { slots: inductive.slots.map(slot => slot.level === undefined ? "parameter"
        : inductive.levels[slot.level].recorded ? "recorded" : "erased") } : {}),
      constructors: record.constructors.map((constructor, c) => ({
      name: shapes[c].generated ? `${localName(name)}.${constructor}` : constructor,
      order: inductive?.constructors[c]?.order,
      data: shapes[c].data, positions: shapes[c].positions, dimensions: shapes[c].dimensions })) };
  }
  // Without a notation, a term prints in the one selected where the message
  // that shows it arises: the declaration's (`notation`, set as each is
  // translated, L2.10j).
  // `reduce` bounds the beta reductions made for display: 0 shows the term
  // as it is.
  // Each display path (displayText, displayTexts, displayGoal, kernelText)
  // names its terms in the context they are shown in, whose dimensions its
  // caller gives (contextDimensions): source text by forSource, kernel
  // notation by displayTerm and cubicalText. The printer chooses no name.
  displayText(term, dimensions, { width = 160, limit = 4000, notation = this.notation ?? {}, reduce = 256 } = {}) {
    return this.printed(forSource([term], this.displayNaming(dimensions, reduce))[0], width, limit, notation);
  }
  // A term in kernel notation as it was checked, no redex reduced.
  kernelText(term, dimensions, width = 160) {
    const context = contextDimensions(dimensions);
    const text = cubicalText(readableDimensions([displayTerm(term, 0)], context)[0], this.displayNames, { dimensions: context });
    return text.length > width ? `${text.slice(0, width - 1)}…` : text;
  }
  // Several terms shown with one naming: a variable they share has one name
  // in all of them, apart from every label any of them prints. `names` gives
  // free variables their names, as displayTerm takes them.
  displayTexts(terms, dimensions, { width = 160, limit = 4000, notation = this.notation ?? {}, names = new Map() } = {}) {
    return forSource(terms, this.displayNaming(dimensions, 256, names)).map(term => this.printed(term, width, limit, notation));
  }
  // A term whose names are already settled, as source text within a width.
  printed(term, width = 160, limit = 4000, notation = this.notation ?? {}) {
    const text = sourceText(term, this.displayNames, limit, notation);
    return text.length > width ? `${text.slice(0, width - 1)}…` : text;
  }
  // A goal, and the term a statement built for it, shown with one renaming,
  // so the context's names, the target and the term agree.
  // Source text, or with `kernel` mathematical notation, as a judgement
  // graph shows terms. A derivation shows its terms as they are: `reduce`
  // false keeps redexes.
  // `notation.selection` names the notation selected at the goal (L2.10d).
  displayGoal(context, dimensions, target, built = null, { width = 400, kernel = false, reduce = true, notation = {} } = {}) {
    const names = contextDimensions(dimensions);
    // Goals can share large terms; the printer stops after `width` nodes too.
    // Kernel notation is given the context's dimensions, so that a
    // definition named as one shows by its kernel name (cubicalText).
    const printed = term => kernel ? cubicalText(term, this.displayNames, { dimensions: names })
      : sourceText(term, this.displayNames, width, notation);
    const show = term => { const text = printed(term); return text.length > width ? `${text.slice(0, width - 1)}…` : text; };
    let chained = { tag: "Pair", first: target, second: built ?? { tag: "Point" } };
    for (const [name, type] of [...context].reverse()) chained = T.pi(name, type, chained);
    // Source text is named by forSource; kernel notation shows the term as
    // it was checked, its names only settled.
    let [shown] = kernel ? [displayTerm(chained, reduce ? 256 : 0)] : forSource([chained], this.displayNaming(names, reduce ? 256 : 0));
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
  // names; a failure is a mismatch (or an exhausted resource) as the kernel
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
      judgement = this.instructed(graph, () => expected ? driver.check(raw, this.syntax.encode(expected, dimensions), assumptions, mask)
        : driver.infer(raw, assumptions, mask));
    } catch (error) {
      // The kernel's own errors pass as they are: a mismatch, or running out
      // of time, steps or representation space. Anything else is the instruction kernel's refusal.
      if (error instanceof KernelError && speculativeFailure(error.kind)) throw error;
      throw Object.assign(new KernelError(`Instruction kernel: ${error.message}`, error.kind ?? "other"), { mismatch: error.mismatch });
    }
    const renamings = [];
    for (const [symbol, entry] of driver.contextScope(assumptions, mask)) {
      if (typeof symbol !== "number") continue;
      const own = graph.entry(entry).symbol;
      if (own !== symbol) renamings.push([own, symbol]);
    }
    return this.viewOfJudgement(judgement, dimensions, renamings, graph.count - before);
  }
  // Read an already checked judgement without deriving it again. The workbench
  // retains this certificate after each native Step, including its context.
  // Its ID and handles must not be retained across checkpoint commit/rollback.
  viewOfJudgement(judgement, dimensions, renamings = [], checkingSteps = 0) {
    const graph = this.driver.graph;
    let { term: expression, type, kind } = graph.judgement(judgement);
    if (kind !== "typing") throw new TypeError("An inspected view needs a typing judgement.");
    // An assumption the driver had to name apart takes its own name back.
    for (const [own, symbol] of renamings) {
      expression = graph.rename(expression, false, own, symbol);
      type = graph.rename(type, false, own, symbol);
    }
    const arena = this.kernel.arena(), derivedHandles = this.kernel.derivedHandles ??= new Set();
    derivedHandles.add(expression).add(type);
    const names = this.kernel.variantStems?.size ? this.sourceNames ??= new SourceNames(this.kernel.variantStems) : null;
    const display = value => names ? names.apply(value) : value;
    return { expression, typeHandle: type, judgement, renamings, term: display(this.syntax.decode(expression, dimensions)),
      type: display(this.syntax.decode(type, dimensions)), checkingSteps,
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
      const eliminator = this.instructed(graph, () => clauses.reduce((opened, clause) =>
        driver.addClause(opened, driver.derive(this.syntax.encode(clause, dimensions), scope)),
      driver.openEliminator(driver.derive(this.syntax.encode(motive, dimensions), scope))));
      type = graph.judgement(eliminator).type;
      for (const [symbol, entry] of scope) {
        if (typeof symbol !== "number") continue;
        const own = graph.entry(entry).symbol;
        if (own !== symbol) type = graph.rename(type, false, own, symbol);
      }
    } catch (error) {
      if (error instanceof KernelError && speculativeFailure(error.kind)) throw this.describeMismatch(error, dimensions);
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
  // the program's checker uses: its caches hold judgements and handles, so
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
    // Unification asks for the same term's head again and again: the kernel
    // computes it once a declaration, for the term's node. A head served
    // again is no kernel query, so the deadline is polled here too, as
    // derived() polls it for a judgement reused.
    this.kernel.checkDeadline();
    const node = this.syntax.encode(term, dimensions);
    let head = this.syntax.heads.get(node);
    if (head === undefined) { head = this.kernel.head(node); this.syntax.heads.set(node, head, Math.max(node, head)); }
    return this.syntax.decode(head, dimensions);
  }
  // Whether two closed terms differ, as the driver's guide finds it: their
  // weak heads compared part by part, each with the session's step budget,
  // with nothing normalized. A conversion that fails normalizes both terms
  // first (InstructionDriver.settle), so this answers where a difference
  // shows without that; false means only that none showed. A query, which
  // certifies nothing.
  differ(left, right, dimensions = this.dimensions) {
    this.kernel.checkDeadline();
    return this.driver.differ(this.syntax.encode(left, dimensions), this.syntax.encode(right, dimensions), this.kernel.stepBudget);
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
  // runs out of resources. Any other rejection throws, as in check().
  attempt(term, expected, context = new Map(), dimensions = this.dimensions) {
    // Speculative failures are answers, not diagnostics: they are not described.
    try { return { ok: true, term: this.check(term, expected, context, dimensions, false) }; }
    catch (error) {
      if (!speculativeFailure(error?.kind)) throw error;
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
      if (cleaned === signature || error.kind === "deadline") throw this.describeMismatch(error, new Map());
      try { ({ reference, admission } = this.admit(name, this.syntax.encode(body), this.syntax.encode(cleaned))); }
      catch (retryError) {
        throw this.describeMismatch(isResourceLimit(retryError?.kind) ? retryError : error, new Map());
      }
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
    const work = this.instructionWork, { ms, judgements } = work;
    const driver = this.driver, graph = driver.graph;
    let reference;
    try {
      reference = this.instructed(graph, () => graph.judgement(graph.define(name, driver.check(body, signature))).term);
    } catch (error) {
      if (isResourceLimit(error?.kind)) throw error;
      throw Object.assign(new Error(`Instruction kernel: ${error.message}`), { kind: error.kind ?? "other" });
    } finally {
      // One driver per declaration: the next starts from a fresh one.
      this.kernel.instructionDriver = null;
    }
    this.kernel.definitions.set(name, reference);
    return { reference, admission: { ms: +(work.ms - ms).toFixed(3), judgements: work.judgements - judgements } };
  }
  // A universe-generic definition the elaborator builds, such as ua's: checked
  // and named once, and instantiated at each use.
  genericDefinition(name, elaborate) {
    if (this.genericDefinitions.has(name)) return this.genericDefinitions.get(name);
    const term = elaborate(), checked = this.infer(term);
    const value = this.define(name, checked.term, checked.type);
    this.genericDefinitions.set(name, value);
    return value;
  }
  // `with unfolding [names] { e }`: e checked as a definition of its own. The
  // names guided the retired conversion oracle; the driver's own guide
  // unfolds what a comparison needs, so they no longer matter here.
  scopedUnfolding(elaborate, context, expected = null, dimensions = this.dimensions, supply = this.names, prefix = "unfolding") {
    const raw = elaborate();
    const checked = expected ? { term: this.check(raw, expected, context, dimensions), type: expected }
      : this.infer(raw, context, dimensions);
    let term = checked.term, type = checked.type;
    // Close over local variables before interval coordinates: a variable's
    // type may itself depend on a coordinate. The helper is then checked as
    // an ordinary closed definition, not installed as an unchecked promise.
    for (const [name, domain] of [...context].reverse()) {
      if(domain.tag==="LBound") {
        term=T.levelLambda(name,term);type=T.levelPi(name,type);
      } else {
        term = T.lam(name, domain, term); type = T.pi(name, domain, type);
      }
    }
    for (const dim of [...dimensions.keys()].reverse()) {
      term = T.line(dim, type, term);
      type = T.path(dim, type, T.at(term, I.zero), T.at(term, I.one));
    }
    this.kernel.unfoldingSerial = (this.kernel.unfoldingSerial ?? 0) + 1;
    const name = `${prefix}_${this.kernel.unfoldingSerial}`;
    let result = this.define(name, this.ascribe(term, type, supply), type);
    this.scopeDefinitions.add(name);
    for (const dim of dimensions.keys()) result = T.at(result, I.variable(dim));
    for (const [name,domain] of context) result = (domain.tag==="LBound"?T.levelApply:T.app)(result, T.variable(name));
    return result;
  }

  verify(term, expected = null, assumptions = []) {
    const checked = this.evaluated(term, expected, assumptions);
    return { ...checked, normal: this.normalForm(checked.expression) };
  }
  // A term checked for evaluation, with its assumptions and kernel
  // extensions, and nothing computed: `expression` is the derived handle
  // that derivedHead and normalForm compute from.
  evaluated(term, expected = null, assumptions = []) {
    const checked = this.checkSyntax(term, expected, new Map(assumptions), this.dimensions);
    return { ...checked, native: { ok: true, arenaNodes: checked.arenaNodes, arenaBytes: checked.arenaBytes, axioms: [...this.requiredAssumptions(checked.term, checked.type).keys()],
      extensions: this.extensionsOf(checked.term, checked.type) } };
  }
  // The normal form of a derived handle, decoded: folded, a stuck
  // definition kept as written, unless the full one is asked for
  // (docs/roadmaps/historical/folded-normal-forms.md).
  normalForm(handle, { full = false } = {}) {
    return this.syntax.decode(full ? this.kernel.normalize(handle) : this.kernel.normalizeFolded(handle), this.dimensions);
  }
  // The weak head of a handle, computed once a declaration, as nf's are. The
  // head of a derived handle, and its data parts (a pair's components, an
  // injection's value, a constructor's arguments), are recorded as derived,
  // so that the kernel's normalize accepts them: the evaluation demand marks
  // normalize the parts a pattern reaches, as `!!` and expression leaves ask
  // (docs/roadmaps/historical/evaluation-demand-marks.md, decision 3).
  // The guard admits normalization only of terms whose reduction
  // terminates, and these are such terms: the weak head of a closed,
  // well-typed term is well-typed by subject reduction, and its data parts
  // are closed, well-typed subterms of it. A query certifies nothing, so no
  // instruction's acceptance depends on it.
  derivedHead(handle) {
    this.kernel.checkDeadline();
    let head = this.syntax.heads.get(handle);
    if (head === undefined) { head = this.kernel.head(handle); this.syntax.heads.set(handle, head, Math.max(handle, head)); }
    const derived = this.kernel.derivedHandles;
    if (derived?.has(handle)) {
      derived.add(head);
      const { root, args } = this.kernel.spine(head);
      if (root.kind === "Con") args.forEach(part => derived.add(part));
      else if (!args.length && root.kind === "Pair") derived.add(root.children[1]).add(root.children[2]);
      else if (!args.length && (root.kind === "Inl" || root.kind === "Inr")) derived.add(root.children[1]);
    }
    return head;
  }
  // A handle's term as the kernel holds it, nothing reduced.
  decoded(handle) { return this.syntax.decode(handle, this.dimensions); }
  // A constructor as a display shows it: its name and its declared type's
  // signature, without the type's parameters, which no display of the
  // constructor shows and which can be large, unreduced, and deep.
  // A glue value's system as a display shows it: each part's face, decoded,
  // and its term's handle, which is computed only where it is shown.
  glueSystem(handle) {
    const system = [];
    for (let part = this.kernel.node(handle).children[2]; part;) {
      const tube = this.kernel.node(part);
      system.push({ face: this.syntax.decodeFormula(tube.payload, this.dimensions), term: tube.children[0] });
      part = tube.children[1];
    }
    return system;
  }
  shownConstructor(handle) {
    const node = this.kernel.node(handle), sort = this.kernel.node(node.children[0]);
    if (sort.kind !== "Sort") return this.decoded(handle);
    const record = this.syntax.signatureRecord(sort.payload), name = record.constructors[node.payload];
    return { tag: "Con", index: node.payload, ...(name ? { name } : {}), sort: { tag: "Sort", signature: record.name, parameters: [], levels: [] } };
  }
}
