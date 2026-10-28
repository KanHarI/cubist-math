// Verify that edited library modules keep their checked meaning. The original
// and edited versions are checked in one native kernel: the edited module is
// loaded under a shadow name next to the original. Two levels are available:
// - "identical": every declaration's checked term and type are the same up to
//   the names of bound variables and generated helpers;
// - "types": every public type is the same by kernel conversion and every
//   declaration keeps the same assumptions. Proof witnesses may change.
// At both levels every declaration keeps its kernel extensions under review,
// which are compared apart from assumptions (the H1 specification's 6.4).
// None is under review since H1's release. Generative signatures are
// compared by their admitted schemas. Only an identical schema grants a
// renaming between the copies.
// A universe-generic definition is one checked term, compared like any other.
import { createHash } from "node:crypto";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { CubicalDeclarationTransaction } from "../web/cubical-transaction.mjs";
import { parse, tokenize } from "../web/cubist/parser.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { forSource } from "../web/display-naming.mjs";
import { validateLedger, ledgerMatches, retiredComparison, REPLACEMENTS } from "./migration-ledger.mjs";
import { canonicalHasher } from "./canonical-hash.mjs";

const SHADOW = "__migration_check";

// Copy a checked term with its definition references renamed, and its free
// assumptions by `variableName`, sharing every unchanged subterm. Only a
// free variable is renamed: a binder of the same spelling hides the
// assumption in its body, so a term is memoized per the renamed names bound
// around it (usually none).
const termBinders = new Set(["Pi", "Lam", "Sigma", "W", "LPi", "LLam"]);
export function mapDefinitions(rename, signatureName = name => name, variableName = name => name) {
  const memos = new Map();
  function map(node, bound = []) {
    if (!node || typeof node !== "object") return node;
    const key = bound.join("\u0000");
    let memo = memos.get(key);
    if (!memo) memos.set(key, memo = new WeakMap());
    if (memo.has(node)) return memo.get(node);
    let result = node;
    if (Array.isArray(node)) {
      const items = node.map(item => map(item, bound));
      if (items.some((item, index) => item !== node[index])) result = items;
    } else if (node.tag === "DefRef") {
      const name = rename(node.name);
      if (name !== node.name) result = { ...node, name };
    } else if (node.tag === "Var") {
      const name = bound.includes(node.name) ? node.name : variableName(node.name);
      if (name !== node.name) result = { ...node, name };
    } else {
      let copy = null;
      if ((node.tag === "Sort" || node.tag === "Elim") && signatureName(node.signature) !== node.signature)
        copy = {...node,signature:signatureName(node.signature)};
      // A binder hides a renamed name in its body.
      const hides = termBinders.has(node.tag) && variableName(node.name) !== node.name && !bound.includes(node.name);
      for (const [key, value] of Object.entries(node)) {
        const mapped = map(value, hides && key === "body" ? [...bound, node.name].sort() : bound);
        if (mapped !== value) (copy ??= { ...node })[key] = mapped;
      }
      if (copy) result = copy;
    }
    memo.set(node, result);
    return result;
  }
  return node => map(node);
}

// modules: names of the library modules to compare, normally the edited
// modules and every module that imports one of them. Each compared module is
// checked again under a shadow name whose imports of compared modules are
// replaced by their shadow versions, so dependents see the edited definitions.
// readOriginal/readEdited return module source text. Returns one report per
// module; `failures` lists every declaration that does not meet the level.
export async function verifyMigration({ modules, readOriginal, readEdited, level = "identical",
  typeTimeLimitMs = 10000, experimental, ledger = null, declarations = null } = {}) {
  if (!["identical", "types"].includes(level)) throw new Error(`Unknown verification level: ${level}`);
  if (experimental !== undefined)
    throw new Error("H1 is no longer experimental: declared types are on by default, so drop the experimental option.");
  const allowedChanges = validateLedger(ledger);
  for (const module of modules) {
    const retired = retiredComparison(ledger, module);
    if (retired) throw Error(`The ledger retired its ${module} comparison, which last passed at ${retired.lastPassing}: ${retired.reason}`);
  }
  const compared = new Set(modules), shadowOf = module => `${module}${SHADOW}`;
  const editedSources = new Map();
  // A compared module's imports and qualified names, m::x, name its shadow,
  // its own among them, as the parser reads them: by its tokens. A source
  // that does not tokenize is checked as it is, and fails as it is.
  const shadowSource = source => {
    let tokens;
    try { tokens = tokenize(source); } catch { return source; }
    const named = tokens.flatMap((token, k) => {
      const module = tokens[k - 1]?.text === "import" ? token.text : /^([A-Za-z_][A-Za-z_0-9]*)::/.exec(token.text)?.[1];
      return compared.has(module) ? [[token.start, token.start + module.length]] : [];
    });
    return named.reduceRight((text, [start, end]) => text.slice(0, start) + shadowOf(text.slice(start, end)) + text.slice(end), source);
  };
  const editedSource = async module => {
    if (!editedSources.has(module)) {
      const source = await readEdited(module);
      const place = readEdited.placeOf?.(module);
      if (place) readOriginal.place?.(shadowOf(module), place);
      editedSources.set(module, shadowSource(source));
    }
    return editedSources.get(module);
  };
  const shadowModule = name => name.endsWith(SHADOW) && compared.has(name.slice(0, -SHADOW.length))
    ? name.slice(0, -SHADOW.length) : null;
  const readSource = (name, importer) => shadowModule(name) ? editedSource(shadowModule(name)) : readOriginal(name, importer);
  readSource.beginCheck = () => readOriginal.beginCheck?.();
  // An original module read from library/ is the library's (its axioms'
  // labels); an edited shadow never is.
  readSource.fromLibrary = async (name, text) => !shadowModule(name) && (await readOriginal.fromLibrary?.(name, text) ?? false);
  readSource.checkImports = (importer, imports) => readOriginal.checkImports?.(importer, imports.filter(name => !shadowModule(name)));
  // An original module of a revision before L2.10j is read as it was then.
  readSource.nameBased = name => !shadowModule(name) && (readOriginal.nameBased?.(name) ?? false);
  const program = new CubicalProgram(await createCubical(), readSource, { collectReferences: false });
  const checker = program.checker, views = checker.definitionViews;
  // Check dependencies before the modules that import them.
  const order = [], visited = new Map();
  const visit = async module => {
    if (visited.get(module) === "done") return;
    if (visited.get(module) === "visiting") throw new Error(`Cyclic source import: ${module}`);
    visited.set(module, "visiting");
    for (const dependency of parse(await readEdited(module)).imports) if (compared.has(dependency)) await visit(dependency);
    visited.set(module, "done");
    order.push(module);
  };
  for (const module of modules) await visit(module);

  // A binding of a shadow module, split into its module and local name.
  const shadowBinding = name => {
    const index = name.indexOf(`${SHADOW}__`);
    return index > 0 && compared.has(name.slice(0, index))
      ? { module: name.slice(0, index), local: name.slice(index + SHADOW.length + 2) } : null;
  };
  const originalName = name => {
    const parts = shadowBinding(name);
    return parts ? `${parts.module}__${parts.local}` : name;
  };
  // Original bindings of declarations whose edited checked term and type are
  // identical, given that every edited definition they mention is identical.
  // Only those edited definitions may stand in for the originals.
  const identical = new Set();
  const ledgerVerified = new Set();
  const signatureCorrespondence = new Map();
  const signatureName = name => signatureCorrespondence.get(name) ?? name;
  // An edited axiom whose assumed statement is the original's stands for it,
  // as a free assumption of its dependents' terms, types and lists: by its
  // exact assumption, in a map of its own, never in `identical`.
  const axiomCorrespondence = new Map();
  const assumptionName = name => axiomCorrespondence.get(name) ?? name;
  // An edited definition stands for the original only when its own exact
  // identity was found identical: never because another declaration's
  // name begins its own, as P's does P__x's, which identifiers allow.
  const standsIn = name => !shadowBinding(name) || identical.has(originalName(name));
  // Generated unfolding helpers are named by a session serial; compare their
  // checked bodies instead of their names.
  const helper = name => /__unfolding_\d+$/.test(name) && views.has(name);
  let hashTerm;
  hashTerm = canonicalHasher({ definitionName: name => helper(name) ? `helper:${hashTerm(views.get(name).term)}`
    : standsIn(name) ? originalName(name) : `edited:${name}`, signatureName, freeVariableName: assumptionName });
  const toOriginal = mapDefinitions(name => standsIn(name) && views.has(originalName(name)) ? originalName(name) : name,
    signatureName, assumptionName);
  // Close each constructor schema over its admission symbols before
  // hashing. In particular, boundaries refer to bound earlier constructors.
  const signatureShape = (binding, hashChecked = null) => {
    const record = program.kernel.signatures.get(binding);
    if (!record) return null;
    const info = program.kernel.signature(record.index), syntax = checker.syntax;
    const former = syntax.decode(info.former), parameters = [];
    let universe = former;
    while (universe.tag === "LPi" || universe.tag === "Pi") { parameters.push(universe); universe = universe.body; }
    const hash = hashChecked ?? canonicalHasher({definitionName:name => standsIn(name) ? originalName(name) : name, signatureName});
    const earlier = [];
    const constructors = info.constructors.map(constructor => {
      const type = syntax.decode(constructor.type);
      let closed = type;
      for (const before of [...earlier].reverse()) closed = {tag:"Pi",name:before.name,domain:before.type,body:closed};
      closed = {tag:"Pi",name:program.kernel.symbolName(info.sort),domain:universe,body:closed};
      for (const parameter of [...parameters].reverse()) closed = {...parameter,body:closed};
      earlier.push({name:program.kernel.symbolName(constructor.symbol),type});
      return {type:hash(closed),data:constructor.data,positions:constructor.positions,
        dimensions:constructor.dimensions,generated:constructor.generated};
    });
    return {former:hash(former),recorded:info.recorded,modifier:info.modifier,
      names:record.constructors,constructors};
  };
  // For each edited declaration that is not identical, the declarations with
  // changed source text that make it differ.
  const roots = new Map();
  const changedReferences = term => {
    const found = new Set(), seen = new WeakSet();
    const visit = node => {
      if (!node || typeof node !== "object" || seen.has(node)) return;
      seen.add(node);
      if (node.tag === "DefRef" && !standsIn(node.name)) found.add(originalName(node.name));
      for (const value of Array.isArray(node) ? node : Object.values(node)) visit(value);
    };
    visit(term);
    return found;
  };
  const rootsOf = bindings => [...new Set([...bindings].flatMap(binding => [...(roots.get(binding) ?? [binding])]))].sort();
  const assumptions = binding => [...new Set((program.symbols[binding]?.axioms ?? []).map(assumptionName)
    .map(name => checker.assumptionLabels.get(name) ?? name))].sort().join(",");
  // Kernel extensions under review are not assumptions: a migration that
  // adds or removes one changes what the result relies on all the same.
  const extensions = binding => [...new Set(program.symbols[binding]?.extensions ?? [])].sort().join(",");
  // A pin closes over referenced checked meanings, not only their names.
  // Otherwise an unchanged `Predicate(A)` could hide a changed Predicate.
  // The checked definition/signature graph is acyclic and its syntax DAG is
  // memoized by canonicalHasher, including the types of referenced values.
  const signaturePins = new Map();
  let snapshotHash;
  snapshotHash = canonicalHasher({definitionName:name => {
    const view = views.get(name);
    return view ? `${helper(name) ? "helper" : originalName(name)}:${snapshotHash(view.term)}:${snapshotHash(view.type)}` : originalName(name);
  }, signatureName:name => {
    if (!signaturePins.has(name)) signaturePins.set(name, createHash("sha1").update(JSON.stringify(signatureShape(name,snapshotHash))).digest("hex"));
    return `${originalName(name)}:${signaturePins.get(name)}`;
  }, freeVariableName:name => {
    name = assumptionName(name);
    const label = checker.assumptionLabels.get(name) ?? name, type = checker.assumptions.get(name);
    return type ? `${label}:${snapshotHash(type)}` : label;
  }});
  const readableBindings = mapDefinitions(originalName, originalName, assumptionName);
  // Pin text uses the explicit unary view, and labels as the kernel names
  // them, no symbols, so that a pin reads alike however the elaborator
  // displays terms; it is named as every display is (forSource), closed,
  // over the original bindings. The definitions whose types and values it
  // reads, for a folded motive's domain, are the ones the term is about: for
  // an edited term, the edited module's shadows, read with original bindings
  // too. Both the rendered text and the checked structural hash remain
  // exact ledger requirements.
  const shadowed = name => {
    const index = name.indexOf("__"), module = name.slice(0, index);
    return index > 0 && compared.has(module) ? `${shadowOf(module)}__${name.slice(index + 2)}` : name;
  };
  const snapshotNaming = edited => {
    const { definitions } = checker.displayNaming([]);
    const read = part => name => {
      const term = definitions[part](edited ? shadowed(name) : name);
      return term && readableBindings(term);
    };
    return { definitions: { ...definitions, type: read("type"), value: read("value") }, symbols: {}, dimensions: [] };
  };
  const snapshot = (term, edited = false) => ({hash:snapshotHash(term),
    text:sourceText(forSource([readableBindings(term)],snapshotNaming(edited))[0],{},4000,{selection:"unat"})});
  const localReferences = (module, ...terms) => {
    const found = new Set(), seen = new WeakSet();
    const visit = node => {
      if (!node || typeof node !== "object" || seen.has(node)) return;
      seen.add(node);
      const name = node.tag === "DefRef" ? node.name : ["Sort", "Elim"].includes(node.tag) ? node.signature : null;
      if (name) {
        if (helper(name)) visit(views.get(name).term);
        // The module's own declarations, by the module that checked them,
        // not by a binding's prefix, which another module's name may share.
        const binding = originalName(name);
        if (program.symbols[binding]?.sourceModule === module) found.add(binding);
      }
      for (const value of Array.isArray(node) ? node : Object.values(node)) visit(value);
    };
    terms.forEach(visit);
    return [...found];
  };
  const difference = (a,b) => a.filter(value => !b.includes(value));
  const list = text => text ? text.split(",") : [];
  try {
    const reports = [];
    for (const module of order) {
      const original = await program.check(`import ${module};`, `${module}${SHADOW}_original_root`);
      const shadow = shadowOf(module);
      // A program reports every main module checked so far; keep this one's.
      const edited = await program.check(await editedSource(module), shadow);
      const selected = declarations?.[module];
      const included = symbol => !selected || selected.includes(symbol.name);
      const editedOutputs = edited.outputs.filter(output => output.binding.startsWith(`${shadow}__`) && included(output));
      const originalOutputs = Object.values(program.symbols).filter(symbol => symbol.sourceModule === module && included(symbol));
      const report = { module, selectedDeclarations: selected ?? null, identical: 0, typesPreserved: 0, ledgerAccepted: 0, changes: [], failures: [] };
      reports.push(report);
      const fail = (name, reason) => report.failures.push({ name, reason });
      for(const name of selected ?? []) if(!originalOutputs.some(symbol=>symbol.name===name) || !editedOutputs.some(symbol=>symbol.name===name))
        fail(name,"A selected declaration is absent from the original or edited module.");
      if (!original.complete && program.gaps.some(gap => gap.module === module))
        fail("(module)", "The original module does not fully check.");
      const originalNames = originalOutputs.map(symbol => symbol.name);
      const editedNames = editedOutputs.map(output => output.name);
      if (JSON.stringify(originalNames) !== JSON.stringify(editedNames))
        fail("(declarations)", `Declaration list changed: ${JSON.stringify(originalNames)} -> ${JSON.stringify(editedNames)}`);
      const declarationText = source => new Map(parse(source).declarations.map(declaration =>
        [declaration.name.text, source.slice(declaration.start, declaration.end).replace(/\s+/g, " ")]));
      const [originalText, editedText] = [declarationText(await readOriginal(module)), declarationText(await readEdited(module))];
      const parametersOf = source => new Map(parse(source).declarations.map(declaration =>
        [declaration.name.text,(declaration.params ?? []).map(parameter => parameter.name.text)]));
      const [oldParameters,newParameters] = [parametersOf(await readOriginal(module)),parametersOf(await readEdited(module))];
      const compare = (name, before, after, originalBinding, editedBinding) => {
        if (!before || !after) return fail(name, "No checked definition to compare.");
        const binding = `${module}__${name}`;
        const own = originalText.get(name) !== editedText.get(name) ? [binding] : [];
        const recordRoots = () => roots.set(binding,
          new Set([...own, ...rootsOf(new Set([...changedReferences(after.term), ...changedReferences(after.type)]))]));
        const oldAssumptions = list(assumptions(originalBinding)), newAssumptions = list(assumptions(editedBinding));
        const oldExtensions = list(extensions(originalBinding)), newExtensions = list(extensions(editedBinding));
        const removed = difference(oldAssumptions,newAssumptions), added = difference(newAssumptions,oldAssumptions);
        // A legacy builtin removed where the library's axiom of its name is
        // added, which a ledger entry must still list.
        const assumptionsReplaced = [...REPLACEMENTS].filter(([old,value]) => removed.includes(old) && added.includes(value))
          .map(([old,value]) => ({old,new:value}));
        const observed = {module,declaration:name,oldPublicType:snapshot(before.type),newPublicType:snapshot(after.type,true),
          oldValue:snapshot(before.term),newValue:snapshot(after.term,true),assumptionsReplaced,
          hypothesesAdded:difference(newParameters.get(name) ?? [],oldParameters.get(name) ?? []),
          assumptionsRemoved:removed.filter(label => !assumptionsReplaced.some(change => change.old === label)),
          assumptionsRetained:oldAssumptions.filter(value => newAssumptions.includes(value)),
          assumptionsAdded:added.filter(label => !assumptionsReplaced.some(change => change.new === label)),extensionsAdded:difference(newExtensions,oldExtensions),
          extensionsRetained:oldExtensions.filter(value => newExtensions.includes(value)),extensionsRemoved:difference(oldExtensions,newExtensions)};
        report.changes.push(observed);
        const permission = allowedChanges.get(binding);
        if (permission) {
          const reason = ledgerMatches(permission, observed);
          if (reason) return fail(name, reason);
          for (const reference of localReferences(module, before.type, after.type)) {
            if (reference === binding) continue;
            if (!originalOutputs.some(symbol => symbol.binding === reference))
              return fail(name, `Ledger dependency ${reference} is outside this comparison's scope.`);
            if (!identical.has(reference) && !ledgerVerified.has(reference))
              return fail(name, `Ledger dependency ${reference} must be identical or have its own verified ledger entry.`);
          }
          // A type former's public type is its returned type construction,
          // pinned by oldValue/newValue. Both versions may already carry H1
          // through Nat, even when the new returned type uses truncation.
          const typeFormer = type => {
            let end = checker.nf(type);
            while (end.tag === "Pi" || end.tag === "LPi") end = end.body;
            return end.tag === "U";
          };
          const changedTypeFormer = typeFormer(before.type) && typeFormer(after.type)
            && observed.oldValue.hash !== observed.newValue.hash;
          if (!changedTypeFormer && observed.oldPublicType.hash === observed.newPublicType.hash && assumptions(originalBinding) === assumptions(editedBinding)
            && extensions(originalBinding) === extensions(editedBinding))
            return fail(name,"The ledger entry records no public type, assumption or extension change; use ordinary verification for proof changes.");
          ledgerVerified.add(binding); recordRoots(); report.ledgerAccepted++; return;
        }
        if (assumptions(originalBinding) !== assumptions(editedBinding))
          return fail(name, `Assumptions changed: ${assumptions(originalBinding)} -> ${assumptions(editedBinding)}`);
        if (extensions(originalBinding) !== extensions(editedBinding))
          return fail(name, `Kernel extensions changed: ${extensions(originalBinding) || "none"} -> ${extensions(editedBinding) || "none"}`);
        if (hashTerm(before.term) === hashTerm(after.term) && hashTerm(before.type) === hashTerm(after.type)) {
          identical.add(binding); report.identical++; return;
        }
        recordRoots();
        if (level === "identical") return fail(name, "The checked term changed.");
        const through = rootsOf(changedReferences(after.type)).filter(root => root !== binding);
        let same, reason = "The public type changed.";
        // Roll the comparison back, so an interrupted check cannot leave
        // native state behind for later modules.
        const transaction = new CubicalDeclarationTransaction(program.kernel, checker);
        program.kernel.setDeadline(typeTimeLimitMs);
        try { same = checker.equal(before.type, toOriginal(after.type)); }
        catch (error) {
          same = false;
          if (error.kind === "deadline")
            reason = `The public types were not shown convertible within ${typeTimeLimitMs} ms.`;
        } finally { program.kernel.setDeadline(); transaction.finish(false); }
        if (same) report.typesPreserved++;
        else fail(name, through.length ? `${reason} It mentions changed definitions from: ${through.join(", ")}.` : reason);
      };
      // An axiom has no definition to compare: its assumed statement is
      // compared instead, as a declaration's public type is. The same
      // statement, or at level types a convertible one, makes the edited
      // axiom stand for the original; a changed one is reported, as a
      // changed type is. What the statements rely on is compared first:
      // every other assumption, by its correspondence, and every kernel
      // extension.
      const compareAxiom = (name, originalBinding, editedBinding) => {
        const original = checker.axioms.get(originalBinding), edited = checker.axioms.get(editedBinding);
        if (!original || !edited) return fail(name, "One version assumes this declaration as an axiom, and the other defines it.");
        const [before, after] = [checker.assumptions.get(original), checker.assumptions.get(edited)];
        const reliedOn = statement => [...new Set([...checker.requiredAssumptions(statement).keys()].map(assumptionName)
          .map(name => checker.assumptionLabels.get(name) ?? name))].sort().join(",");
        if (reliedOn(before) !== reliedOn(after))
          return fail(name, `The axiom's statement relies on other assumptions: ${reliedOn(before) || "none"} -> ${reliedOn(after) || "none"}`);
        if (extensions(originalBinding) !== extensions(editedBinding))
          return fail(name, `Kernel extensions changed: ${extensions(originalBinding) || "none"} -> ${extensions(editedBinding) || "none"}`);
        if (hashTerm(before) === hashTerm(after)) {
          axiomCorrespondence.set(edited, original); report.identical++; return;
        }
        if (level === "identical") return fail(name, "The axiom's assumed statement changed.");
        // As a public type is compared: bounded kernel conversion, rolled back.
        let same, reason = "The axiom's assumed statement changed.";
        const transaction = new CubicalDeclarationTransaction(program.kernel, checker);
        program.kernel.setDeadline(typeTimeLimitMs);
        try { same = checker.equal(before, toOriginal(after)); }
        catch (error) {
          same = false;
          if (error.kind === "deadline")
            reason = `The axiom's assumed statements were not shown convertible within ${typeTimeLimitMs} ms.`;
        } finally { program.kernel.setDeadline(); transaction.finish(false); }
        if (!same) return fail(name, reason);
        axiomCorrespondence.set(edited, original); report.typesPreserved++;
      };
      // Establish schema correspondences before comparing terms that use
      // them. This grants a verifier renaming, never kernel conversion
      // between different generative sorts.
      for (const symbol of originalOutputs.filter(symbol => symbol.kind === "inductive")) {
        const output = editedOutputs.find(item => item.name === symbol.name);
        if (!symbol.verified || !output?.verified) continue;
        if (JSON.stringify(signatureShape(symbol.binding)) !== JSON.stringify(signatureShape(output.binding)))
          fail(symbol.name,"The admitted signature changed: former, levels, modifier, constructors or boundaries.");
        else { signatureCorrespondence.set(output.binding,symbol.binding); identical.add(`${module}__${symbol.name}`); report.identical++; }
      }
      for (const symbol of originalOutputs) {
        const output = editedOutputs.find(item => item.name === symbol.name);
        if (!output) continue;
        if (symbol.verified && !output.verified) { fail(symbol.name, `No longer checks: ${output.reason}`); continue; }
        if (!symbol.verified) {
          fail(symbol.name,`The original declaration has no checked image: ${symbol.reason ?? "it did not check"}`);
          continue;
        }
        if (symbol.kind === "inductive") {
          continue;
        }
        // In source order, so that a statement's earlier definitions are decided.
        if (checker.axioms.has(symbol.binding) || checker.axioms.has(output.binding)) {
          compareAxiom(symbol.name, symbol.binding, output.binding);
          continue;
        }
        compare(symbol.name, views.get(symbol.binding), views.get(output.binding), symbol.binding, output.binding);
      }
      for (const key of allowedChanges.keys()) if (key.startsWith(`${module}__`)
        && !report.changes.some(change => `${module}__${change.declaration}` === key))
        fail(key.slice(module.length+2),"The ledger entry has no pair of checked declarations.");
    }
    return reports;
  } finally { program.dispose(); }
}
