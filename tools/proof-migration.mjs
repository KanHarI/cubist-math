// Verify that edited library modules keep their checked meaning. The original
// and edited versions are checked in one native kernel: the edited module is
// loaded under a shadow name next to the original. Two levels are available:
// - "identical": every declaration's checked term and type are the same up to
//   the names of bound variables and generated helpers;
// - "types": every public type is the same by kernel conversion and every
//   declaration keeps the same assumptions. Proof witnesses may change.
// At both levels every declaration keeps its kernel extensions under review,
// such as H1, which are compared apart from assumptions (the H1
// specification's 6.4). Generative signatures are compared by their admitted
// schemas. Only an identical schema grants a renaming between the copies.
// A universe-generic definition is one checked term, compared like any other.
import { createHash } from "node:crypto";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { CubicalDeclarationTransaction } from "../web/cubical-transaction.mjs";
import { parse } from "../web/mathscript/parser.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { displayTerm } from "../web/cubical-elaborator.mjs";
import { validateLedger, ledgerMatches } from "./migration-ledger.mjs";

const SHADOW = "__migration_check";
const termBinders = new Set(["Pi", "Lam", "Sigma", "W", "LPi", "LLam"]);
// Which fields a dimension binder scopes, matching the core syntax rules.
const dimensionScope = { Path: ["family"], PLam: ["family", "body"], Comp: ["family", "system"],
  HComp: ["system"], Trans: ["family"] };

// Hash checked syntax up to renaming of bound term variables and dimensions.
// Shared subterms are hashed once for each assignment of their free names, so
// a compact DAG is never expanded into a tree.
export function canonicalHasher({ definitionName = name => name, signatureName = name => name,
  freeVariableName = name => name } = {}) {
  const freeMemo = new WeakMap(), hashMemo = new WeakMap();
  const formulaNames = formula => formula.flat().map(literal => literal.slice(0, -2));
  function free(node) {
    if (!node || typeof node !== "object") return [];
    if (freeMemo.has(node)) return freeMemo.get(node);
    const names = new Set();
    const add = (values, except = null) => { for (const name of values) if (name !== except) names.add(name); };
    if (Array.isArray(node)) node.forEach(child => add(free(child)));
    else if (node.tag === "Var") names.add(`t:${node.name}`);
    else for (const [key, value] of Object.entries(node)) {
      // face and arg hold interval formulas, except App.arg, which is a term.
      if ((key === "face" || key === "arg") && Array.isArray(value)) { add(formulaNames(value).map(name => `d:${name}`)); continue; }
      if (!value || typeof value !== "object") continue;
      let except = null;
      if (termBinders.has(node.tag) && key === "body") except = `t:${node.name}`;
      if (dimensionScope[node.tag]?.includes(key)) except = `d:${node.dim}`;
      add(free(value), except);
    }
    const result = [...names].sort();
    freeMemo.set(node, result);
    return result;
  }
  // scope maps each bound name to the depth of its binder. A bound name is
  // hashed as its distance to that binder (a de Bruijn index), so a subterm's
  // hash depends only on the subterm and the indices of its free names.
  function hash(node, scope, depth) {
    if (node === null || typeof node !== "object") return JSON.stringify(node ?? null);
    const index = name => scope.has(name) ? `#${depth - 1 - scope.get(name)}` : null;
    const names = free(node), key = names.map(name => index(name) ?? name).join("\u0000");
    let byScope = hashMemo.get(node);
    if (!byScope) hashMemo.set(node, byScope = new Map());
    if (byScope.has(key)) return byScope.get(key);
    const digest = createHash("sha1");
    const inner = name => new Map(scope).set(name, depth);
    if (Array.isArray(node)) {
      digest.update("[");
      for (const child of node) digest.update(hash(child, scope, depth) + ",");
    } else {
      digest.update(node.tag ?? "{");
      for (const fieldName of Object.keys(node).sort()) {
        const value = node[fieldName];
        if (fieldName === "tag") continue;
        // Con.name is display metadata. Constructor identity is its index
        // in a sort whose admitted schema also compares constructor names.
        if ((termBinders.has(node.tag) && fieldName === "name") || (dimensionScope[node.tag] && fieldName === "dim")
          || node.tag === "Con" && fieldName === "name") continue;
        digest.update(`|${fieldName}=`);
        if (node.tag === "Var" && fieldName === "name") digest.update(index(`t:${value}`) ?? `free:${freeVariableName(value)}`);
        else if (node.tag === "DefRef" && fieldName === "name") digest.update(definitionName(value));
        else if ((node.tag === "Sort" || node.tag === "Elim") && fieldName === "signature") digest.update(signatureName(value));
        else if ((fieldName === "face" || fieldName === "arg") && Array.isArray(value))
          digest.update(JSON.stringify(value.map(clause => clause.map(literal => {
            const name = literal.slice(0, -2);
            return `${index(`d:${name}`) ?? `free:${name}`}${literal.slice(-2)}`;
          }).sort()).sort()));
        else if (value && typeof value === "object") {
          let childScope = scope, childDepth = depth;
          if (termBinders.has(node.tag) && fieldName === "body") { childScope = inner(`t:${node.name}`); childDepth++; }
          if (dimensionScope[node.tag]?.includes(fieldName)) { childScope = inner(`d:${node.dim}`); childDepth++; }
          digest.update(hash(value, childScope, childDepth));
        } else digest.update(JSON.stringify(value));
      }
    }
    const result = digest.digest("hex");
    byScope.set(key, result);
    return result;
  }
  return term => hash(term, new Map(), 0);
}

// Copy a checked term with its definition references renamed, sharing every
// unchanged subterm.
function mapDefinitions(rename, signatureName = name => name) {
  const memo = new WeakMap();
  function map(node) {
    if (!node || typeof node !== "object") return node;
    if (memo.has(node)) return memo.get(node);
    let result = node;
    if (Array.isArray(node)) {
      const items = node.map(map);
      if (items.some((item, index) => item !== node[index])) result = items;
    } else if (node.tag === "DefRef") {
      const name = rename(node.name);
      if (name !== node.name) result = { ...node, name };
    } else {
      let copy = null;
      if ((node.tag === "Sort" || node.tag === "Elim") && signatureName(node.signature) !== node.signature)
        copy = {...node,signature:signatureName(node.signature)};
      for (const [key, value] of Object.entries(node)) {
        const mapped = map(value);
        if (mapped !== value) (copy ??= { ...node })[key] = mapped;
      }
      if (copy) result = copy;
    }
    memo.set(node, result);
    return result;
  }
  return map;
}

// modules: names of the library modules to compare, normally the edited
// modules and every module that imports one of them. Each compared module is
// checked again under a shadow name whose imports of compared modules are
// replaced by their shadow versions, so dependents see the edited definitions.
// readOriginal/readEdited return module source text. Returns one report per
// module; `failures` lists every declaration that does not meet the level.
export async function verifyMigration({ modules, readOriginal, readEdited, level = "identical",
  typeTimeLimitMs = 10000, experimental = [], ledger = null, declarations = null } = {}) {
  if (!["identical", "types"].includes(level)) throw new Error(`Unknown verification level: ${level}`);
  const allowedChanges = validateLedger(ledger);
  const compared = new Set(modules), shadowOf = module => `${module}${SHADOW}`;
  const editedSources = new Map();
  const editedSource = async module => {
    if (!editedSources.has(module)) {
      const source = await readEdited(module);
      const place = readEdited.placeOf?.(module);
      if (place) readOriginal.place?.(shadowOf(module), place);
      editedSources.set(module, source.replace(/^(\s*import\s+)([A-Za-z_][A-Za-z_0-9]*)(\s*;)/gm,
        (text, head, name, tail) => compared.has(name) ? `${head}${shadowOf(name)}${tail}` : text));
    }
    return editedSources.get(module);
  };
  const shadowModule = name => name.endsWith(SHADOW) && compared.has(name.slice(0, -SHADOW.length))
    ? name.slice(0, -SHADOW.length) : null;
  const readSource = (name, importer) => shadowModule(name) ? editedSource(shadowModule(name)) : readOriginal(name, importer);
  readSource.beginCheck = () => readOriginal.beginCheck?.();
  readSource.checkImports = (importer, imports) => readOriginal.checkImports?.(importer, imports.filter(name => !shadowModule(name)));
  const program = new CubicalProgram(await createCubical(), readSource, { collectReferences: false, experimental });
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
  const standsIn = name => {
    const parts = shadowBinding(name);
    return !parts || identical.has(`${parts.module}__${parts.local.split("__")[0]}`);
  };
  // Generated unfolding helpers are named by a session serial; compare their
  // checked bodies instead of their names.
  const helper = name => /__unfolding_\d+$/.test(name) && views.has(name);
  let hashTerm;
  hashTerm = canonicalHasher({ definitionName: name => helper(name) ? `helper:${hashTerm(views.get(name).term)}`
    : standsIn(name) ? originalName(name) : `edited:${name}`, signatureName });
  const toOriginal = mapDefinitions(name => standsIn(name) && views.has(originalName(name)) ? originalName(name) : name, signatureName);
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
      experimental:info.experimental,names:record.constructors,constructors};
  };
  // For each edited declaration that is not identical, the declarations with
  // changed source text that make it differ.
  const roots = new Map();
  const changedReferences = term => {
    const found = new Set(), seen = new WeakSet();
    const visit = node => {
      if (!node || typeof node !== "object" || seen.has(node)) return;
      seen.add(node);
      if (node.tag === "DefRef" && !standsIn(node.name)) {
        const parts = shadowBinding(node.name);
        found.add(`${parts.module}__${parts.local.split("__")[0]}`);
      }
      for (const value of Array.isArray(node) ? node : Object.values(node)) visit(value);
    };
    visit(term);
    return found;
  };
  const rootsOf = bindings => [...new Set([...bindings].flatMap(binding => [...(roots.get(binding) ?? [binding])]))].sort();
  const assumptions = binding => [...new Set((program.symbols[binding]?.axioms ?? [])
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
    const label = checker.assumptionLabels.get(name) ?? name, type = checker.assumptions.get(name);
    return type ? `${label}:${snapshotHash(type)}` : label;
  }});
  const readableBindings = mapDefinitions(originalName, originalName);
  const snapshot = term => ({hash:snapshotHash(term),text:sourceText(displayTerm(readableBindings(term)))});
  const localReferences = (module, ...terms) => {
    const found = new Set(), seen = new WeakSet();
    const visit = node => {
      if (!node || typeof node !== "object" || seen.has(node)) return;
      seen.add(node);
      const name = node.tag === "DefRef" ? node.name : ["Sort", "Elim"].includes(node.tag) ? node.signature : null;
      if (name) {
        if (helper(name)) visit(views.get(name).term);
        const binding = originalName(name);
        if (binding.startsWith(`${module}__`)) found.add(`${module}__${binding.slice(module.length+2).split("__")[0]}`);
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
        const assumptionsReplaced = [];
        for (const old of ["LEM", "Choice"]) {
          const variants = added.filter(label => [...checker.assumptionOrigins].some(([symbol, origin]) =>
            origin.kind === "generic-assumption" && origin.name === old && origin.truncateSignature
            && checker.assumptionLabels.get(symbol) === label));
          if (removed.includes(old) && variants.length === 1) assumptionsReplaced.push({old,new:variants[0]});
        }
        const observed = {module,declaration:name,oldPublicType:snapshot(before.type),newPublicType:snapshot(after.type),
          oldValue:snapshot(before.term),newValue:snapshot(after.term),assumptionsReplaced,
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
          if (observed.oldPublicType.hash === observed.newPublicType.hash && assumptions(originalBinding) === assumptions(editedBinding)
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
        compare(symbol.name, views.get(symbol.binding), views.get(output.binding), symbol.binding, output.binding);
      }
      for (const key of allowedChanges.keys()) if (key.startsWith(`${module}__`)
        && !report.changes.some(change => `${module}__${change.declaration}` === key))
        fail(key.slice(module.length+2),"The ledger entry has no pair of checked declarations.");
    }
    return reports;
  } finally { program.dispose(); }
}
