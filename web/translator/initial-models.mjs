// L2.6's retained construction-and-fold prototype. This does not register
// an initial/free capability: deriving and the universal proofs are pending.
// The expansion is ordinary syntax, checked with no new kernel rule.
import {theoryBinding, usesScope, failedExpansion} from "./theories.mjs";
import {universeAt, nodes} from "../cubist/theories.mjs";
import {freeNames, substituted, renamedFree, allNames, relocated, unlinked, freshName, fixedBinders} from "../cubist/scopes.mjs";
import {assignArguments} from "./arguments.mjs";
import {Scope} from "./elaboration.mjs";
import {repeatedName} from "./names.mjs";
import {T as Term} from "./core.mjs";
import {reference} from "../cubist/references.mjs";

// The declarations an initial or free model expands to, checked in its
// place; one that does not expand fails as a declaration of its name.
export function initialDeclarations(t, module, d, env, declarations) {
  const unit = module.declaration(t.declarationFuel).with({references: null});
  try { return expand(t, unit, d, env); }
  catch (failure) { return failedExpansion(t, d, env, declarations, unit.locate(failure, d.name)); }
  finally { unit.fuel.close(); }
}

function expand(t, module, d, env) {
  // Generated syntax stands at the declared name and is synthetic: it links
  // nowhere, while the header's own syntax keeps its positions and links.
  const N = d.name.text, at = {start: d.name.start, end: d.name.end, synthetic: true}, free = d.kind === "free";
  const token = text => nodes.token(text, at), name = text => nodes.name(text, at);
  const call = (fn, args) => args.length ? nodes.call(fn, args, at) : typeof fn === "string" ? name(fn) : fn;
  const named = (label, value) => ({kind: "namedArgument", name: token(label), value, ...at});
  const lambda = (binder, body) => ({kind: "lambda", name: token(binder), body, ...at});
  const lambdas = (binders, body) => binders.reduceRight((inner, b) => lambda(b, inner), body);
  const head = d.theory.kind === "call" ? d.theory.fn : d.theory;
  const entry = head.kind === "name" ? env.get(theoryBinding(head.name)) : null;
  // A theory that failed its own check is a dependency here, as at its
  // other uses, whether or not it expanded: one whose use was refused has
  // no notation to read its fields in (theories.mjs, capturedNotation).
  const failed = head.kind === "name" ? env.get(head.name) : null;
  if (failed?.tag === "Untranslated" || entry?.tag === "Theory" && !entry.notation)
    throw module.locate(Object.assign(Error(`Untranslated dependency: ${head.name}`), {blockedBy: failed?.binding ?? head.name}), head);
  if (entry?.tag !== "Theory")
    throw module.locate(notATheory(d.kind, module.source.slice(d.theory.start, d.theory.end).trim()), d.theory);
  const record = entry.record, T = record.name;
  // Only copied field expressions read the theory's captured notation.
  // The header, generator type and elaborated arguments keep the caller's.
  const inTheory = body => ({kind: "notationScope", aliases: entry.notation, body, ...at});
  const repeated = repeatedName(d.params);
  if (repeated) throw module.locate(Error(`${N} has two parameters named ${repeated.name.text}: give each its own name.`), repeated.name);

  // Names from a theory's fields retain their meaning under the free
  // declaration's parameters, and a field's pattern, which substitution
  // cannot rename, never captures one. A colliding parameter is renamed with
  // a prime, as printing marks a shadowed name, which no source spells: it
  // keeps its public label, and later parameter groups and user expressions
  // follow.
  const globals = new Set([N, T, "IsSet", "IsProp", "refl", ...record.fields.flatMap(f => [...freeNames(f.type)])]);
  const fixed = new Set(record.fields.flatMap(f => [...fixedBinders(f.type)]));
  const taken = new Set([...allNames(d), ...record.fields.flatMap(f => [...allNames(f.type)]), ...globals]);
  const fresh = stem => freshName(stem, taken);
  // Only the model's own name can then be captured, where a field's pattern
  // binds it and the expansion writes the model or an operation under it.
  const put = (node, map, field) => substituted(node, map, n => module.locate(capturedModel(T, field, n), d.theory));
  const renaming = new Map(), params = [];
  const apart = node => renamedFree(node, n => renaming.get(n));
  for (let k = 0; k < d.params.length;) {
    const group = d.params[k].group, members = [];
    while (k < d.params.length && d.params[k].group === group) members.push(d.params[k++]);
    const changes = members.map(p => [p.name.text, globals.has(p.name.text) || fixed.has(p.name.text) ? `${p.name.text}′` : p.name.text]);
    for (const [j, p] of members.entries()) params.push({...p, name: {...p.name, text: changes[j][1]}, label: p.name.text,
      ...(p.bound ? {bound: apart(p.bound)} : {type: apart(p.type)})});
    for (const [before, after] of changes) renaming.set(before, after);
  }
  const theory = d.theory.kind === "call" ? {...d.theory, args: d.theory.args.map(apart)} : d.theory;
  const on = free ? apart(d.on) : null;
  if (free && freeNames(on).has(N)) throw module.locate(recursiveGenerators(N), d.on);
  // The carrier is published before its model and folds. It must not
  // replace a global those declarations still need to read by name.
  const fieldScope = new Set([...record.fields.map(f => f.name), ...record.params.map(p => p.name),
    ...record.universes.map((_, k) => universeAt(k))]);
  if (env.has(N) && (freeNames([theory, ...params.map(p => p.bound ?? p.type), ...(d.uses ?? [])], new Set(params.map(p => p.name.text))).has(N)
      || record.fields.some(f => freeNames(f.type, fieldScope).has(N))))
    throw module.locate(hiddenDependency(N), d.name);
  const args = theory.kind === "call" ? theory.args : [];
  const parameters = [...record.universes.map(name => ({name})), ...record.params];
  const argument = assignArguments({...theory, args}, parameters, module, T);
  if (args.length !== parameters.length)
    throw module.locate(theoryArguments(T, parameters.length, args.length), d.theory);

  // Check the theory application before substituting its arguments into
  // field types. This uses ordinary application checking, in the header's
  // scope and notation, so a bad argument fails once at its own source span.
  let checked = args.length ? {...theory, args: parameters.map((p, k) => named(p.name, argument(k)))} : theory;
  for (let k = params.length - 1; k >= 0;) {
    const group = params[k].group, members = [];
    while (k >= 0 && params[k].group === group) members.unshift(params[k--]);
    checked = {kind: "binderGroup", binderKind: "lambda", names: members.map(p => p.name),
      ...(members[0].bound ? {bound: members[0].bound} : {domain: members[0].type}), body: checked, ...at};
  }
  const scope = usesScope(t, new Scope(module, new Map(), env), d.uses);
  const application = t.term(checked, scope);
  scope.infer(application);
  // Keep the elaborated arguments: a hole solved by the call is no longer
  // a hole when substituted into a carrier universe or constructor domain.
  // Abstract over the free declaration's parameters, then instantiate in
  // each generated declaration's scope; the checking scope's local names
  // cannot escape into a later declaration.
  const telescope = [], values = [];
  let applied = application;
  for (let k = 0; k < params.length; k++) { telescope.push(applied); applied = applied.body; }
  for (let k = parameters.length - 1; k >= 0; k--) {
    const value = applied.tag === "LApp" ? Term.universe(applied.level) : applied.arg;
    values[k] = {kind: "instantiated", value: telescope.reduceRight((body, binder) => ({...binder, body}), value),
      args: params.map(p => name(p.name.text)), ...at};
    applied = applied.fn;
  }
  const given = new Map([...record.universes.map((_, k) => [universeAt(k), values[k]]),
    ...record.params.map((p, k) => [p.name, values[record.universes.length + k]])]);

  const carriers = record.fields.filter(f => f.kind === "sort");
  if (carriers.length !== 1 || carriers[0].family) throw module.locate(notOneCarrier(T, carriers), d.theory);
  const carrier = carriers[0].name;
  const evidence = record.fields.find(f => f.kind === "evidence" && f.of === carrier);
  if (!evidence) throw module.locate(untruncatedCarrier(T, carrier), d.theory);
  const level = evidence.evidence === "IsSet" ? "set" : "prop";
  const universe = relocated(put(carriers[0].type, given, carrier), at);
  const names = params.map(p => p.name.text), self = call(N, names.map(name));
  const operations = record.fields.filter(f => f.kind === "operation").map(f => f.name);
  // The proofs: each law's name and the carrier evidence's, to "law" or "evidence".
  const proofs = new Map(record.fields.filter(f => f.kind === "law" || f.kind === "evidence").map(f => [f.name, f.kind]));
  const constructor = field => `${N}.${field}`;
  const inside = new Map([...given, [carrier, self], ...operations.map(op => [op, name(constructor(op))])]);

  // A domain must be the carrier or independent of it, including the
  // earlier carrier-typed variables and carrier-valued operations, and of
  // the proofs. Shared domains are read before any of their group's names
  // binds. `dependent` gives what each such name is: "carrier", or a
  // proof's kind.
  const shape = field => {
    const binders = [], bound = new Set(), flattened = new Set();
    const dependent = new Map([[carrier, "carrier"], ...operations.map(op => [op, "carrier"]), ...proofs]);
    let body = field.type, placed = relocated(put(field.type, inside, field.name), at), dependency = null;
    for (const n of allNames(placed)) taken.add(n);
    for (let group = 0; body?.kind === "forall" || body?.kind === "binderGroup" && body.binderKind === "forall";
        body = body.body, placed = placed.body, group++) {
      const names = body.kind === "forall" ? [body.name] : body.names;
      const placedNames = placed.kind === "forall" ? [placed.name] : placed.names;
      if (body.bound) throw module.locate(universeArguments(field.name), d.theory);
      const domain = body.domain, isCarrier = domain.kind === "name" && domain.name === carrier && !bound.has(carrier);
      const on = isCarrier ? null : [...freeNames(domain)].find(n => dependent.has(n));
      if (on) dependency ??= {binder: names[0].text, on, kind: dependent.get(on)};
      // Nested quantifiers may shadow each other; a constructor's flat
      // parameter list may not. Rename in the body only: this group's
      // domain still reads the preceding binders.
      const renaming = new Map();
      for (const n of placedNames) {
        const name = flattened.has(n.text) ? fresh(n.text) : n.text;
        if (name !== n.text) renaming.set(n.text, name);
        flattened.add(name);
        binders.push({name, carrier: isCarrier, type: placed.domain, group});
      }
      if (renaming.size) placed = {...placed, body: renamedFree(placed.body, n => renaming.get(n))};
      for (const n of names) { bound.add(n.text); if (isCarrier) dependent.set(n.text, "carrier"); else dependent.delete(n.text); }
    }
    return {binders, body, bound, placed, dependency};
  };

  const constructors = [], operationShapes = [], lawShapes = [];
  for (const field of record.fields) {
    if (field.kind === "sort" || field.kind === "evidence") continue;
    const {binders, body, bound, placed, dependency} = shape(field);
    if (field.kind === "law" && (!(body.kind === "binary" && body.operator === "=")
        || [...freeNames(body, bound)].some(n => proofs.has(n))))
      throw module.locate(notEquational(field.name), d.theory);
    if (dependency) throw module.locate(dependency.kind === "carrier" ? notPositive(field.name, dependency.binder, carrier)
      : onProof(field.name, dependency.binder, dependency.kind, dependency.on), d.theory);
    const params = binders.map(b => ({name: token(b.name), type: inTheory(b.type), group: b.group}));
    if (field.kind === "operation") {
      if (body.kind === "binary" && body.operator === "->") throw module.locate(arrowOperation(field.name), d.theory);
      if (!(body.kind === "name" && body.name === carrier && !bound.has(carrier))) throw module.locate(notCarrierValued(field.name, carrier), d.theory);
      operationShapes.push({name: field.name, binders});
      constructors.push({kind: "constructor", name: token(constructor(field.name)), params, type: null, ...at});
    } else {
      lawShapes.push({name: field.name, binders});
      constructors.push({kind: "constructor", name: token(constructor(field.name)), params, type: inTheory(placed), ...at});
    }
  }
  for (const f of [...operationShapes, ...lawShapes]) for (const b of f.binders) taken.add(b.name);
  const v = Object.fromEntries(["target", "evidence", "g", "x", "a"].map(stem => [stem, fresh(stem)]));
  // A clause's variables take names no source spells, as the match
  // compiler's do (patterns.mjs), so that no constructor in scope, of the
  // generators' type or another, is read for one. A dimension's stem
  // names it in the kernel.
  let spelled = 0;
  const variable = stem => ({text: `${stem}'${++spelled}`, stem, ...at});
  const xs = Array.from({length: Math.max(0, ...[...operationShapes, ...lawShapes].map(f => f.binders.length))}, (_, k) => fresh(`x${k}`));
  if (free) constructors.unshift({kind: "constructor", name: token(constructor("gen")),
    params: [{name: token(v.a), type: on, group: 0}], type: null, ...at});
  const generated = {initial: N}, uses = d.uses ? {uses: d.uses} : {};
  // The kernel decides whether each law's sides are constructor
  // expressions, after beta reduction; `laws` names the law it refuses.
  const laws = Object.fromEntries(lawShapes.map(f => [constructor(f.name), f.name]));
  const inductive = {kind: "inductive", name: d.name, params, result: {modifier: {kind: level, ...at}, universe},
    constructors, start: d.start, end: d.end, generated: {...generated, laws, theorySpan: {start: d.theory.start, end: d.theory.end}}, ...uses};

  const ownModel = call(constructor("model"), names.map(name));
  const variables = f => xs.slice(0, f.binders.length);
  const target = field => name(`${v.target}.${field}`);
  // The header's syntax links in the declaration that first reads it: the
  // parameters and generator type in the inductive, the theory in the
  // model. Later declarations read copies that link nowhere.
  const again = {params: unlinked(params), theory: unlinked(theory), on: free ? unlinked(on) : null};
  const generator = free ? [[v.g, {kind: "binary", operator: "->", left: again.on, right: target(carrier), ...at}]] : [];
  const recurse = (proof, x) => call(constructor("fold_map"), [...names.map(name), name(v.target), proof, ...(free ? [name(v.g)] : []), x]);
  const mapped = (proof, f, vars = variables(f)) => f.binders.map((b, k) => b.carrier ? recurse(proof, name(vars[k])) : name(vars[k]));
  const definition = (suffix, extra, type, value) => ({kind: "def", name: token(constructor(suffix)),
    params: [...again.params, ...extra.map(([n, type], k) => ({name: token(n), type, group: d.params.length + k}))],
    type, body: [{kind: "exact", value, ...at}], typedValue: true, ...at, generated, ...uses});
  const model = definition("model", [], theory, call(reference(record.makeReference, record.make, at), [named(carrier, self), named(evidence.name, name("_")),
    ...[...operationShapes, ...lawShapes].map(f => named(f.name, lambdas(variables(f), call(constructor(f.name), variables(f).map(name)))))]));
  const clause = (field, stems, body, dimension = null) => {
    const args = stems.map(variable), i = dimension && variable(dimension);
    return {kind: "clause", constructor: token(constructor(field)), args, binders: [], coordinates: i ? [i] : [],
      body: body(args.map(a => a.text), i?.text), ...at};
  };
  const clauses = [
    ...(free ? [clause("gen", ["a"], ([a]) => call(v.g, [name(a)]))] : []),
    ...operationShapes.map(f => clause(f.name, f.binders.map(b => b.name), vars => call(target(f.name), mapped(name(v.evidence), f, vars)))),
    ...lawShapes.map(f => clause(f.name, f.binders.map(b => b.name), (vars, i) => ({kind: "pathApply", operator: "@",
      left: call(target(f.name), mapped(name(v.evidence), f, vars)), right: name(i), ...at}), "i")),
  ];
  const foldMap = definition("fold_map", [[v.target, again.theory],
    [v.evidence, call(evidence.type.fn, [universe, target(carrier)])], ...generator, [v.x, self]], target(carrier),
    {kind: "match", value: name(v.x), motiveName: null, type: null, clauses, ...at});
  const fold = definition("fold", [[v.target, again.theory], ...generator], call(reference(record.homReference, `${T}.Hom`, at), [ownModel, name(v.target)]),
    call(reference(record.homMakeReference, `${T}.Hom.make`, at), [ownModel, name(v.target), named("map", lambda(v.x, recurse(target(evidence.name), name(v.x)))),
      ...operationShapes.map(f => named(`map_${f.name}`, lambdas(variables(f), call("refl", [call(target(f.name), mapped(target(evidence.name), f))]))))]));
  return [inductive, model, foldMap, fold];
}

// The strategy's refusal of a law whose path constructor the kernel refuses
// as a boundary (K102-K105, K133-K140), as one whose side is a match, or
// null for any other failure, which keeps the kernel's own message.
const BOUNDARY = /: A (?:constructor's boundary|boundary|binder(?:'s type)? in a boundary|path abstraction or application in a boundary)\b/;
export const lawRefusal = (d, failure) => {
  const law = d.generated?.laws?.[failure.constructor];
  return law && BOUNDARY.test(failure.message ?? "") ? notEquational(law) : null;
};

// Refusals describe this strategy's limits, not nonexistence of a model.
const notATheory = (kind, given) => Error(`${kind} takes a theory at its universes and parameters, as ${
  kind === "free" ? "free W(A : U0) : Monoid(U0) on A" : "initial N : Monoid(U0)"}; ${given} is none.`);
const theoryArguments = (T, wanted, given) => Error(`${T} takes ${wanted} argument${wanted === 1 ? "" : "s"}, its universes and parameters; this gives ${given}.`);
const notOneCarrier = (T, carriers) => Error(`The equational strategy supports one carrier that is not a family; ${T} has ${
  carriers.length ? carriers.map(f => f.family ? `the family ${f.name}` : f.name).join(", ") : "none"}.`);
const untruncatedCarrier = (T, carrier) => Error(`${T}'s carrier ${carrier} is neither a set nor a proposition: the equational strategy requires a truncated carrier.`);
const notPositive = (field, binder, carrier) => Error(`${field} takes ${binder} with a type depending on the carrier ${carrier}: the equational strategy supports carrier arguments or types independent of the carrier.`);
const onProof = (field, binder, kind, proof) => Error(`${field} takes ${binder} with a type depending on the ${kind} ${proof}: the equational strategy supports arguments independent of the theory's laws and carrier evidence.`);
const notCarrierValued = (field, carrier) => Error(`${field} does not return the carrier ${carrier}: the equational strategy supports carrier-valued operations.`);
const notEquational = field => Error(`The law ${field} is not an equation between operation terms: the equational strategy does not support this law.`);
const arrowOperation = field => Error(`${field} uses an arrow type: the equational strategy requires named operation arguments, as in succ(x : M) : M.`);
const recursiveGenerators = N => Error(`The generator type of ${N} mentions ${N} or one of its generated names: free requires a type given independently of the declared model.`);
const capturedModel = (T, field, N) => Error(`${T}'s ${field} binds ${N} in a pattern, under which the expansion names the model ${N}: rename the initial or free model.`);
const universeArguments = field => Error(`${field} binds a universe argument: the equational strategy supports term arguments only; bind universes in the theory header.`);
const hiddenDependency = N => Error(`${N} hides a declaration used by its expansion: rename the initial or free model.`);
