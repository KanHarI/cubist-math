// L2.6's retained construction-and-fold prototype. This does not register
// an initial/free capability: deriving and the universal proofs are pending.
// The expansion is ordinary syntax, checked with no new kernel rule.
import {theoryBinding, selected} from "./theories.mjs";
import {universeAt} from "../cubist/theories.mjs";
import {freeNames, substituted, renamedFree, allNames, relocated} from "../cubist/scopes.mjs";
import {assignArguments} from "./arguments.mjs";
import {Scope} from "./elaboration.mjs";
import {repeatedName} from "./names.mjs";

// The declarations an initial or free model expands to, checked in its
// place; one that does not expand fails as a declaration of its name.
export function initialDeclarations(t, module, d, env, declarations) {
  const unit = module.declaration(t.declarationFuel).with({references: null});
  try { return expand(t, unit, d, env); }
  catch (failure) {
    const error = unit.locate(failure, d.name);
    t.onDeclarationStart?.(d);
    declarations.push({ name: d.name.text, status: "not-translated", reason: error.message, errorStart: error.offset, errorEnd: error.sourceEnd,
      blockedBy: error.blockedBy });
    env.set(d.name.text, { tag: "Untranslated", name: d.name.text, binding: t.checker.bindingName?.(d.name.text) ?? d.name.text, reason: error.message });
    t.onDeclaration?.(d, declarations.at(-1));
    return [];
  } finally { unit.fuel.close(); }
}

function expand(t, module, d, env) {
  const N = d.name.text, at = {start: d.name.start, end: d.name.end}, free = d.kind === "free";
  const token = text => ({text, ...at});
  const name = text => ({kind: "name", name: text, ...at});
  const call = (fn, args) => args.length ? {kind: "call", fn: typeof fn === "string" ? name(fn) : fn, args, ...at}
    : typeof fn === "string" ? name(fn) : fn;
  const named = (label, value) => ({kind: "namedArgument", name: token(label), value, ...at});
  const lambda = (binder, body) => ({kind: "lambda", name: token(binder), body, ...at});
  const lambdas = (binders, body) => binders.reduceRight((inner, b) => lambda(b, inner), body);
  const head = d.theory.kind === "call" ? d.theory.fn : d.theory;
  const entry = head.kind === "name" ? env.get(theoryBinding(head.name)) : null;
  if (entry?.tag !== "Theory") {
    // A theory that failed its own check is a dependency here, as at its other uses.
    const failed = head.kind === "name" ? env.get(head.name) : null;
    if (failed?.tag === "Untranslated")
      throw module.locate(Object.assign(Error(`Untranslated dependency: ${head.name}`), {blockedBy: failed.binding ?? failed.name}), head);
    throw module.locate(notATheory(d.kind, module.source.slice(d.theory.start, d.theory.end).trim()), d.theory);
  }
  const record = entry.record, T = record.name;
  const repeated = repeatedName(d.params);
  if (repeated) throw module.locate(Error(`${N} has two parameters named ${repeated.name.text}: give each its own name.`), repeated.name);

  // Names from a theory's fields retain their meaning under the free
  // declaration's parameters. Rename colliding parameters, keeping their
  // public labels; later parameter groups and user expressions follow them.
  const globals = new Set([N, T, "IsSet", "IsProp", "refl", ...record.fields.flatMap(f => [...freeNames(f.type)])]);
  const taken = new Set([...allNames(d), ...record.fields.flatMap(f => [...allNames(f.type)]), ...globals]);
  const fresh = stem => { let n = stem, k = 1; while (taken.has(n)) n = `${stem}${k++}`; taken.add(n); return n; };
  const put = (node, map) => substituted(node, map, n => module.locate(capturedBy(N, n), d.theory));
  const renaming = new Map(), params = [];
  const apart = node => renamedFree(node, n => renaming.get(n));
  for (let k = 0; k < d.params.length;) {
    const group = d.params[k].group, members = [];
    while (k < d.params.length && d.params[k].group === group) members.push(d.params[k++]);
    const changes = members.map(p => [p.name.text, globals.has(p.name.text) ? fresh(p.name.text) : p.name.text]);
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
  const scope = (d.uses ?? []).reduce((inner, model) => selected(t, inner, model), new Scope(module, new Map(), env));
  scope.infer(t.term(checked, scope));
  const given = new Map([...record.universes.map((_, k) => [universeAt(k), argument(k)]),
    ...record.params.map((p, k) => [p.name, argument(record.universes.length + k)])]);

  const carriers = record.fields.filter(f => f.kind === "sort");
  if (carriers.length !== 1 || carriers[0].family) throw module.locate(notOneCarrier(T, carriers), d.theory);
  const carrier = carriers[0].name;
  const evidence = record.fields.find(f => f.kind === "evidence" && f.of === carrier);
  if (!evidence) throw module.locate(untruncatedCarrier(T, carrier), d.theory);
  const level = evidence.evidence === "IsSet" ? "set" : "prop";
  const universe = relocated(put(carriers[0].type, given), at);
  const names = params.map(p => p.name.text), self = call(N, names.map(name));
  const operations = record.fields.filter(f => f.kind === "operation").map(f => f.name);
  const proofs = new Set(record.fields.filter(f => f.kind === "law" || f.kind === "evidence").map(f => f.name));
  const constructor = field => `${N}.${field}`;
  const inside = new Map([...given, [carrier, self], ...operations.map(op => [op, name(constructor(op))])]);

  // A domain must be the carrier or independent of it, including the
  // earlier carrier-typed variables and carrier-valued operations. Shared
  // domains are read before any of their group's names binds.
  const shape = field => {
    const binders = [], bound = new Set(), dependent = new Set([carrier, ...operations, ...proofs]);
    let body = field.type, placed = relocated(put(field.type, inside), at), dependentBinder = null;
    for (let group = 0; body?.kind === "forall" || body?.kind === "binderGroup" && body.binderKind === "forall";
        body = body.body, placed = placed.body, group++) {
      const names = body.kind === "forall" ? [body.name] : body.names;
      const placedNames = placed.kind === "forall" ? [placed.name] : placed.names;
      if (body.bound) throw module.locate(universeArguments(field.name), d.theory);
      const domain = body.domain, isCarrier = domain.kind === "name" && domain.name === carrier && !bound.has(carrier);
      if (!isCarrier && [...freeNames(domain)].some(n => dependent.has(n)))
        dependentBinder ??= names[0].text;
      for (const n of placedNames) binders.push({name: n.text, carrier: isCarrier, type: placed.domain, group});
      for (const n of names) { bound.add(n.text); if (isCarrier) dependent.add(n.text); else dependent.delete(n.text); }
    }
    return {binders, body, bound, placed, dependentBinder};
  };

  const constructors = [], operationShapes = [], lawShapes = [];
  for (const field of record.fields) {
    if (field.kind === "sort" || field.kind === "evidence") continue;
    const {binders, body, bound, placed, dependentBinder} = shape(field);
    if (field.kind === "law" && (!(body.kind === "binary" && body.operator === "=")
        || [...freeNames(body, bound)].some(n => proofs.has(n))))
      throw module.locate(notEquational(field.name), d.theory);
    if (dependentBinder) throw module.locate(notPositive(field.name, dependentBinder, carrier), d.theory);
    const params = binders.map(b => ({name: token(b.name), type: b.type, group: b.group}));
    if (field.kind === "operation") {
      if (body.kind === "binary" && body.operator === "->") throw module.locate(arrowOperation(field.name), d.theory);
      if (!(body.kind === "name" && body.name === carrier && !bound.has(carrier))) throw module.locate(notCarrierValued(field.name, carrier), d.theory);
      operationShapes.push({name: field.name, binders});
      constructors.push({kind: "constructor", name: token(constructor(field.name)), params, type: null, ...at});
    } else {
      lawShapes.push({name: field.name, binders});
      constructors.push({kind: "constructor", name: token(constructor(field.name)), params, type: placed, ...at});
    }
  }
  for (const f of [...operationShapes, ...lawShapes]) for (const b of f.binders) taken.add(b.name);
  const v = Object.fromEntries(["target", "evidence", "g", "x", "i", "a"].map(stem => [stem, fresh(stem)]));
  const xs = Array.from({length: Math.max(0, ...[...operationShapes, ...lawShapes].map(f => f.binders.length))}, (_, k) => fresh(`x${k}`));
  if (free) constructors.unshift({kind: "constructor", name: token(constructor("gen")),
    params: [{name: token(v.a), type: on, group: 0}], type: null, ...at});
  const generated = {initial: N}, uses = d.uses ? {uses: d.uses} : {};
  const inductive = {kind: "inductive", name: d.name, params, result: {modifier: {kind: level, ...at}, universe},
    constructors, start: d.start, end: d.end, generated, ...uses};

  const ownModel = call(constructor("model"), names.map(name));
  const variables = f => xs.slice(0, f.binders.length);
  const target = field => name(`${v.target}.${field}`);
  const generator = free ? [[v.g, {kind: "binary", operator: "->", left: on, right: target(carrier), ...at}]] : [];
  const recurse = (proof, x) => call(constructor("fold_map"), [...names.map(name), name(v.target), proof, ...(free ? [name(v.g)] : []), x]);
  const mapped = (proof, f) => f.binders.map((b, k) => b.carrier ? recurse(proof, name(xs[k])) : name(xs[k]));
  const definition = (suffix, extra, type, value) => ({kind: "def", name: token(constructor(suffix)),
    params: [...params, ...extra.map(([n, type], k) => ({name: token(n), type, group: d.params.length + k}))],
    type, body: [{kind: "exact", value, ...at}], typedValue: true, ...at, generated, ...uses});
  const model = definition("model", [], theory, call(`${T}.make`, [named(carrier, self), named(evidence.name, name("_")),
    ...[...operationShapes, ...lawShapes].map(f => named(f.name, lambdas(variables(f), call(constructor(f.name), variables(f).map(name)))))]));
  const clause = (field, args, body, coordinates = []) => ({kind: "clause", constructor: token(constructor(field)),
    args: args.map(token), binders: [], coordinates: coordinates.map(token), body, ...at});
  const clauses = [
    ...(free ? [clause("gen", [v.a], call(v.g, [name(v.a)]))] : []),
    ...operationShapes.map(f => clause(f.name, variables(f), call(target(f.name), mapped(name(v.evidence), f)))),
    ...lawShapes.map(f => clause(f.name, variables(f), {kind: "pathApply", operator: "@",
      left: call(target(f.name), mapped(name(v.evidence), f)), right: name(v.i), ...at}, [v.i])),
  ];
  const foldMap = definition("fold_map", [[v.target, theory],
    [v.evidence, call(evidence.evidence, [universe, target(carrier)])], ...generator, [v.x, self]], target(carrier),
    {kind: "match", value: name(v.x), motiveName: null, type: null, clauses, ...at});
  const fold = definition("fold", [[v.target, theory], ...generator], call(`${T}.Hom`, [ownModel, name(v.target)]),
    call(`${T}.Hom.make`, [ownModel, name(v.target), named("map", lambda(v.x, recurse(target(evidence.name), name(v.x)))),
      ...operationShapes.map(f => named(`map_${f.name}`, lambdas(variables(f), call("refl", [call(target(f.name), mapped(target(evidence.name), f))]))))]));
  return [inductive, model, foldMap, fold];
}

// Refusals describe this strategy's limits, not nonexistence of a model.
const notATheory = (kind, given) => Error(`${kind} takes a theory at its universes and parameters, as ${
  kind === "free" ? "free W(A : U0) : Monoid(U0) on A" : "initial N : Monoid(U0)"}; ${given} is none.`);
const theoryArguments = (T, wanted, given) => Error(`${T} takes ${wanted} argument${wanted === 1 ? "" : "s"}, its universes and parameters; this gives ${given}.`);
const notOneCarrier = (T, carriers) => Error(`The equational strategy supports one carrier that is not a family; ${T} has ${
  carriers.length ? carriers.map(f => f.family ? `the family ${f.name}` : f.name).join(", ") : "none"}.`);
const untruncatedCarrier = (T, carrier) => Error(`${T}'s carrier ${carrier} is neither a set nor a proposition: the equational strategy requires a truncated carrier.`);
const notPositive = (field, binder, carrier) => Error(`${field} takes ${binder} with a type depending on the carrier ${carrier}: the equational strategy supports carrier arguments or types independent of the carrier.`);
const notCarrierValued = (field, carrier) => Error(`${field} does not return the carrier ${carrier}: the equational strategy supports carrier-valued operations.`);
const notEquational = field => Error(`The law ${field} is not an equation between operation terms: the equational strategy does not support this law.`);
const arrowOperation = field => Error(`${field} uses an arrow type: the equational strategy requires named operation arguments, as in succ(x : M) : M.`);
const recursiveGenerators = N => Error(`The generator type of ${N} mentions ${N} or one of its generated names: free requires a type given independently of the declared model.`);
const capturedBy = (field, name) => Error(`${field}'s pattern binds ${name}, which an argument here names: rename it in ${field}.`);
const universeArguments = field => Error(`${field} binds a universe argument: the equational strategy supports term arguments only; bind universes in the theory header.`);
const hiddenDependency = N => Error(`${N} hides a declaration used by its expansion: choose another name for the initial or free model.`);
