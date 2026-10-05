// Theories (L2.4, docs/roadmaps/core-theories.md). The translator expands a
// theory declaration into ordinary declarations, which it then checks like a
// user's own, so each is inspectable by name:
//
//   T(U < UU0) : next(U)         the type of models: a Σ of the fields, in order;
//   T.make{{U < UU0}}(f1, …)     its constructor, one parameter per field;
//   T.f{{U < UU0}}(m)            for each field f, its projection, typed
//                                through the earlier projections;
//   T.p{{U < UU0}}(m)            for each parent P labelled p, m's P-model.
//
// `theory T(U < UU0)` names the universe of the carriers (L2.4c). A carrier
// `M : set U` is a type in it followed by the field M_is_set : IsSet(U, M);
// `P : prop U`, by P_is_prop : IsProp(U, P); and `M : U` is the type alone,
// whose equations are no propositions. `sort M : set;` and `sort P : prop;`
// are the earlier spelling of the first two.
// An operation `mul(x, y : M) : M` is a field of type forall x, y : M. M, a
// constant `one : M` one of type M, and a law `law l(x : M) : S` one of type
// forall x : M. S. Inside the theory, a notation means its operation: with
// `mul(x, y : M) : M notation x * y`, x * y is mul(x, y).
//
// `extends` takes each parent's fields, renamed as it says, before the
// theory's own. A field two parents give is one field when it comes from one
// ancestor's field, with one name and one type; otherwise it is refused.

import { parse } from "./parser.mjs";
import { morphismSource } from "./morphisms.mjs";

// The universes of a theory's carriers, in the fields a theory records, the
// first, UNIVERSE, and the k-th: each expansion names them afresh.
const UNIVERSE = "\u0000universe";
export const universeAt = k => k === 0 ? UNIVERSE : `${UNIVERSE}${k}`;

// An error at a node of the theory's text.
const located = (error, node) => Object.assign(error, { offset: node.start });

// Nodes of the source syntax, placed at `at`, the theory text they come from.
const place = at => ({ start: at.start, end: at.end });
const token = (text, at) => ({ text, ...place(at) });
const name = (text, at) => ({ kind: "name", name: text, ...place(at) });
const call = (fn, args, at) => ({ kind: "call", fn: typeof fn === "string" ? name(fn, at) : fn, args, ...place(at) });
const quantifier = (kind, binder, domain, body, at) =>
  ({ kind, name: typeof binder === "string" ? token(binder, at) : binder, binderKind: kind, domain, body, ...place(at) });
const projection = (value, index, at) => ({ kind: "projection", value, index, ...place(at) });
const pair = (left, right, at) => ({ kind: "pair", left, right, ...place(at) });

// A copy of a syntax tree with `rewrite(node, bound)` applied to each node,
// outermost first; `bound` holds the names its binders bind there.
function rewritten(node, rewrite, bound = new Set()) {
  if (Array.isArray(node)) return node.map(item => rewritten(item, rewrite, bound));
  if (!node || typeof node !== "object" || !node.kind) return node;
  const replaced = rewrite(node, bound);
  if (replaced !== node) return replaced;
  const binders = node.kind === "binderGroup" ? node.names
    : ["forall", "exists", "lambda"].includes(node.kind) && node.name?.text ? [node.name] : [];
  const copy = {};
  for (const [key, value] of Object.entries(node)) {
    // A binder's own domain is outside its scope; its body is inside.
    const scope = binders.length && key === "body" ? new Set([...bound, ...binders.map(b => b.text)]) : bound;
    copy[key] = rewritten(value, rewrite, scope);
  }
  return copy;
}
// Every position in a tree set to `at`: inherited syntax comes from another
// theory's text, perhaps another module's.
const relocated = (node, at) => JSON.parse(JSON.stringify(node), (key, value) =>
  key === "start" ? at.start : key === "end" ? at.end : value);
// Free names replaced by others: `names` maps a name to its replacement's name.
const renamed = (node, names, at) => rewritten(node, (n, bound) => {
  if (n.kind !== "name" || !names.has(n.name) || bound.has(n.name)) return n;
  if (bound.has(names.get(n.name)))
    throw located(Error(`Renaming ${n.name} to ${names.get(n.name)} would capture a variable named ${names.get(n.name)}; pick another name.`), at);
  return { ...n, name: names.get(n.name) };
});

// Every name the syntax uses, bound or free, so that a generated name avoids
// all of them.
function namesIn(node, names = new Set()) {
  if (Array.isArray(node)) { for (const item of node) namesIn(item, names); return names; }
  if (!node || typeof node !== "object") return names;
  if (node.kind === "name") names.add(node.name);
  if (typeof node.text === "string") names.add(node.text);
  for (const value of Object.values(node)) if (value && typeof value === "object") namesIn(value, names);
  return names;
}
const fresh = (stem, taken) => { let candidate = stem, k = 1; while (taken.has(candidate)) candidate = `${stem}${k++}`; return candidate; };
// An unlabelled parent's label: its name in snake case, CommMonoid as comm_monoid.
const snake = text => text.replace(/([a-z0-9])([A-Z])/g, "$1_$2").toLowerCase();
const sameSyntax = (a, b) => JSON.stringify(a, (key, value) => ["start", "end"].includes(key) ? undefined : value)
  === JSON.stringify(b, (key, value) => ["start", "end"].includes(key) ? undefined : value);

// Why a law's statement is not evidently a proposition, or null when it is.
// Laws are propositions: homomorphisms ignore them (L2.4). Accepted are an
// equation between elements of a sort (every sort is a set or a
// proposition, so its equations are propositions), Void and Unit, an
// element of a proposition sort, and forall, -> into one, and `and` of two.
// `byName` holds the fields declared so far.
function notAProposition(statement, byName) {
  const sortNamed = (node, bound) =>
    node?.kind === "name" && !bound.has(node.name) && byName.get(node.name)?.kind === "sort" ? node.name : null;
  // The sort an operation or a constant returns: its type past the foralls.
  const returns = field => {
    if (field?.kind !== "operation") return null;
    let type = field.type;
    while (type.kind === "forall" || type.kind === "binderGroup") type = type.body;
    return sortNamed(type, new Map());
  };
  // The sort a term lies in, where the theory's own syntax says so; `bound`
  // maps a bound variable to its sort, or to null.
  const sortOf = (term, bound) =>
    term.kind === "name" ? (bound.has(term.name) ? bound.get(term.name) : returns(byName.get(term.name)))
      : term.kind === "call" && term.fn.kind === "name" && !bound.has(term.fn.name) ? returns(byName.get(term.fn.name))
        : null;
  const propositionSort = name => byName.get(name)?.kind === "sort"
    && [...byName.values()].some(field => field.kind === "evidence" && field.of === name && field.evidence === "IsProp");
  const check = (node, bound) => {
    if (node.kind === "forall" || node.kind === "binderGroup" && node.binderKind === "forall") {
      const sort = sortNamed(node.domain, bound), inner = new Map(bound);
      for (const binder of node.kind === "forall" ? [node.name] : node.names) inner.set(binder.text, sort);
      return check(node.body, inner);
    }
    if (node.kind === "binary" && node.operator === "->") return check(node.right, bound);
    if (node.kind === "binary" && node.operator === "and") return check(node.left, bound) ?? check(node.right, bound);
    if (node.kind === "binary" && node.operator === "=") {
      const sort = node.carrier ? sortNamed(node.carrier, bound) : sortOf(node.left, bound) ?? sortOf(node.right, bound);
      if (!sort) return { node, why: "the sides of an equation in it are not elements of one of the theory's sorts" };
      return [...byName.values()].some(field => field.kind === "evidence" && field.of === sort) ? null
        : { node, why: `${sort} has no h-level, so an equation between its elements is not a proposition` };
    }
    if (node.kind === "name" && !bound.has(node.name)
      && (["Void", "Unit"].includes(node.name) && !byName.has(node.name) || propositionSort(node.name))) return null;
    return { node, why: node.kind === "name" && byName.get(node.name)?.kind === "sort"
      ? `${node.name} is a sort, whose elements are data` : "its statement is none of these" };
  };
  return check(statement, new Map());
}

// A theory's fields, in order, with types over the earlier fields' names,
// its notations and its parents, as the theory records them (`lookup` gives
// a parent's record by name).
function theoryFields(theory, lookup) {
  const T = theory.name.text, fields = [], notations = new Map(), parents = [], byName = new Map();
  // The header's universes are the model's, which each expansion names
  // afresh; a theory without a header has one. Its parameters are every
  // model's, as the header writes them (L2.4c).
  const headerUniverses = (theory.universes ?? []).map(u => u.text);
  const universeCount = Math.max(1, headerUniverses.length);
  const universe = new Map(headerUniverses.map((u, k) => [u, universeAt(k)]));
  const inTheoryUniverse = (node, at) => universe.size ? renamed(node, universe, at) : node;
  const params = (theory.params ?? []).map(p => ({ name: p.name.text, type: inTheoryUniverse(p.type, p.name), at: p.name }));
  const header = [...(theory.universes ?? []), ...(theory.params ?? []).map(p => p.name)];
  header.forEach((binder, k) => {
    if (header.slice(0, k).some(other => other.text === binder.text))
      throw located(Error(`${T}'s header binds ${binder.text} twice: give each its own name.`), binder);
  });
  const add = (field, at, from = null) => {
    const existing = byName.get(field.name);
    if (existing) {
      // One ancestor's field, with one type, is one field of the child.
      if (from && existing.origin === field.origin && sameSyntax(existing.type, field.type)) return;
      throw located(Error(existing.from && from
        ? `${T} gets a field named ${field.name} from both ${existing.from} and ${from}: rename one, as in ${from}(${field.name} := …).`
        : `${T} has two fields named ${field.name}: give each its own name.`), at);
    }
    const entry = { ...field, at, ...(from ? { from } : {}) };
    byName.set(field.name, entry);
    fields.push(entry);
  };
  const notate = (operator, field, at) => {
    if (notations.has(operator) && notations.get(operator) !== field)
      throw located(Error(`${operator} would stand for both ${notations.get(operator)} and ${field} in ${T}: a notation means one operation; rename one's notation.`), at);
    notations.set(operator, field);
  };
  for (const parent of theory.parents ?? []) {
    const record = lookup(parent.name.text);
    if (!record) throw located(Error(`${parent.name.text} is not a theory here: ${T} extends theories in scope.`), parent.name);
    const label = parent.label?.text ?? snake(record.name);
    if (parents.some(other => other.label === label))
      throw located(Error(`${T} has two parents labelled ${label}: label one, as in other : ${parent.name.text}.`), parent.label ?? parent.name);
    // The parent's universes are the child's: its one universe the child's
    // one, or each by its name. Its parameters are the child's of the same
    // names and types.
    const universes = new Map(), parentCount = Math.max(1, record.universes.length);
    if (parentCount === 1 && universeCount === 1) universes.set(UNIVERSE, UNIVERSE);
    else record.universes.forEach((u, k) => {
      const own = headerUniverses.indexOf(u);
      if (own < 0) throw located(Error(`${T} extends ${record.name}, whose header binds the universe ${u}: bind ${u} in ${T}'s header too.`), parent.name);
      universes.set(universeAt(k), universeAt(own));
    });
    for (const p of record.params) {
      const own = params.find(q => q.name === p.name);
      if (!own || !sameSyntax(own.type, renamed(p.type, universes, parent.name)))
        throw located(Error(`${T} extends ${record.name}, whose header has the parameter ${p.name}: give ${T} the parameter ${p.name} with the same type.`), parent.name);
    }
    // Each renaming names a field of the parent, once.
    const names = new Map(universes), renotated = new Map();
    for (const { from, to, notation } of parent.renaming) {
      const field = record.fields.find(f => f.name === from.text);
      if (!field) throw located(Error(`${record.name} has no field ${from.text}; its fields are ${record.fields.map(f => f.name).join(", ")}.`), from);
      if (names.has(from.text)) throw located(Error(`${from.text} is renamed twice.`), from);
      names.set(from.text, to.text);
      if (notation) {
        if (field.kind !== "operation" || field.arity !== 2)
          throw located(Error(`A notation names an operation's two arguments; ${from.text} is not an operation of two.`), notation);
        renotated.set(to.text, notation.operator);
      }
    }
    // A sort's evidence follows the sort's name.
    for (const field of record.fields)
      if (field.kind === "evidence" && names.has(field.of) && !names.has(field.name))
        names.set(field.name, `${names.get(field.of)}_is_${field.evidence === "IsSet" ? "set" : "prop"}`);
    const at = { start: parent.start, end: parent.end };
    // Evidence names its sort by the sort's new name, so a later renaming
    // of that sort renames the evidence too.
    for (const field of record.fields)
      add({ ...field, name: names.get(field.name) ?? field.name, type: relocated(renamed(field.type, names, at), at),
        ...(field.kind === "evidence" ? { of: names.get(field.of) ?? field.of } : {}) },
        at, parent.name.text);
    for (const [operator, field] of Object.entries(record.notations)) {
      const child = names.get(field) ?? field;
      if (!renotated.has(child)) notate(operator, child, at);
    }
    for (const [field, operator] of renotated) notate(operator, field, at);
    parents.push({ label, theory: record.name, model: record.model, make: record.make, projection: `${T}.${label}`,
      universes: Array.from({ length: parentCount }, (_, k) => universes.get(universeAt(k))), params: record.params.map(p => p.name),
      fields: record.fields.map(field => names.get(field.name) ?? field.name), kinds: record.fields.map(field => field.kind) });
  }
  for (const item of theory.fields) {
    const origin = `${T}.${item.name.text}`;
    if (item.kind === "sort") {
      const own = universeAt(Math.max(0, headerUniverses.indexOf(item.universe?.text)));
      add({ name: item.name.text, kind: "sort", type: name(own, item.name), origin }, item.name);
      if (!item.level) continue;
      const evidence = item.level === "set" ? "IsSet" : "IsProp";
      add({ name: `${item.name.text}_is_${item.level}`, kind: "evidence", evidence, of: item.name.text,
        type: call(evidence, [name(own, item.name), name(item.name.text, item.name)], item.name),
        origin: `${origin}_is_${item.level}` }, item.name);
      continue;
    }
    if (item.notation) {
      const { operator, left, right } = item.notation;
      if (item.kind !== "operation" || item.params.length !== 2)
        throw located(Error(`A notation names an operation's two arguments, as in mul(x, y : M) : M notation x * y; ${item.name.text} has ${["none", "one"][item.params.length] ?? item.params.length}.`), item.notation);
      if (left.text !== item.params[0].name.text || right.text !== item.params[1].name.text)
        throw located(Error(`The notation of ${item.name.text} writes its arguments in order: ${item.params[0].name.text} ${operator} ${item.params[1].name.text}.`), item.notation);
      notate(operator, item.name.text, item.notation);
    }
    // forall over the parameters, innermost last.
    let type = item.type;
    for (let j = item.params.length - 1; j >= 0; j--)
      type = quantifier("forall", item.params[j].name, item.params[j].type, type, item);
    type = inTheoryUniverse(type, item);
    // Inside the theory, a notation means its operation.
    const operatorsAsCalls = node => rewritten(node, (n, bound) =>
      n.kind === "binary" && notations.has(n.operator) && !bound.has(notations.get(n.operator))
        ? call(notations.get(n.operator), [operatorsAsCalls(n.left), operatorsAsCalls(n.right)], n)
        : n);
    type = operatorsAsCalls(type);
    if (item.kind === "law") {
      const data = notAProposition(type, byName);
      if (data)
        throw located(Error(`The law ${item.name.text} must state a proposition: an equation between elements of a sort, Void, or forall, -> or and over those; ${data.why}. A law holds no data, and homomorphisms ignore laws: declare data as an operation or a constant.`), data.node);
    }
    add({ name: item.name.text, kind: item.kind, arity: item.params.length, type, origin }, item.name);
  }
  for (const field of fields) {
    if (field.name.includes(".")) throw located(Error(`A field's name is a plain name; ${field.name} is not.`), field.at);
    if (header.some(binder => binder.text === field.name))
      throw located(Error(`${T}'s header binds ${field.name}, which names a field too: give each its own name.`), field.at);
  }
  return { fields, notations, parents, universes: headerUniverses, params: params.map(({ at: _, ...p }) => p) };
}

// The declarations a theory expands to, and its record, which a theory
// that extends it reads (`lookup` gives the record of a theory by name).
export function expandTheory(theory, lookup = () => null) {
  const T = theory.name.text, at = theory.name;
  const { fields, notations, parents, universes: headerUniverses, params } = theoryFields(theory, lookup);
  if (!fields.length) throw located(Error(`${T} has no fields: a theory declares sorts, operations and laws.`), at);
  const taken = new Set([...namesIn(theory), ...fields.map(field => field.name), ...fields.flatMap(field => [...namesIn(field.type)])]);
  // The header's names for the universes, or fresh ones without a header.
  const universes = headerUniverses.length ? headerUniverses : [fresh("U", taken)], model = fresh("m", taken);
  const inUniverse = node => renamed(node, new Map(universes.map((u, k) => [universeAt(k), u])), at);
  // The header's binders, the universes in one group and then each
  // parameter; `implicit` says which are implicit.
  const headerParameters = ({ universe = false, parameter = false } = {}) => [
    ...universes.map(u => ({ name: token(u, at), bound: name("UU0", at), group: 0, ...(universe ? { implicit: true } : {}) })),
    ...params.map((p, k) => ({ name: token(p.name, at), type: inUniverse(p.type), group: k + 1, ...(parameter ? { implicit: true } : {}) })),
  ];
  const nextGroup = params.length + 1;
  const modelType = span => call(T, [...universes, ...params.map(p => p.name)].map(text => name(text, span)), span);
  const largest = list => list.length === 1 ? name(list[0], at) : call("max", [name(list[0], at), largest(list.slice(1))], at);
  const declaration = (declName, declParams, type, value, span, generated, extra = {}) => ({
    kind: "def", name: token(declName, span), params: declParams, type,
    ...(declParams.some(p => p.implicit) ? { implicitParameters: place(span) } : {}),
    body: [{ kind: "exact", value, ...place(span) }], typedValue: true, ...place(span),
    generated: { theory: T, ...generated }, ...extra,
  });
  const record = {
    name: T, model: T, make: `${T}.make`, universes: headerUniverses, params,
    fields: fields.map(({ at: _, from: __, ...field }) => ({ ...field, projection: `${T}.${field.name}` })),
    notations: Object.fromEntries(notations), parents,
  };
  // The sorts' evidence comes from hlevels.
  const requires = [...new Set(fields.filter(field => field.evidence).map(field => field.evidence))];
  const out = [];
  // T(U < UU0, params) : next(U) := exists f1 : A1. … An;
  let modelBody = inUniverse(fields.at(-1).type);
  for (let k = fields.length - 2; k >= 0; k--)
    modelBody = quantifier("exists", token(fields[k].name, fields[k].at), inUniverse(fields[k].type), modelBody, fields[k].at);
  out.push(declaration(T, headerParameters(), call("next", [largest(universes)], at), modelBody, at,
    { role: "model" }, { theory: record, requires }));
  // T.make{{U < UU0}}(params, f1 : A1, …) : T(U, params) := (f1, …, fn);
  let tuple = name(fields.at(-1).name, fields.at(-1).at);
  for (let k = fields.length - 2; k >= 0; k--) tuple = pair(name(fields[k].name, fields[k].at), tuple, at);
  out.push(declaration(`${T}.make`, [...headerParameters({ universe: true }),
    ...fields.map((field, k) => ({ name: token(field.name, field.at), type: inUniverse(field.type), group: nextGroup + k }))],
  modelType(at), tuple, at, { role: "make" }, { requires }));
  // T.f{{U < UU0, params}}(m : T(U, params)) : A[earlier fields := their projections] := m.2…2.1;
  const projected = new Map();
  fields.forEach((field, k) => {
    const type = rewritten(inUniverse(field.type), (n, bound) => n.kind === "name" && projected.has(n.name) && !bound.has(n.name)
      ? call(projected.get(n.name), [name(model, n)], n) : n);
    let value = name(model, field.at);
    for (let j = 0; j < k; j++) value = projection(value, 2, field.at);
    if (k < fields.length - 1) value = projection(value, 1, field.at);
    out.push(declaration(`${T}.${field.name}`, [...headerParameters({ universe: true, parameter: true }),
      { name: token(model, field.at), type: modelType(field.at), group: nextGroup }], type, value, field.at,
    { role: "projection", field: field.name }));
    projected.set(field.name, `${T}.${field.name}`);
  });
  // T.p{{U < UU0, params}}(m : T(U, params)) : P(U, params) := P.make(params, T.f(m), …),
  // each of P's fields from the child's field it became.
  for (const [index, parent] of parents.entries()) {
    const span = theory.parents[index];
    const parentModel = call(parent.theory, [...parent.universes.map(u => inUniverse(name(u, span))), ...parent.params.map(p => name(p, span))], span);
    out.push(declaration(parent.projection, [...headerParameters({ universe: true, parameter: true }),
      { name: token(model, span), type: modelType(span), group: nextGroup }], parentModel,
    call(parent.make, [...parent.params.map(p => name(p, span)), ...parent.fields.map(field => call(`${T}.${field}`, [name(model, span)], span))], span), span,
    { role: "projection", field: parent.label }));
  }
  // Homomorphisms and isomorphisms, when every operation takes and returns
  // sorts (morphisms.mjs): their source, parsed and placed at the theory's
  // name. A generated definition's name is dotted, which a def cannot
  // spell, so each is parsed under a placeholder and then renamed.
  const morphisms = morphismSource(record, other => Boolean(lookup(other)));
  if (morphisms.missing) record.noMorphisms = morphisms.missing;
  else {
    // A parameter's type is written in place of its marker, in the
    // homomorphism's universes.
    const parameterType = new Map(params.map((p, k) => [morphisms.parameterMarker(k),
      renamed(p.type, new Map(morphisms.universes.map((u, j) => [universeAt(j), u])), at)]));
    const parsed = parse(morphisms.declarations.map((d, k) => d.source.replace(/^def \S+?(?=[{(:])/, `def generated_${k}`)).join("\n")).declarations
      .map(d => JSON.parse(JSON.stringify(d), (key, value) =>
        value?.kind === "name" && parameterType.has(value.name) ? parameterType.get(value.name) : value));
    parsed.forEach((d, k) => {
      const { name: declName, role, field, record: morphismRecord } = morphisms.declarations[k];
      out.push({ ...relocated(d, at), name: token(declName, at),
        generated: { theory: T, role, ...(field ? { field } : {}) }, ...(morphismRecord ? { theory: morphismRecord } : {}) });
    });
  }
  return out;
}
