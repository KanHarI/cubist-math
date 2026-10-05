// Theories (L2.4, docs/roadmaps/core-theories.md). The translator expands a
// theory declaration into ordinary declarations, which it then checks like a
// user's own, so each is inspectable by name:
//
//   T.Model(U < UU0) : next(U)   the type of models: a Σ of the fields, in order;
//   T.make{{U < UU0}}(f1, …)     its constructor, one parameter per field;
//   T.f{{U < UU0}}(m)            for each field f, its projection, typed
//                                through the earlier projections;
//   T.p{{U < UU0}}(m)            for each parent P labelled p, m's P-model.
//
// A sort `M : set` is a type in the model's universe followed by the field
// M_is_set : IsSet(U, M); a sort `P : prop`, by P_is_prop : IsProp(U, P).
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

// The universe of a theory's sorts, in the fields a theory records: each
// expansion names it afresh.
const UNIVERSE = "\u0000universe";

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

// A theory's fields, in order, with types over the earlier fields' names,
// its notations and its parents, as the theory records them (`lookup` gives
// a parent's record by name).
function theoryFields(theory, lookup) {
  const T = theory.name.text, fields = [], notations = new Map(), parents = [], byName = new Map();
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
    // Each renaming names a field of the parent, once.
    const names = new Map(), renotated = new Map();
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
    for (const field of record.fields)
      add({ ...field, name: names.get(field.name) ?? field.name, type: relocated(renamed(field.type, names, at), at) },
        at, parent.name.text);
    for (const [operator, field] of Object.entries(record.notations)) {
      const child = names.get(field) ?? field;
      if (!renotated.has(child)) notate(operator, child, at);
    }
    for (const [field, operator] of renotated) notate(operator, field, at);
    parents.push({ label, theory: record.name, model: record.model, make: record.make, projection: `${T}.${label}`,
      fields: record.fields.map(field => names.get(field.name) ?? field.name), kinds: record.fields.map(field => field.kind) });
  }
  for (const item of theory.fields) {
    const origin = `${T}.${item.name.text}`;
    if (item.kind === "sort") {
      add({ name: item.name.text, kind: "sort", type: name(UNIVERSE, item.name), origin }, item.name);
      const evidence = item.level === "set" ? "IsSet" : "IsProp";
      add({ name: `${item.name.text}_is_${item.level}`, kind: "evidence", evidence, of: item.name.text,
        type: call(evidence, [name(UNIVERSE, item.name), name(item.name.text, item.name)], item.name),
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
    // Inside the theory, a notation means its operation.
    const operatorsAsCalls = node => rewritten(node, (n, bound) =>
      n.kind === "binary" && notations.has(n.operator) && !bound.has(notations.get(n.operator))
        ? call(notations.get(n.operator), [operatorsAsCalls(n.left), operatorsAsCalls(n.right)], n)
        : n);
    add({ name: item.name.text, kind: item.kind, arity: item.params.length, type: operatorsAsCalls(type), origin }, item.name);
  }
  for (const field of fields)
    if (field.name.includes(".")) throw located(Error(`A field's name is a plain name; ${field.name} is not.`), field.at);
  return { fields, notations, parents };
}

// The declarations a theory expands to, and its record, which a theory
// that extends it reads (`lookup` gives the record of a theory by name).
export function expandTheory(theory, lookup = () => null) {
  const T = theory.name.text, at = theory.name;
  const { fields, notations, parents } = theoryFields(theory, lookup);
  if (!fields.length) throw located(Error(`${T} has no fields: a theory declares sorts, operations and laws.`), at);
  const taken = new Set([...namesIn(theory), ...fields.map(field => field.name), ...fields.flatMap(field => [...namesIn(field.type)])]);
  const universe = fresh("U", taken), model = fresh("m", taken);
  const inUniverse = node => renamed(node, new Map([[UNIVERSE, universe]]), at);
  const universeParameter = implicit => ({ name: token(universe, at), bound: name("UU0", at), group: 0, ...(implicit ? { implicit } : {}) });
  const modelType = (theoryName, span) => call(`${theoryName}.Model`, [name(universe, span)], span);
  const declaration = (declName, params, type, value, span, generated, extra = {}) => ({
    kind: "def", name: token(declName, span), params, type,
    ...(params.some(p => p.implicit) ? { implicitParameters: place(span) } : {}),
    body: [{ kind: "exact", value, ...place(span) }], typedValue: true, ...place(span),
    generated: { theory: T, ...generated }, ...extra,
  });
  const record = {
    name: T, model: `${T}.Model`, make: `${T}.make`,
    fields: fields.map(({ at: _, from: __, ...field }) => ({ ...field, projection: `${T}.${field.name}` })),
    notations: Object.fromEntries(notations), parents,
  };
  // The sorts' evidence comes from hlevels.
  const requires = [...new Set(fields.filter(field => field.evidence).map(field => field.evidence))];
  const out = [];
  // T.Model(U < UU0) : next(U) := exists f1 : A1. … An;
  let modelBody = inUniverse(fields.at(-1).type);
  for (let k = fields.length - 2; k >= 0; k--)
    modelBody = quantifier("exists", token(fields[k].name, fields[k].at), inUniverse(fields[k].type), modelBody, fields[k].at);
  out.push(declaration(`${T}.Model`, [universeParameter(false)], call("next", [name(universe, at)], at), modelBody, at,
    { role: "model" }, { theory: record, requires }));
  // T.make{{U < UU0}}(f1 : A1, …) : T.Model(U) := (f1, …, fn);
  let tuple = name(fields.at(-1).name, fields.at(-1).at);
  for (let k = fields.length - 2; k >= 0; k--) tuple = pair(name(fields[k].name, fields[k].at), tuple, at);
  out.push(declaration(`${T}.make`, [universeParameter(true),
    ...fields.map((field, k) => ({ name: token(field.name, field.at), type: inUniverse(field.type), group: k + 1 }))],
  modelType(T, at), tuple, at, { role: "make" }, { requires }));
  // T.f{{U < UU0}}(m : T.Model(U)) : A[earlier fields := their projections] := m.2…2.1;
  const projected = new Map();
  fields.forEach((field, k) => {
    const type = rewritten(inUniverse(field.type), (n, bound) => n.kind === "name" && projected.has(n.name) && !bound.has(n.name)
      ? call(projected.get(n.name), [name(model, n)], n) : n);
    let value = name(model, field.at);
    for (let j = 0; j < k; j++) value = projection(value, 2, field.at);
    if (k < fields.length - 1) value = projection(value, 1, field.at);
    out.push(declaration(`${T}.${field.name}`, [universeParameter(true),
      { name: token(model, field.at), type: modelType(T, field.at), group: 1 }], type, value, field.at,
    { role: "projection", field: field.name }));
    projected.set(field.name, `${T}.${field.name}`);
  });
  // T.p{{U < UU0}}(m : T.Model(U)) : P.Model(U) := P.make(T.f(m), …), each
  // of P's fields from the child's field it became.
  for (const [index, parent] of parents.entries()) {
    const span = theory.parents[index];
    out.push(declaration(parent.projection, [universeParameter(true),
      { name: token(model, span), type: modelType(T, span), group: 1 }], modelType(parent.theory, span),
    call(parent.make, parent.fields.map(field => call(`${T}.${field}`, [name(model, span)], span)), span), span,
    { role: "projection", field: parent.label }));
  }
  // Homomorphisms and isomorphisms, when every operation takes and returns
  // sorts (morphisms.mjs): their source, parsed and placed at the theory's
  // name. A generated definition's name is dotted, which a def cannot
  // spell, so each is parsed under a placeholder and then renamed.
  const morphisms = morphismSource(record);
  if (morphisms.missing) record.noMorphisms = morphisms.missing;
  else {
    const parsed = parse(morphisms.declarations.map((d, k) => d.source.replace(/^def \S+?(?=[{(:])/, `def generated_${k}`)).join("\n")).declarations;
    parsed.forEach((d, k) => {
      const { name: declName, role, field, record: morphismRecord } = morphisms.declarations[k];
      out.push({ ...relocated(d, at), name: token(declName, at),
        generated: { theory: T, role, ...(field ? { field } : {}) }, ...(morphismRecord ? { theory: morphismRecord } : {}) });
    });
  }
  return out;
}
