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
// element of a proposition sort, a declared type whose header says it is a
// proposition, as Trunc(U, A) (L2.10k), and forall, -> into one, and `and`
// of two. `byName` holds the fields declared so far, `proposition` says
// whether a name is such a declared type, and `header` lists the names the
// theory's header binds.
function notAProposition(statement, byName, proposition = () => false, header = []) {
  // A carrier, M, or a family's member, F(A).
  const sortNamed = (node, bound) =>
    node?.kind === "name" && !bound.has(node.name) && byName.get(node.name)?.kind === "sort" ? node.name
      : node?.kind === "call" && node.fn.kind === "name" && !bound.has(node.fn.name) && byName.get(node.fn.name)?.kind === "sort"
        ? node.fn.name : null;
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
    // A member of a family of propositions, as a relation's x <= y.
    if (node.kind === "call" && sortNamed(node, bound) && propositionSort(node.fn.name)) return null;
    // A declared proposition, as a truncation.
    const head = node.kind === "call" ? node.fn : node;
    if (head.kind === "name" && !bound.has(head.name) && !byName.has(head.name) && proposition(head.name)) return null;
    return { node, why: node.kind === "name" && byName.get(node.name)?.kind === "sort"
      ? `${node.name} is a sort, whose elements are data` : "its statement is none of these" };
  };
  // The header's universes and parameters are bound, with no sort: a
  // parameter that takes a proposition's name is not that proposition.
  return check(statement, new Map(header.map(binder => [binder, null])));
}

// A theory's fields, in order, with types over the earlier fields' names,
// its notations and its parents, as the theory records them (`lookup` gives
// a parent's record by name).
function theoryFields(theory, lookup, proposition) {
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
      // One ancestor's field, with one type, is one field of the child, and
      // so is a carrier two parents give with one kind and type (L2.4c).
      if (from && existing.origin === field.origin && sameSyntax(existing.type, field.type)) return;
      if (from && existing.from && existing.kind === field.kind && ["sort", "evidence"].includes(field.kind)
        && sameSyntax(existing.type, field.type)) return;
      throw located(Error(existing.from && from
        ? `${T} gets a field named ${field.name} from both ${existing.from} and ${from}: rename one, as in ${from}(${field.name} := …).`
        : `${T} has two fields named ${field.name}: give each its own name.`), at);
    }
    const entry = { ...field, at, ...(from ? { from } : {}) };
    byName.set(field.name, entry);
    fields.push(entry);
  };
  const notate = (operator, field, at) => {
    if (ambiguousNotations?.has(operator))
      throw located(Error(`${operator} would stand for ${field} in ${T}, and its parents bind it to ${ambiguousNotations.get(operator).map(e => e.field).join(" and ")}: a notation means one operation; rename one's notation.`), at);
    if (notations.has(operator) && notations.get(operator) !== field)
      throw located(Error(`${operator} would stand for both ${notations.get(operator)} and ${field} in ${T}: a notation means one operation; rename one's notation.`), at);
    notations.set(operator, field);
  };
  // A field's binders: an index (A : set U) holds A and then its evidence,
  // A_is_set : IsSet(U, A).
  const expanded = item => item.params.flatMap(p => p.level ? [p, {
    name: token(`${p.name.text}_is_${p.level}`, p.name),
    type: call(p.level === "set" ? "IsSet" : "IsProp", [p.type, name(p.name.text, p.name)], p.name), group: p.group }] : [p]);
  // Inside the theory, a field whose index is a set is applied to that
  // index alone, F(A), for A bound as one: its evidence follows it. Applied
  // to its evidence too, F(A, A_is_set), it is left as written.
  const evidenced = (node, leveled) => {
    const rewrite = (n, bound) => {
      if (n.kind !== "call" || n.fn.kind !== "name" || bound.has(n.fn.name)) return n;
      const target = byName.get(n.fn.name);
      if (!target?.visible?.some(Boolean) || n.args.length !== target.visible.length) return n;
      const args = [];
      n.args.forEach((arg, k) => {
        args.push(rewritten(arg, rewrite, bound));
        const level = target.visible[k];
        if (!level) return;
        if (arg.kind !== "name" || bound.has(arg.name) || leveled.get(arg.name) !== level)
          throw located(Error(`${n.fn.name}'s argument ${k + 1} is a ${level === "set" ? "set" : "proposition"} with its evidence: give an index bound as one, (A : ${level} U), or write its evidence after it, ${n.fn.name}(…, A, A_is_${level}, …).`), arg);
        args.push(name(`${arg.name}_is_${level}`, arg));
      });
      return { ...n, args };
    };
    return rewritten(node, rewrite);
  };
  const leveledOf = item => new Map(item.params.filter(p => p.level).map(p => [p.name.text, p.level]));
  // forall over binders, innermost last.
  const quantified = (binders, body, at) => binders.reduceRight((inner, p) => quantifier("forall", p.name, p.type, inner, at), body);
  // Each parent prepared: its record, label, universes and renamings.
  const prepared = [];
  for (const parent of theory.parents ?? []) {
    const record = lookup(parent.name.text);
    if (!record) throw located(Error(`${parent.name.text} is not a theory here: ${T} extends theories in scope.`), parent.name);
    const label = parent.label?.text ?? snake(record.name);
    if (prepared.some(other => other.label === label))
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
    // `renotated` gives a parent's field, by its name there, another notation.
    const names = new Map(universes), renotated = new Map();
    for (const { from, to, notation } of parent.renaming) {
      const field = record.fields.find(f => f.name === from.text);
      if (!field) throw located(Error(`${record.name} has no field ${from.text}; its fields are ${record.fields.map(f => f.name).join(", ")}.`), from);
      if (names.has(from.text)) throw located(Error(`${from.text} is renamed twice.`), from);
      names.set(from.text, to.text);
      if (notation) {
        if (field.kind !== "operation" || field.arity !== 2)
          throw located(Error(`A notation names an operation's two arguments; ${from.text} is not an operation of two.`), notation);
        renotated.set(from.text, notation.operator);
      }
    }
    // A sort's evidence follows the sort's name.
    for (const field of record.fields)
      if (field.kind === "evidence" && names.has(field.of) && !names.has(field.name))
        names.set(field.name, `${names.get(field.of)}_is_${field.evidence === "IsSet" ? "set" : "prop"}`);
    prepared.push({ parent, record, label, universes, parentCount, names, renotated, at: { start: parent.start, end: parent.end } });
  }
  // Independent parents (L2.4c). A field two parents give under one name is
  // one field when it comes from one ancestor; a carrier of one name, kind
  // and type from both is one carrier of the child; any other field of one
  // name from two parents stays each parent's, named apart by its label,
  // label_name, and the name is ambiguous in the child, refused where it is
  // used and reachable through the parents' labels, label.name.
  const finalName = (p, field) => p.names.get(field.name) ?? field.name;
  const levelIn = (record, sort) => record.fields.find(field => field.kind === "evidence" && field.of === sort)?.evidence ?? null;
  const byFinal = new Map();
  for (const p of prepared) for (const field of p.record.fields) {
    const n = finalName(p, field);
    if (!byFinal.has(n)) byFinal.set(n, []);
    byFinal.get(n).push({ p, field });
  }
  const ambiguous = new Map(), allNames = new Set([...byFinal.keys(), ...theory.fields.map(item => item.name.text)]);
  for (const [n, entries] of byFinal) {
    if (new Set(entries.map(e => e.p)).size < 2 || new Set(entries.map(e => e.field.origin)).size === 1) continue;
    const carriers = entries.filter(e => ["sort", "evidence"].includes(e.field.kind));
    if (carriers.length && carriers.length < entries.length)
      throw located(Error(`${T} gets ${n} from ${entries.map(e => e.p.record.name).join(" and ")}, a carrier in one and not in another: rename one, as in ${entries.at(-1).p.record.name}(${n} := …).`), entries.at(-1).p.parent.name);
    if (carriers.length) {
      const sorts = carriers.filter(e => e.field.kind === "sort");
      const kinds = new Set(sorts.map(e => levelIn(e.p.record, e.field.name)));
      if (kinds.size > 1 || sorts.some(e => !sameSyntax(renamed(e.field.type, e.p.names, e.p.at), renamed(sorts[0].field.type, sorts[0].p.names, sorts[0].p.at))))
        throw located(Error(`${T} gets the carrier ${n} from ${sorts.map(e => e.p.record.name).join(" and ")} with different kinds or indices: rename one, as in ${sorts.at(-1).p.record.name}(${n} := …).`), sorts.at(-1).p.parent.name);
      continue;
    }
    // Entries from one ancestor are one field, reached through each of
    // their parents' labels.
    const byOrigin = new Map();
    for (const e of entries) {
      if (!byOrigin.has(e.field.origin)) {
        byOrigin.set(e.field.origin, fresh(`${e.p.label}_${n}`, allNames));
        allNames.add(byOrigin.get(e.field.origin));
      }
      const own = byOrigin.get(e.field.origin);
      e.p.names.set(e.field.name, own);
      if (!ambiguous.has(n)) ambiguous.set(n, []);
      ambiguous.get(n).push({ label: e.p.label, field: own, parentField: e.field.name });
    }
  }
  // The parents' fields, each renamed as above; and their notations, an
  // operator that two parents bind to two fields ambiguous in the child.
  const inherited = new Map(), ambiguousNotations = new Map();
  for (const p of prepared) {
    const { record, names, renotated, at, label } = p;
    // Evidence names its sort by the sort's new name, so a later renaming
    // of that sort renames the evidence too.
    for (const field of record.fields)
      add({ ...field, name: names.get(field.name) ?? field.name, type: relocated(renamed(field.type, names, at), at),
        ...(field.kind === "evidence" ? { of: names.get(field.of) ?? field.of } : {}) },
        at, record.name);
    const bind = (operator, field, parentField) => {
      if (!inherited.has(operator)) inherited.set(operator, []);
      inherited.get(operator).push({ label, field, parentField, at });
    };
    for (const [operator, field] of Object.entries(record.notations))
      if (!renotated.has(field)) bind(operator, names.get(field) ?? field, field);
    for (const [operator, list] of Object.entries(record.ambiguousNotations ?? {}))
      for (const entry of list) bind(operator, names.get(entry.field) ?? entry.field, entry.field);
    for (const [field, operator] of renotated) bind(operator, names.get(field) ?? field, field);
  }
  for (const [operator, list] of inherited) {
    const distinct = [...new Map(list.map(entry => [entry.field, entry])).values()];
    if (distinct.length === 1) notate(operator, distinct[0].field, distinct[0].at);
    else ambiguousNotations.set(operator, distinct.map(({ at: _, ...entry }) => entry));
  }
  for (const p of prepared)
    parents.push({ label: p.label, theory: p.record.name, model: p.record.model, make: p.record.make, projection: `${T}.${p.label}`,
      universes: Array.from({ length: p.parentCount }, (_, k) => p.universes.get(universeAt(k))), params: p.record.params.map(q => q.name),
      fields: p.record.fields.map(field => p.names.get(field.name) ?? field.name), kinds: p.record.fields.map(field => field.kind) });
  // Inside the theory, label.f is the field the parent labelled label gave
  // as f, and an ambiguous name is refused with the qualified forms.
  const viaLabel = new Map(prepared.map(p => [p.label, p]));
  const resolved = (node, scope = new Set()) => rewritten(node, (n, bound) => {
    if (n.kind !== "name" || bound.has(n.name.split(".")[0])) return n;
    const dot = n.name.indexOf(".");
    if (dot > 0) {
      const p = viaLabel.get(n.name.slice(0, dot)), rest = n.name.slice(dot + 1);
      if (!p || rest.includes(".") || params.some(q => q.name === n.name.slice(0, dot))) return n;
      const field = p.record.fields.find(f => f.name === rest);
      if (!field) throw located(Error(`${p.record.name}, ${T}'s parent ${p.label}, has no field ${rest}.`), n);
      return { ...n, name: finalName(p, field) };
    }
    if (ambiguous.has(n.name))
      throw located(Error(`${n.name} is ambiguous in ${T}: ${ambiguous.get(n.name).map(e => `${e.label}'s`).join(" and ")}. Write ${ambiguous.get(n.name).map(e => `${e.label}.${e.parentField}`).join(" or ")}, or rename one in extends.`), n);
    return n;
  }, scope);
  // Inside the theory, a parent's notation through its label (L2.4c):
  // label.(e) reads e's operators and names as that parent does, and
  // x label.(*) y and label.(*) its operator. A selection inside label.(e)
  // is read as it says, not as the outer label's.
  const labelled = (node, scope = new Set()) => rewritten(node, (n, bound) => {
    const qualifier = n.kind === "binary" ? n.qualifier : ["select", "operatorOf"].includes(n.kind) ? n.model : null;
    const p = qualifier?.kind === "name" && !bound.has(qualifier.name) ? viaLabel.get(qualifier.name) : null;
    if (!p) return n;
    const fieldFor = operator => {
      const parentField = p.record.notations[operator];
      if (!parentField) throw located(Error(`${p.record.name}, ${T}'s parent ${p.label}, binds no operation to ${operator}.`), n);
      return finalName(p, { name: parentField });
    };
    if (n.kind === "operatorOf") return name(fieldFor(n.operator), n);
    if (n.kind === "binary") return call(fieldFor(n.operator), [labelled(n.left, bound), labelled(n.right, bound)], n);
    const own = new Map(p.record.fields.map(field => [field.name, finalName(p, field)]));
    const inside = node => rewritten(node, (m, inner) => {
      if (["select", "operatorOf"].includes(m.kind)) return labelled(m, inner);
      if (m.kind === "binary" && m.qualifier) return labelled({ ...m, left: inside(m.left), right: inside(m.right) }, inner);
      if (m.kind === "binary" && p.record.notations[m.operator])
        return call(fieldFor(m.operator), [inside(m.left), inside(m.right)], m);
      if (m.kind === "name" && own.has(m.name) && !inner.has(m.name)) return { ...m, name: own.get(m.name) };
      return m;
    }, bound);
    return labelled(inside(n.body), bound);
  }, scope);
  for (const source of theory.fields) {
    // A field's parameters are in scope in the later ones' types and in its
    // own: a parameter named as an ambiguous field is that parameter.
    const scope = new Set();
    const within = (node, bound) => resolved(labelled(node, bound), bound);
    const item = { ...source, params: (source.params ?? []).map(p => {
      const param = { ...p, type: within(p.type, new Set(scope)) };
      scope.add(p.name.text);
      if (p.level) scope.add(`${p.name.text}_is_${p.level}`);
      return param;
    }) };
    if (source.type) item.type = within(source.type, scope);
    const origin = `${T}.${item.name.text}`;
    if (item.kind === "sort") {
      const own = universeAt(Math.max(0, headerUniverses.indexOf(item.universe?.text)));
      // A family's indices, each a binder over the earlier ones.
      const leveled = leveledOf(item), binders = expanded(item).map(p => ({ ...p, type: inTheoryUniverse(evidenced(p.type, leveled), item) }));
      const family = binders.length > 0;
      add({ name: item.name.text, kind: "sort", type: quantified(binders, name(own, item.name), item), origin,
        ...(family ? { family: true, visible: item.params.map(p => p.level ?? null) } : {}) }, item.name);
      if (item.notation) {
        const { operator, left, right } = item.notation;
        if (item.params.length !== 2 || left.text !== item.params[0].name.text || right.text !== item.params[1].name.text)
          throw located(Error(`A notation names a family's two indices in order, as in le(x, y : M) : prop U notation x <= y.`), item.notation);
        notate(operator, item.name.text, item.notation);
      }
      if (!item.level) continue;
      const evidence = item.level === "set" ? "IsSet" : "IsProp";
      const member = family ? call(item.name.text, binders.map(p => name(p.name.text, item.name)), item.name) : name(item.name.text, item.name);
      add({ name: `${item.name.text}_is_${item.level}`, kind: "evidence", evidence, of: item.name.text,
        type: quantified(binders, call(evidence, [name(own, item.name), member], item.name), item),
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
    // forall over the parameters, innermost last, each index's evidence
    // after it.
    const leveled = leveledOf(item);
    let type = quantified(expanded(item).map(p => ({ ...p, type: evidenced(p.type, leveled) })), evidenced(item.type, leveled), item);
    type = inTheoryUniverse(type, item);
    // Inside the theory, a notation means its operation.
    const operatorsAsCalls = node => rewritten(node, (n, bound) => {
      if (n.kind === "binary" && ambiguousNotations.has(n.operator)) {
        const list = ambiguousNotations.get(n.operator);
        throw located(Error(`${n.operator} is ambiguous in ${T}: it is ${list.map(e => `${e.label}'s ${e.parentField}`).join(" and ")}. Write ${
          list.map(e => `x ${e.label}.(${n.operator}) y`).join(" or ")}, or give one another notation in extends.`), n);
      }
      return n.kind === "binary" && notations.has(n.operator) && !bound.has(notations.get(n.operator))
        ? call(notations.get(n.operator), [operatorsAsCalls(n.left), operatorsAsCalls(n.right)], n)
        : n;
    });
    type = operatorsAsCalls(type);
    if (item.kind === "law") {
      const data = notAProposition(type, byName, proposition, header.map(binder => binder.text));
      if (data)
        throw located(Error(`The law ${item.name.text} must state a proposition: an equation between elements of a sort, Void, a type declared at prop, or forall, -> or and over those; ${data.why}. A law holds no data, and homomorphisms ignore laws: declare data as an operation or a constant.`), data.node);
    }
    add({ name: item.name.text, kind: item.kind, arity: item.params.length, type, origin,
      ...(leveled.size ? { visible: item.params.map(p => p.level ?? null) } : {}) }, item.name);
  }
  for (const field of fields) {
    if (field.name.includes(".")) throw located(Error(`A field's name is a plain name; ${field.name} is not.`), field.at);
    if (header.some(binder => binder.text === field.name))
      throw located(Error(`${T}'s header binds ${field.name}, which names a field too: give each its own name.`), field.at);
  }
  // A parent's label names its projection, T.label, beside the fields' T.f.
  for (const p of prepared)
    if (byName.has(p.label))
      throw located(Error(`${T}'s parent ${p.record.name} is labelled ${p.label}, which names a field of ${T} too: label it apart, as in base : ${p.record.name}.`), p.parent.label ?? p.parent.name);
  return { fields, notations, parents, universes: headerUniverses, params: params.map(({ at: _, ...p }) => p),
    ambiguous: Object.fromEntries([...ambiguous].map(([n, list]) => [n, list])), ambiguousNotations: Object.fromEntries(ambiguousNotations) };
}

// The declarations a theory expands to, and its record, which a theory
// that extends it reads (`lookup` gives the record of a theory by name).
export function expandTheory(theory, lookup = () => null, proposition = () => false) {
  const T = theory.name.text, at = theory.name;
  const { fields, notations, parents, universes: headerUniverses, params, ambiguous, ambiguousNotations } = theoryFields(theory, lookup, proposition);
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
    name: T, model: T, make: `${T}.make`, universes: headerUniverses, params, ambiguous, ambiguousNotations,
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
  // Homomorphisms and isomorphisms, unless an operation's argument mixes a
  // carrier's variance (morphisms.mjs): their source, parsed and placed at the theory's
  // name. A generated definition's name is dotted, which a def cannot
  // spell, so each is parsed under a placeholder and then renamed.
  const morphisms = morphismSource(record, other => Boolean(lookup(other)));
  if (morphisms.missing) record.noMorphisms = morphisms.missing;
  else {
    // Homomorphisms without isomorphisms: the source stops after Hom's.
    if (morphisms.missingIso) record.noIsomorphisms = morphisms.missingIso;
    // A parameter's type is written in place of its marker, in the
    // homomorphism's universes, and an operation's type in a model's: its
    // carriers that model's, A.M.
    const inUniverses = list => list.map((u, j) => [universeAt(j), u]);
    const parameterType = new Map([
      ...params.map((p, k) => [morphisms.parameterMarker(k), renamed(p.type, new Map(inUniverses(morphisms.universes)), at)]),
      ...[...morphisms.typeMarkers].map(([marker, { type, model, universes }]) => [marker,
        renamed(type, new Map([...fields.map(field => [field.name, `${model}.${field.name}`]), ...inUniverses(universes)]), at)]),
    ]);
    const parsed = parse(morphisms.declarations.map((d, k) => d.source.replace(/^def \S+?(?=[{(:])/, `def generated_${k}`)).join("\n")).declarations
      .map(d => JSON.parse(JSON.stringify(d), (key, value) =>
        value?.kind === "name" && parameterType.has(value.name) ? parameterType.get(value.name) : value));
    parsed.forEach((d, k) => {
      const { name: declName, role, field, record: morphismRecord, labels = {} } = morphisms.declarations[k];
      // A parameter whose binder is named apart from its field is called
      // by the field's name.
      for (const p of d.params ?? []) if (Object.hasOwn(labels, p.name.text)) p.label = labels[p.name.text];
      out.push({ ...relocated(d, at), name: token(declName, at),
        generated: { theory: T, role, ...(field ? { field } : {}) }, ...(morphismRecord ? { theory: morphismRecord } : {}) });
    });
  }
  return out;
}
