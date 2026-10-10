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

import { parse, reservedNames } from "./parser.mjs";
import { morphismSource } from "./morphisms.mjs";
import {dependencyGraph} from "./dependencies.mjs";
// A copy of a syntax tree with `rewrite(node, bound)` applied to each node,
// outermost first; `bound` holds the names bound there, by every binding
// form (scopes.mjs).
import { rewritten, substituted, renamedApart, freeNames, relocated, freshName } from "./scopes.mjs";

// The universes of a theory's carriers, in the fields a theory records, the
// first, UNIVERSE, and the k-th: each expansion names them afresh.
const UNIVERSE = "\u0000universe";
export const universeAt = k => k === 0 ? UNIVERSE : `${UNIVERSE}${k}`;

// An error at a node of the theory's text.
const located = (error, node) => Object.assign(error, { offset: node.start, sourceEnd: node.end });

// Nodes of the source syntax, placed at `at`, the theory text they come from;
// synthetic where `at` is, as an initial/free expansion's (initial-models.mjs).
const place = at => ({ start: at.start, end: at.end, ...(at.synthetic ? { synthetic: true } : {}) });
const token = (text, at) => ({ text, ...place(at) });
const name = (text, at) => ({ kind: "name", name: text, ...place(at) });
const call = (fn, args, at) => ({ kind: "call", fn: typeof fn === "string" ? name(fn, at) : fn, args, ...place(at) });
const quantifier = (kind, binder, domain, body, at) =>
  ({ kind, name: typeof binder === "string" ? token(binder, at) : binder, binderKind: kind, domain, body, ...place(at) });
const projection = (value, index, at) => ({ kind: "projection", value, index, ...place(at) });
const pair = (left, right, at) => ({ kind: "pair", left, right, ...place(at) });
export const nodes = { token, name, call };

// Free names replaced by others: `names` maps a name to its replacement's name.
const renamed = (node, names, at) => renamedApart(node, names, (binder, site) => {
  const before = [...names].find(([,after])=>after===binder)?.[0];
  return located(Error(`Renaming ${before} to ${binder} would capture a variable named ${binder}; pick another name.`), site??at);
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
// An unlabelled parent's label: its name in snake case, CommMonoid as comm_monoid.
export const snake = text => text.replace(/([a-z0-9])([A-Z])/g, "$1_$2").toLowerCase();
const syntaxValue = (key, value) => ["spelling", "label", "synthetic"].includes(key)
  || typeof value === "number" && /^(start|end)$|Start$|End$/.test(key) ? undefined : value;
const sameSyntax = (a, b) => JSON.stringify(a, syntaxValue) === JSON.stringify(b, syntaxValue);
// Keep each written shared domain outside its binders. Generated evidence
// may share a group number but has a different, dependent domain.
function parameterGroups(params) {
  const groups = [];
  for (let k = 0; k < params.length;) {
    const first = params[k++], members = [first];
    while (first.group !== undefined && k < params.length && params[k].group === first.group && sameSyntax(params[k].type, first.type))
      members.push(params[k++]);
    groups.push(members);
  }
  return groups;
}

// Retained operations transform as declarations, with their whole telescope.
// Record storage uses plain names; scope traversal always sees binder tokens.
const derivedSyntax = d => ({kind:"derived", name:token(d.name,d.at),
  params:d.params.map(p=>({name:{...token(p.name,p.at??d.at),label:p.label??p.name},type:p.type,group:p.group})),
  type:d.type,value:d.value,...place(d.at)});
const derivedRecord = (syntax, metadata) => ({...metadata,
  params:syntax.params.map(p=>({name:p.name.text,label:p.name.label??p.name.text,at:p.name,type:p.type,group:p.group})),
  type:syntax.type,value:syntax.value});

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
    // Inlining a retained helper can expose a resolved declaration. Its
    // spelling may now be bound to something else; ask about its identity.
    if (head.kind === "reference" && proposition(head.binding)) return null;
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
function theoryFields(theory, lookup, proposition, capture) {
  const T = theory.name.text, fields = [], notations = new Map(), parents = [], byName = new Map();
  // Each notation's operand recipes: the notation an operand is read in,
  // other than the current one (L2.10b), as nat for x ^ nat.(n).
  const recipes = new Map();
  // A notation's key: its operator, unary - for -x, or numeral.
  const keyOf = notation => notation.numeral ? "numeral" : notation.unary ? "unary -" : notation.operator;
  // Derived operations, a theory's own and its parents' (L2.10b): each
  // applied in a later field is its value, its parameters substituted.
  const derived = [], derivedByName = new Map();
  const inlineDerived = (node, purpose = "type") => {
    // Substitute the helper as a lambda through the entire enclosing tree
    // before beta reduction. This freshens the caller's binders as well as
    // the helper's: a law parameter c must not capture the helper's field c.
    const used = freeNames(node);
    const helpers = new Map(derived.filter(d => !d.recursive && used.has(d.name)).map(d => {
      const value = parameterGroups(d.params).reduceRight((body, group) => ({kind: "binderGroup", binderKind: "lambda",
        names: group.map(p => token(p.name, d.at)), domain: group[0].type, body, ...place(d.at)}), d.value);
      return [d.name, {...value, inlineName: d.name, inlineArity: d.params.length}];
    }));
    const expanded = helpers.size ? substituted(node, helpers, (binder, at) => {
      const helper = [...helpers].find(([, value]) => freeNames(value).has(binder))?.[0];
      return located(Error(`Inlining ${helper} here would capture its field ${binder}: rename the enclosing pattern or statement binding.`), at);
    }) : node;
    return rewritten(expanded, (n, bound) => {
      if (n.kind === "call" && n.fn.inlineName && n.args.length === n.fn.inlineArity) {
        const args = new Map();
        let body = n.fn, index = 0;
        while (index < n.args.length && body.kind === "binderGroup") {
          for (const parameter of body.names) args.set(parameter.text, inlineDerived(n.args[index++], purpose));
          body = body.body;
        }
        return substituted(body, args, binder => located(Error(`${n.fn.inlineName}'s pattern binds ${binder}, which an argument here names: rename it in ${n.fn.inlineName}.`), n));
      }
      const d = n.kind === "call" && n.fn.kind === "name" && !bound.has(n.fn.name) ? derivedByName.get(n.fn.name) : null;
      if (d?.recursive && purpose === "type") throw located(Error(`${d.name} is recursive, and a field's type cannot unfold it: state the law over a model, outside the theory.`), n);
      return n;
    });
  };
  // The header's universes are the model's, which each expansion names
  // afresh; a theory without a header has one. Its parameters are every
  // model's, as the header writes them (L2.4c).
  const headerUniverses = (theory.universes ?? []).map(u => u.text);
  const universeCount = Math.max(1, headerUniverses.length);
  const universe = new Map(headerUniverses.map((u, k) => [u, universeAt(k)]));
  const inTheoryUniverse = (node, at) => universe.size ? renamed(node, universe, at) : node;
  const parameterScope = new Set(headerUniverses);
  const params = [];
  for (const members of parameterGroups(theory.params ?? [])) {
    const first = members[0];
    // A group's domain is outside all of its binders, even when one takes
    // the name of a global mentioned by that domain.
    const type = capture(inTheoryUniverse(first.type, first.name), parameterScope);
    for (const p of members) params.push({name: p.name.text, type, at: p.name});
    for (const p of members) parameterScope.add(p.name.text);
  }
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
    const entry = { ...field, type: capture(field.type, new Set([...header.map(b => b.text), ...byName.keys()])),
      at, ...(from ? { from } : {}) };
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
  // A group's shared domain is outside every name the group binds.
  const quantified = (binders, body, at) => parameterGroups(binders).reduceRight((inner, members) =>
    members.length === 1 ? quantifier("forall", members[0].name, members[0].type, inner, at)
      : {kind: "binderGroup", binderKind: "forall", names: members.map(p => p.name), domain: members[0].type, body: inner, ...place(at)}, body);
  // Each parent prepared: its record, label, universes and renamings.
  const prepared = [];
  for (const parent of theory.parents ?? []) {
    const record = lookup(parent.name.text);
    if (!record) throw located(Error(`${parent.name.text} is not a theory here: ${T} extends theories in scope.`), parent.name);
    const label = parent.label?.text ?? snake(record.name);
    // A label is a field's name, so it is none of the reserved words.
    if (!parent.label && reservedNames.has(label))
      throw located(Error(`${parent.name.text}'s label would be ${label}, which is reserved: label it, as in other : ${parent.name.text}.`), parent.name);
    if (prepared.some(other => other.label === label))
      throw located(Error(`${T} has two parents labelled ${label}: label one, as in other : ${parent.name.text}.`), parent.label ?? parent.name);
    // The parent's universes are the child's: its one universe the child's
    // one, or each by its name. A parent whose header binds no universe has
    // one, by the name its expansion gives it. Its parameters are the
    // child's of the same names and types.
    const universes = new Map(), parentCount = Math.max(1, record.universes.length);
    if (parentCount === 1 && universeCount === 1) universes.set(UNIVERSE, UNIVERSE);
    else (record.universeLabels ?? record.universes).forEach((u, k) => {
      const own = headerUniverses.indexOf(u);
      if (own < 0) throw located(record.generatedUniverse
        ? Error(`${T} extends ${record.name}, whose header binds no universe: bind ${u}, its public universe parameter, in ${T}'s header, or name that universe in ${record.name}'s header.`)
        : Error(`${T} extends ${record.name}, whose header binds the universe ${u}: bind ${u} in ${T}'s header too.`), parent.name);
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
        if (field.kind !== "operation" || field.arity !== (notation.unary ? 1 : 2))
          throw located(Error(notation.unary ? `-x names an operation's one argument; ${from.text} is not an operation of one.`
            : `A notation names an operation's two arguments; ${from.text} is not an operation of two.`), notation);
        renotated.set(from.text, keyOf(notation));
        recipes.set(keyOf(notation), { left: notation.leftView?.text ?? null, right: notation.rightView?.text ?? null });
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
        byOrigin.set(e.field.origin, freshName(`${e.p.label}_${n}`, allNames));
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
    for (const d of record.derived ?? []) {
      if (derivedByName.has(d.name)) continue;
      const entry = derivedRecord(relocated(renamed(derivedSyntax({...d,at}), names, at), at), {...d, at});
      derived.push(entry);
      derivedByName.set(entry.name, entry);
    }
    const bind = (operator, field, parentField) => {
      if (!inherited.has(operator)) inherited.set(operator, []);
      inherited.get(operator).push({ label, field, parentField, at });
    };
    for (const [operator, field] of Object.entries(record.notations)) {
      if (renotated.has(field)) continue;
      bind(operator, names.get(field) ?? field, field);
      if (record.recipes?.[operator]) recipes.set(operator, record.recipes[operator]);
    }
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
    const item = { ...source, params: [] };
    for (const members of parameterGroups(source.params ?? [])) {
      const type = within(members[0].type, scope);
      for (const p of members) item.params.push({...p, type});
      for (const p of members) {
        scope.add(p.name.text);
        if (p.level) scope.add(`${p.name.text}_is_${p.level}`);
      }
    }
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
        const { operator, left, right, unary } = item.notation;
        if (unary || item.params.length !== 2 || left.text !== item.params[0].name.text || right.text !== item.params[1].name.text)
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
    if (item.notation?.numeral) {
      if (item.kind !== "derived" || item.params.length !== 1 || !(item.params[0].type.kind === "name" && item.params[0].type.name === "Nat"))
        throw located(Error(`notation numeral reads a plain numeral: it marks a derived operation of one natural number, as def of_nat(n : Nat) : R := … notation numeral.`), item.notation);
      notate("numeral", item.name.text, item.notation);
    } else if (item.notation) {
      const { operator, left, right, unary, leftView, rightView } = item.notation;
      if (unary) {
        if (!["operation", "derived"].includes(item.kind) || item.params.length !== 1 || left.text !== item.params[0].name.text)
          throw located(Error(`-x names an operation's one argument, as in neg(x : M) : M notation -x.`), item.notation);
      } else {
        if (!["operation", "derived"].includes(item.kind) || item.params.length !== 2)
          throw located(Error(`A notation names an operation's two arguments, as in mul(x, y : M) : M notation x * y; ${item.name.text} has ${["none", "one"][item.params.length] ?? item.params.length}.`), item.notation);
        if (left.text !== item.params[0].name.text || right.text !== item.params[1].name.text)
          throw located(Error(`The notation of ${item.name.text} writes its arguments in order: ${item.params[0].name.text} ${operator} ${item.params[1].name.text}.`), item.notation);
      }
      // An operand that is a carrier's element is read in the current
      // notation; any other names its own, as x ^ nat.(n) (L2.10b).
      for (const [k, token, view] of unary ? [[0, left, leftView]] : [[0, left, leftView], [1, right, rightView]]) {
        const type = item.params[k].type;
        if (!view && !(type.kind === "name" && byName.get(type.name)?.kind === "sort"))
          throw located(Error(`The notation of ${item.name.text} reads ${token.text} in the notation selected where it is used, which is ${T}'s; ${token.text} is no carrier's element: name the notation it is read in, as ${token.text === left?.text && !unary ? `nat.(${token.text}) ^ y` : `x ^ nat.(${token.text})`}.`), token);
      }
      notate(keyOf(item.notation), item.name.text, item.notation);
      recipes.set(keyOf(item.notation), { left: leftView?.text ?? null, right: rightView?.text ?? null });
    }
    // forall over the parameters, innermost last, each index's evidence
    // after it.
    const leveled = leveledOf(item);
    let type = quantified(expanded(item).map(p => ({ ...p, type: evidenced(p.type, leveled) })), evidenced(item.type, leveled), item);
    type = inTheoryUniverse(type, item);
    // Inside the theory, a notation means its operation.
    // An operand with a recipe is read in its notation, which the theory's
    // own does not rewrite.
    const operand = (node, view) => view ? { kind: "select", model: name(view, node), body: node, start: node.start, end: node.end }
      : operatorsAsCalls(node);
    const operatorsAsCalls = node => rewritten(node, (n, bound) => {
      // Another notation's selection, nat.(n + 1), is that notation's.
      if (n.kind === "select") return n;
      // x > y is y < x, and x >= y is y <= x.
      if (n.kind === "binary" && [">", ">="].includes(n.operator) && notations.has(n.operator === ">" ? "<" : "<="))
        return operatorsAsCalls({ ...n, operator: n.operator === ">" ? "<" : "<=", left: n.right, right: n.left });
      const key = n.kind === "negation" ? "unary -" : n.kind === "binary" && !n.qualifier ? n.operator : null;
      if (key && ambiguousNotations.has(key)) {
        const list = ambiguousNotations.get(key);
        throw located(Error(`${key} is ambiguous in ${T}: it is ${list.map(e => `${e.label}'s ${e.parentField}`).join(" and ")}. Write ${
          list.map(e => `x ${e.label}.(${key}) y`).join(" or ")}, or give one another notation in extends.`), n);
      }
      if (!key || !notations.has(key) || bound.has(notations.get(key))) return n;
      const recipe = recipes.get(key) ?? {};
      return n.kind === "negation" ? call(notations.get(key), [operand(n.operand, recipe.left)], n)
        : call(notations.get(key), [operand(n.left, recipe.left), operand(n.right, recipe.right)], n);
    });
    // A derived operation (L2.10b) is no field: its type and value, over
    // the fields, generate T.f(m, …); later fields read it inlined.
    if (item.kind === "derived") {
      if (byName.has(item.name.text) || derivedByName.has(item.name.text))
        throw located(Error(`${T} has two fields named ${item.name.text}: give each its own name.`), item.name);
      // Evidence insertion precedes scoping: generated evidence parameters
      // form dependent groups of their own. Every subsequent transformation
      // sees domains, result and body beneath the actual parameter binders.
      const params = parameterGroups(expanded(item)).flatMap((group,index)=>group.map(p=>({
        ...p, type:evidenced(p.type,leveled),group:index})));
      const prepared = {...item,params,type:evidenced(item.type,leveled),value:evidenced(item.value,leveled)};
      const transformed = inlineDerived(operatorsAsCalls(inTheoryUniverse(prepared,item)), "value");
      // Value calls to checked earlier recursive operations stay as calls;
      // the parameter/result interface still has the type-unfolding rule.
      inlineDerived({...transformed,value:null}, "type");
      const entry = derivedRecord(transformed,{name:item.name.text,origin,at:item.name});
      // A recursive one, as of_nat, is called, not inlined, in later fields:
      // its value names it free, and no parameter of its takes its name.
      entry.recursive = !entry.params.some(p => p.name === entry.name) && freeNames(entry.value).has(entry.name);
      const scope = new Set([...header.map(b => b.text), ...byName.keys(), ...derivedByName.keys(), entry.name]);
      Object.assign(entry,derivedRecord(capture(derivedSyntax(entry),scope),entry));
      derived.push(entry);
      derivedByName.set(entry.name, entry);
      continue;
    }
    type = inlineDerived(operatorsAsCalls(type));
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
  return { fields, notations, recipes, derived, parents, universes: headerUniverses, params: params.map(({ at: _, ...p }) => p),
    ambiguous: Object.fromEntries([...ambiguous].map(([n, list]) => [n, list])), ambiguousNotations: Object.fromEntries(ambiguousNotations) };
}

// The declarations a theory expands to, and its record, which a theory
// that extends it reads (`lookup` gives the record of a theory by name).
export function expandTheory(theory, lookup = () => null, proposition = () => false, capture = node => node, reference = node => node,
  knownTheory = other => Boolean(lookup(other))) {
  // What the expansion places at the theory's name is generated, and links
  // nowhere there (cubical-program.mjs): the name links to its models' type.
  const T = theory.name.text, at = { ...theory.name, synthetic: true };
  // Only the expansion's builders introduce declaration references. Reused
  // source syntax is already resolved and is never searched for matching text.
  const globalCall = (fn, args, span) => call(reference(name(fn, span), "generated"), args, span);
  const outerCall = (fn, args, span) => call(reference(name(fn, span), "outer"), args, span);
  const { fields, notations, recipes, derived, parents, universes: headerUniverses, params, ambiguous, ambiguousNotations } = theoryFields(theory, lookup, proposition, capture);
  if (!fields.length) throw located(Error(`${T} has no fields: a theory declares sorts, operations and laws.`), at);
  const taken = new Set([...namesIn(theory), ...fields.map(field => field.name), ...fields.flatMap(field => [...namesIn(field.type)]),
    ...derived.flatMap(operation => [...namesIn(operation)])]);
  // The header's names for the universes, or fresh ones without a header:
  // U, or U_1 when U is taken. The public label depends only on the header,
  // never on an internal binder that makes this generated name fresh.
  const universes = headerUniverses.length ? headerUniverses : [freshName("U", taken)], model = freshName("m", taken);
  const universeLabels = headerUniverses.length ? headerUniverses : [freshName("U", new Set(params.map(p => p.name)))];
  const inUniverse = node => renamed(node, new Map(universes.map((u, k) => [universeAt(k), u])), at);
  // The header's binders, the universes in one group and then each
  // parameter; `implicit` says which are implicit.
  const headerParameters = ({ universe = false, parameter = false } = {}) => [
    ...universes.map((u, k) => ({ name: token(u, at), label: universeLabels[k], bound: name("UU0", at), group: 0, ...(universe ? { implicit: true } : {}) })),
    ...params.map((p, k) => ({ name: token(p.name, at), type: inUniverse(p.type), group: k + 1, ...(parameter ? { implicit: true } : {}) })),
  ];
  const nextGroup = params.length + 1;
  const modelType = span => globalCall(T, [...universes, ...params.map(p => p.name)].map(text => name(text, span)), span);
  // Each declaration reads its operators and numerals in the file's
  // selection where the theory stands (L2.10j).
  const declaration = (declName, declParams, type, value, span, generated, extra = {}) => ({
    kind: "def", name: token(declName, span), params: declParams, type, ...(theory.uses ? { uses: theory.uses } : {}),
    ...(declParams.some(p => p.implicit) ? { implicitParameters: place(span) } : {}),
    ...(type ? {body: [{ kind: "exact", value, ...place(span) }], typedValue: true} : {
      params:[],valueParameters:declParams,
      value:parameterGroups(declParams).reduceRight((body,group)=>({kind:"binderGroup",binderKind:"lambda",
        names:group.map(p=>p.name),...(group[0].bound?{bound:group[0].bound}:{domain:group[0].type}),body,...place(span)}),value),
      valueStart:value.start,valueEnd:value.end,
    }), ...place(span),
    generated: { theory: T, family: generated.role === "derived" ? `derived:${generated.field}` : "base", ...generated }, ...extra,
  });
  // Retain both internal universe names and public labels. Inheritance and
  // named arguments use the labels; fresh internal binders are not an API.
  const record = {
    name: T, model: T, make: `${T}.make`, universes, universeLabels, ...(headerUniverses.length ? {} : { generatedUniverse: true }), params, ambiguous, ambiguousNotations,
    fields: fields.map(({ at: _, from: __, ...field }) => ({ ...field, projection: `${T}.${field.name}` })),
    notations: Object.fromEntries(notations), recipes: Object.fromEntries(recipes), parents,
    derived: derived.map(({ at: _, ...d }) => ({ ...d, projection: `${T}.${d.name}` })),
  };
  const identity = field => reference(name(`${T}.${field.name}`,field.at??at),"generated").binding??`${T}.${field.name}`;
  for(const field of [...record.fields,...record.derived]) {
    field.identity=identity(field);
    field.originIdentity??=field.identity;
  }
  const owner = reference(name(T,at),"generated").binding??T;
  record.dependencies=dependencyGraph(owner,[
    ...universes.map((_,k)=>({identity:`${owner}:universe:${k}`,name:universeAt(k),label:universeLabels[k],category:"universe"})),
    ...params.map((p,k)=>({identity:`${owner}:parameter:${k}`,name:p.name,category:"parameter",type:p.type,at:p.at})),
  ],[
    ...fields.map((field,k)=>({...field,identity:record.fields[k].identity,signature:field.type})),
    ...derived.map((field,k)=>({...field,kind:"derived",identity:record.derived[k].identity,
      signature:{...derivedSyntax(field),value:null},value:derivedSyntax(field)})),
  ]);
  // The sorts' evidence comes from hlevels.
  const requires = [...new Set(fields.filter(field => field.evidence).map(field => field.evidence))];
  const out = [];
  // Infer the model type's universe from its entire telescope, including
  // fixed domains above the carrier universe. Hom/Iso use the same ordinary
  // inference rather than guessing a level from the header alone.
  let modelBody = inUniverse(fields.at(-1).type);
  for (let k = fields.length - 2; k >= 0; k--)
    modelBody = quantifier("exists", token(fields[k].name, fields[k].at), inUniverse(fields[k].type), modelBody, fields[k].at);
  out.push(declaration(T, headerParameters(), null, modelBody, at,
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
      ? globalCall(projected.get(n.name), [name(model, n)], n) : n);
    let value = name(model, field.at);
    for (let j = 0; j < k; j++) value = projection(value, 2, field.at);
    if (k < fields.length - 1) value = projection(value, 1, field.at);
    out.push(declaration(`${T}.${field.name}`, [...headerParameters({ universe: true, parameter: true }),
      { name: token(model, field.at), type: modelType(field.at), group: nextGroup }], type, value, field.at,
    { role: "projection", field: field.name }));
    projected.set(field.name, `${T}.${field.name}`);
  });
  // T.d{{U < UU0, params}}(m : T(U, params), args…) : A := value, for each
  // derived operation, its fields read through m (L2.10b).
  for (const d of derived) {
    const own = new Set();
    // Its fields through m; a recursive one's call to itself, T.d(m, …).
    const through = node => rewritten(inUniverse(node), (n, bound) => {
      if (d.recursive && n.kind === "call" && n.fn.kind === "name" && n.fn.name === d.name && !bound.has(d.name))
        return {...call(`${T}.${d.name}`, [name(model, n), ...n.args.map(through)], n), kind: "recursiveCall"};
      return n.kind === "name" && projected.has(n.name) && !bound.has(n.name) && !own.has(n.name)
        ? globalCall(projected.get(n.name), [name(model, n)], n) : n;
    });
    const parameters = [];
    for (const members of parameterGroups(d.params)) {
      const group = nextGroup + 1 + parameters.length, type = through(members[0].type);
      for (const p of members) parameters.push({name: token(p.name, p.at??d.at),label:p.label??p.name,type,group});
      for (const p of members) own.add(p.name);
    }
    out.push(declaration(`${T}.${d.name}`, [...headerParameters({ universe: true, parameter: true }),
      { name: token(model, d.at), type: modelType(d.at), group: nextGroup },
      ...parameters],
    through(d.type), through(d.value), d.at, { role: "derived", field: d.name }));
    projected.set(d.name,`${T}.${d.name}`);
  }
  // T.p{{U < UU0, params}}(m : T(U, params)) : P(U, params) := P.make(params, T.f(m), …),
  // each of P's fields from the child's field it became.
  for (const [index, parent] of parents.entries()) {
    const span = theory.parents[index];
    const parentModel = outerCall(parent.theory, [...parent.universes.map(u => inUniverse(name(u, span))), ...parent.params.map(p => name(p, span))], span);
    out.push(declaration(parent.projection, [...headerParameters({ universe: true, parameter: true }),
      { name: token(model, span), type: modelType(span), group: nextGroup }], parentModel,
    outerCall(parent.make, [...parent.params.map(p => name(p, span)), ...parent.fields.map(field => globalCall(`${T}.${field}`, [name(model, span)], span))], span), span,
    { role: "projection", field: parent.label }));
  }
  // Homomorphisms and isomorphisms, unless an operation's argument mixes a
  // carrier's variance (morphisms.mjs): their source, parsed and placed at the theory's
  // name. A generated definition's name is dotted, which a def cannot
  // spell, so each is parsed under a placeholder and then renamed.
  const morphisms = morphismSource(record, knownTheory);
  record.support={hom:morphisms.support,iso:morphisms.isoSupport};
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
    // Resolve only the template's declaration references, before inserting
    // source fragments. A splice is an AST, never source to parse or resolve.
    const parsed = parse(morphisms.declarations.map((d, k) => d.source.replace(/^def \S+?(?=[{(:])/, `def generated_${k}`)).join("\n")).declarations
      .map(d => rewritten(d, n => {
        if (n.kind !== "name") return n;
        if (parameterType.has(n.name)) return parameterType.get(n.name);
        const global = morphisms.references.get(n.name);
        return global ? reference({...n, name: global.name}, global.scope) : n;
      }));
    parsed.forEach((d, k) => {
      const { name: declName, role, family, field, record: morphismRecord, labels = {} } = morphisms.declarations[k];
      // A parameter whose binder is named apart from its field is called
      // by the field's name.
      for (const p of d.params ?? []) if (Object.hasOwn(labels, p.name.text)) p.label = labels[p.name.text];
      // Generated from text, all of it stands at the theory's name.
      out.push({ ...relocated(d, at), name: token(declName, at), ...(theory.uses ? { uses: theory.uses } : {}),
        generated: { theory: T, role, family, ...(field ? { field } : {}) }, ...(morphismRecord ? { theory: morphismRecord } : {}) });
    });
  }
  return out;
}
