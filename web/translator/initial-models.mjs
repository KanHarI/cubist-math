// Initial and free models of a theory (L2.6; core-theories.md, "Initial and
// free models"). `initial N : T(…);` and `free W(A : U0) : T(…) on A;`
// declare, with no new kernel rule:
//   N, a declared type with a constructor for each of T's operations, N.mul,
//     a path constructor for each law, N.mul_assoc, and the squash of the
//     carrier's h-level; free adds the generator W.gen(a : A);
//   N.model : T(…), the model on N;
//   N.fold_map(target, evidence, x), recursion into a model's carrier, and
//   N.fold(target) : T.Hom(N.model, target), whose preservation laws hold by
//     computation. free's take the generators' images, g : A -> target.M.
// A theory qualifies with one carrier, a set or a proposition, strictly
// positive operations and equational laws, none named as N's other names,
// model, fold_map, fold, squash and free's gen; anything else is refused,
// naming the field. The declared type is checked as any other.
import {theoryBinding} from "./theories.mjs";
import {universeAt} from "../cubist/theories.mjs";
import {parse} from "../cubist/parser.mjs";
import {freeNames, substituted} from "../cubist/scopes.mjs";
import {assignArguments} from "./arguments.mjs";

// The declarations an initial or free model expands to, checked in its
// place; one that does not expand fails as a declaration of its name.
export function initialDeclarations(t, module, d, env, declarations) {
  try { return expand(module, d, env); }
  catch (failure) {
    const error = failure.offset !== undefined ? failure : module.locate(failure, d.name);
    t.onDeclarationStart?.(d);
    declarations.push({ name: d.name.text, status: "not-translated", reason: error.message, errorStart: error.offset, errorEnd: error.sourceEnd });
    env.set(d.name.text, { tag: "Untranslated", name: d.name.text, binding: t.checker.bindingName?.(d.name.text) ?? d.name.text, reason: error.message });
    t.onDeclaration?.(d, declarations.at(-1));
    return [];
  }
}

function expand(module, d, env) {
  const N = d.name.text, source = module.source, text = node => source.slice(node.start, node.end).trim();
  const head = d.theory.kind === "call" ? d.theory.fn : d.theory;
  const entry = head.kind === "name" ? env.get(theoryBinding(head.name)) : null;
  if (entry?.tag !== "Theory")
    throw module.locate(notATheory(d.kind, text(d.theory)), d.theory);
  const record = entry.record, T = record.name, args = d.theory.kind === "call" ? d.theory.args : [];
  const parameters = [...record.universes.map(name => ({ name })), ...record.params];
  const argument = assignArguments({ ...d.theory, args }, parameters, module, T);
  if (args.length !== record.universes.length + record.params.length)
    throw module.locate(theoryArguments(T, record.universes.length + record.params.length, args.length), d.theory);
  // Named arguments give their parameter; positional ones fill the rest,
  // just as in an ordinary application of the theory's type of models.
  const given = new Map([...record.universes.map((_, k) => [universeAt(k), argument(k)]),
    ...record.params.map((p, k) => [p.name, argument(record.universes.length + k)])]);
  // A field's syntax with names replaced, its binders renamed apart from the
  // names put there; a pattern's binder, which is not renamed, is refused.
  const put = (field, node, map) => substituted(node, map, name => module.locate(capturedBy(field, name), d.theory));

  // One carrier, a set or a proposition.
  const carriers = record.fields.filter(f => f.kind === "sort");
  if (carriers.length !== 1 || carriers[0].family) throw module.locate(notOneCarrier(T, carriers.map(f => f.name)), d.theory);
  const carrier = carriers[0].name;
  const evidence = record.fields.find(f => f.kind === "evidence" && f.of === carrier);
  if (!evidence) throw module.locate(untruncatedCarrier(T, carrier), d.theory);
  const level = evidence.evidence === "IsSet" ? "set" : "prop";
  const universe = put(carrier, carriers[0].type, given);
  const derived = new Set((record.derived ?? []).map(op => op.name)), free = d.kind === "free";
  // N's constructors are named as the fields, beside its other names: a
  // field named as one of those would be both.
  const others = new Map([["model", "model"], ["fold_map", "recursion"], ["fold", "fold"], ["squash", "squash"],
    ...(free ? [["gen", "generator"]] : [])]);
  const clash = record.fields.find(f => ["operation", "law"].includes(f.kind) && others.has(f.name));
  if (clash) throw module.locate(generatedName(T, clash.name, N, others.get(clash.name)), d.theory);

  // The carrier inside the declared type: N, or W(A) for a free model with
  // parameters.
  const names = d.params.map(p => p.name.text);
  const at = { start: d.start, end: d.end };
  const self = names.length ? { kind: "call", fn: { kind: "name", name: N, ...at }, args: names.map(n => ({ kind: "name", name: n, ...at })), ...at }
    : { kind: "name", name: N, ...at };
  const operations = record.fields.filter(f => f.kind === "operation").map(f => f.name);
  const constructor = name => `${N}.${name}`;
  // A field's syntax inside the declared type: the carrier is N, each
  // operation its constructor, and the theory's universes and parameters
  // as given.
  const inside = new Map([...given, [carrier, self], ...operations.map(op => [op, { kind: "name", name: constructor(op), ...at }])]);
  // A field's binders, each the carrier or a type that does not mention it,
  // and its body, as written and inside the declared type. There each binder
  // holds over the later binders and the body, so law idem(c : M) : c = c
  // keeps its c, and one that would capture a name put there is renamed: an
  // argument named A is not W(A)'s A.
  const shape = field => {
    const binders = [], bound = new Set();
    let body = field.type, placed = put(field.name, field.type, inside);
    for (let group = 0; body?.kind === "forall" || body?.kind === "binderGroup" && body.binderKind === "forall";
        body = body.body, placed = placed.body, group++) {
      const names = body.kind === "forall" ? [body.name] : body.names;
      const placedNames = placed.kind === "forall" ? [placed.name] : placed.names;
      const domain = body.domain, isCarrier = domain.kind === "name" && domain.name === carrier && !bound.has(carrier);
      if (!isCarrier && freeNames(domain, bound).has(carrier))
        throw module.locate(notPositive(field.name, names[0].text, carrier), d.theory);
      // All names in a group share the domain read before any of them binds.
      for (const name of placedNames) binders.push({ name: name.text, carrier: isCarrier, type: placed.domain, group });
      for (const name of names) bound.add(name.text);
    }
    return { binders, body, bound, placed };
  };

  const constructors = [];
  const operationShapes = [], lawShapes = [];
  for (const field of record.fields) {
    if (field.kind === "sort" || field.kind === "evidence") continue;
    if (field.kind !== "operation" && field.kind !== "law") throw module.locate(unsupportedField(T, field.name), d.theory);
    const { binders, body, bound, placed } = shape(field);
    const params = binders.map(b => ({ name: { text: b.name, ...at }, type: b.type, group: b.group }));
    if (field.kind === "operation") {
      if (!(body.kind === "name" && body.name === carrier && !bound.has(carrier))) throw module.locate(notCarrierValued(field.name, carrier), d.theory);
      operationShapes.push({ name: field.name, binders });
      constructors.push({ kind: "constructor", name: { text: constructor(field.name), ...at }, params, type: null, ...at });
    } else {
      if (!(body.kind === "binary" && body.operator === "=")) throw module.locate(notEquational(field.name), d.theory);
      const uses = [...derived].find(name => freeNames(body, bound).has(name));
      if (uses) throw module.locate(lawUsesDerived(field.name, uses), d.theory);
      lawShapes.push({ name: field.name, binders });
      constructors.push({ kind: "constructor", name: { text: constructor(field.name), ...at }, params, type: placed, ...at });
    }
  }
  // The generated declarations' own binders, apart from every name the
  // declaration writes, its parameters among them, and the theory's fields
  // and their binders: free W(target : U0) folds into a model named target1.
  const taken = new Set([...[...source.slice(d.start, d.end).matchAll(/[A-Za-z_][A-Za-z0-9_]*/g)].map(m => m[0]),
    ...record.fields.map(f => f.name), ...[...operationShapes, ...lawShapes].flatMap(f => f.binders.map(b => b.name))]);
  const fresh = stem => { let name = stem; for (let k = 1; taken.has(name); k++) name = `${stem}${k}`; taken.add(name); return name; };
  const v = Object.fromEntries(["target", "evidence", "g", "x", "i", "a"].map(stem => [stem, fresh(stem)]));
  const xs = Array.from({ length: Math.max(0, ...[...operationShapes, ...lawShapes].map(f => f.binders.length)) }, (_, k) => fresh(`x${k}`));
  if (free) constructors.unshift({ kind: "constructor", name: { text: constructor("gen"), ...at },
    params: [{ name: { text: v.a, ...at }, type: d.on, group: 0 }], type: null, ...at });
  const inductive = { kind: "inductive", name: d.name, params: d.params, result: { modifier: { kind: level, ...at }, universe },
    constructors, ...at, generated: { initial: N } };

  // The model, the recursion and the fold, as source, read where the
  // declaration is.
  const theoryText = text(d.theory), universeText = text(universe), paramsText = names.length
    ? source.slice(d.name.end, d.theory.start).replace(/:\s*$/, "").trim() : "";
  const selfText = names.length ? `${N}(${names.join(", ")})` : N;
  // A call, of no arguments a name alone; a declaration's parameters, then
  // the generated ones; and nested lambdas.
  const call = (fn, args) => args.length ? `${fn}(${args.join(", ")})` : fn;
  const signature = extra => `${names.length ? `${paramsText.replace(/\)$/, "")}, ` : "("}${extra.join(", ")})`;
  const lambdas = (binders, body) => binders.reduceRight((inner, b) => `fun ${b} => ${inner}`, body);
  // A generated declaration's dotted name is a placeholder in its source,
  // which declares no dotted name.
  const own = suffix => `__${N}__${suffix}`;
  const ownModel = call(own("model"), names);
  // A field's arguments, the generated variables.
  const variables = f => xs.slice(0, f.binders.length);
  // The carrier's evidence, the squash's, is the search's: left out, it would
  // be the last argument of a carrier-only theory's make, which no later one
  // gives.
  const model = `def ${own("model")}${paramsText} : ${theoryText} := ${T}.make(${[`${carrier} := ${selfText}`, `${evidence.name} := _`,
    ...[...operationShapes, ...lawShapes].map(f => `${f.name} := ${lambdas(variables(f), call(constructor(f.name), variables(f)))}`)].join(", ")});`;
  const generator = free ? [`${v.g} : (${text(d.on)}) -> ${v.target}.${carrier}`] : [];
  // The recursion at an element, given the target's carrier evidence, and
  // a field's arguments with each in the carrier mapped.
  const recurse = (proof, x) => call(own("fold_map"), [...names, v.target, proof, ...(free ? [v.g] : []), x]);
  const mapped = (proof, f) => f.binders.map((b, k) => b.carrier ? recurse(proof, xs[k]) : xs[k]);
  const clauses = [
    ...(free ? [`${constructor("gen")}(${v.a}) => ${v.g}(${v.a});`] : []),
    ...operationShapes.map(f => `${call(constructor(f.name), variables(f))} => ${call(`${v.target}.${f.name}`, mapped(v.evidence, f))};`),
    ...lawShapes.map(f => `${call(constructor(f.name), variables(f))} @ ${v.i} => ${call(`${v.target}.${f.name}`, mapped(v.evidence, f))} @ ${v.i};`),
  ];
  const foldMap = `def ${own("fold_map")}${signature([`${v.target} : ${theoryText}`,
    `${v.evidence} : ${level === "set" ? "IsSet" : "IsProp"}(${universeText}, ${v.target}.${carrier})`, ...generator, `${v.x} : ${selfText}`])} : ${v.target}.${carrier} := match ${v.x} {
    ${clauses.join("\n    ")}
  };`;
  const targetEvidence = `${v.target}.${evidence.name}`;
  const fold = `def ${own("fold")}${signature([`${v.target} : ${theoryText}`, ...generator])} : ${T}.Hom(${ownModel}, ${v.target}) := ${T}.Hom.make(
    ${[ownModel, v.target, `map := fun ${v.x} => ${recurse(targetEvidence, v.x)}`,
      ...operationShapes.map(f => `map_${f.name} := ${lambdas(variables(f), `refl(${call(`${v.target}.${f.name}`, mapped(targetEvidence, f))})`)}`)].join(", ")});`;
  const dotted = new Map(["model", "fold_map", "fold"].map(suffix => [own(suffix), `${N}.${suffix}`]));
  const generated = renamed(parse(`${model}\n${foldMap}\n${fold}\n`).declarations, dotted);
  return [inductive, ...generated.map(g => ({ ...relocated(g, at), ...(d.uses ? { uses: d.uses } : {}), generated: { initial: N } }))];
}

// A copy with each placeholder name, a token's or a reference's, dotted.
function renamed(node, map) {
  if (Array.isArray(node)) return node.map(item => renamed(item, map));
  if (!node || typeof node !== "object") return node;
  const copy = {};
  for (const [key, value] of Object.entries(node)) copy[key] = renamed(value, map);
  if (typeof copy.text === "string" && map.has(copy.text)) copy.text = map.get(copy.text);
  if (copy.kind === "name" && map.has(copy.name)) copy.name = map.get(copy.name);
  return copy;
}
// Generated source's positions are the declaration's.
function relocated(node, at) {
  if (Array.isArray(node)) return node.map(item => relocated(item, at));
  if (!node || typeof node !== "object") return node;
  const copy = {};
  for (const [key, value] of Object.entries(node))
    copy[key] = ["start", "end"].includes(key) && typeof value === "number" ? at[key]
      : /Start$|End$/.test(key) && typeof value === "number" ? (key.endsWith("Start") ? at.start : at.end) : relocated(value, at);
  return copy;
}

// Why a theory has no initial model here.
const notATheory = (kind, given) => Error(`${kind} takes a theory at its universes and parameters, as ${kind} N : Monoid(U0); ${given} is none.`);
const theoryArguments = (T, wanted, given) => Error(`${T} takes ${wanted} argument${wanted === 1 ? "" : "s"}, its universes and parameters; this gives ${given}.`);
const notOneCarrier = (T, carriers) => Error(`An initial model needs one carrier, not a family; ${T} has ${carriers.length ? carriers.join(", ") : "none"}.`);
const untruncatedCarrier = (T, carrier) => Error(`${T}'s carrier ${carrier} is neither a set nor a proposition: its models have no homomorphisms yet, so it has no initial model here.`);
const notPositive = (field, binder, carrier) => Error(`${field} takes ${binder} with the carrier ${carrier} inside its type: an initial model's operations take the carrier, or types without it.`);
const notCarrierValued = (field, carrier) => Error(`${field} gives no element of the carrier ${carrier}: an initial model's operations do.`);
const notEquational = field => Error(`The law ${field} is no equation: an initial model's laws are equations between its operations' terms.`);
const lawUsesDerived = (field, derived) => Error(`The law ${field} uses the derived operation ${derived}: an initial model's laws use its operations.`);
const unsupportedField = (T, field) => Error(`${T}'s field ${field} is neither an operation nor a law: an initial model has only those.`);
const generatedName = (T, field, N, role, dotted = `${N}.${field}`) => Error(`${T}'s field ${field} would be the constructor ${dotted}, but ${dotted} is ${N}'s ${role}: an initial model's operations and laws are named apart from model, fold_map, fold and squash, and a free model's from gen too.`);
const capturedBy = (field, name) => Error(`${field}'s pattern binds ${name}, which an argument here names: rename it in ${field}.`);
