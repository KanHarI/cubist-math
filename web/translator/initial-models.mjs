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
// positive operations and equational laws; anything else is refused, naming
// the field. The declared type is checked as any other.
import {theoryBinding} from "./theories.mjs";
import {universeAt} from "../cubist/theories.mjs";
import {parse} from "../cubist/parser.mjs";

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
  if (args.length !== record.universes.length + record.params.length)
    throw module.locate(theoryArguments(T, record.universes.length + record.params.length, args.length), d.theory);
  // The theory's universes and parameters, given.
  const given = new Map([...record.universes.map((_, k) => [universeAt(k), args[k]]),
    ...record.params.map((p, k) => [p.name, args[record.universes.length + k]])]);

  // One carrier, a set or a proposition.
  const carriers = record.fields.filter(f => f.kind === "sort");
  if (carriers.length !== 1 || carriers[0].family) throw module.locate(notOneCarrier(T, carriers.map(f => f.name)), d.theory);
  const carrier = carriers[0].name;
  const evidence = record.fields.find(f => f.kind === "evidence" && f.of === carrier);
  if (!evidence) throw module.locate(untruncatedCarrier(T, carrier), d.theory);
  const level = evidence.evidence === "IsSet" ? "set" : "prop";
  const universe = substituted(carriers[0].type, given);
  const derived = new Set((record.derived ?? []).map(op => op.name));

  // The carrier inside the declared type: N, or W(A) for a free model with
  // parameters.
  const names = d.params.map(p => p.name.text);
  const at = { start: d.start, end: d.end };
  const self = names.length ? { kind: "call", fn: { kind: "name", name: N, ...at }, args: names.map(n => ({ kind: "name", name: n, ...at })), ...at }
    : { kind: "name", name: N, ...at };
  const operations = record.fields.filter(f => f.kind === "operation").map(f => f.name);
  const constructor = name => `${N}.${name}`;
  // A field's binders, each the carrier or a type that does not mention it,
  // and its body.
  const shape = field => {
    const binders = [];
    let body = field.type;
    for (; body?.kind === "forall"; body = body.body) {
      const domain = body.domain;
      if (!(domain.kind === "name" && domain.name === carrier) && mentions(domain, carrier))
        throw module.locate(notPositive(field.name, body.name.text, carrier), d.theory);
      binders.push({ name: body.name.text, carrier: domain.kind === "name" && domain.name === carrier, domain });
    }
    return { binders, body };
  };
  // A field's term inside the declared type: the carrier is N, each
  // operation its constructor, and the theory's universes and parameters
  // as given.
  const inside = node => substituted(node, new Map([...given, [carrier, self],
    ...operations.map(op => [op, { kind: "name", name: constructor(op), ...at }])]));

  const constructors = [];
  if (d.kind === "free") constructors.push({ kind: "constructor", name: { text: constructor("gen"), ...at },
    params: [{ name: { text: "a", ...at }, type: d.on, group: 0 }], type: null, ...at });
  const operationShapes = [], lawShapes = [];
  for (const field of record.fields) {
    if (field.kind === "sort" || field.kind === "evidence") continue;
    if (field.kind !== "operation" && field.kind !== "law") throw module.locate(unsupportedField(T, field.name), d.theory);
    const { binders, body } = shape(field);
    const params = binders.map((b, k) => ({ name: { text: b.name, ...at }, type: b.carrier ? self : inside(b.domain), group: k }));
    if (field.kind === "operation") {
      if (!(body.kind === "name" && body.name === carrier)) throw module.locate(notCarrierValued(field.name, carrier), d.theory);
      operationShapes.push({ name: field.name, binders });
      constructors.push({ kind: "constructor", name: { text: constructor(field.name), ...at }, params, type: null, ...at });
    } else {
      if (!(body.kind === "binary" && body.operator === "=")) throw module.locate(notEquational(field.name), d.theory);
      const uses = [...derived].find(name => mentions(body, name));
      if (uses) throw module.locate(lawUsesDerived(field.name, uses), d.theory);
      lawShapes.push({ name: field.name, binders });
      constructors.push({ kind: "constructor", name: { text: constructor(field.name), ...at }, params, type: inside(body), ...at });
    }
  }
  const inductive = { kind: "inductive", name: d.name, params: d.params, result: { modifier: { kind: level, ...at }, universe },
    constructors, ...at, generated: { initial: N } };

  // The model, the recursion and the fold, as source, read where the
  // declaration is.
  const theoryText = text(d.theory), universeText = text(universe), paramsText = names.length
    ? source.slice(d.name.end, d.theory.start).replace(/:\s*$/, "").trim() : "";
  const applied = names.length ? `(${names.join(", ")})` : "", leading = names.map(n => `${n}, `).join("");
  const selfText = names.length ? `${N}(${names.join(", ")})` : N;
  const lambdas = (binders, body) => binders.reduceRight((inner, b) => `fun ${b.name} => ${inner}`, body);
  // A generated declaration's dotted name is a placeholder in its source,
  // which declares no dotted name.
  const own = suffix => `__${N}__${suffix}`;
  const model = `def ${own("model")}${paramsText} : ${theoryText} := ${T}.make(${carrier} := ${selfText}, ${
    [...operationShapes, ...lawShapes].map(f => `${f.name} := ${lambdas(f.binders, f.binders.length
      ? `${constructor(f.name)}(${f.binders.map(b => b.name).join(", ")})` : constructor(f.name))}`).join(", ")});`;
  const generator = d.kind === "free" ? `, g : ${text(d.on)} -> target.${carrier}` : "";
  function recurse(x) { return `${own("fold_map")}(${leading}target, evidence${d.kind === "free" ? ", g" : ""}, ${x})`; }
  const mapped = (b, k) => b.carrier ? recurse(`x${k}`) : `x${k}`;
  const pattern = (name, binders) => binders.length ? `${constructor(name)}(${binders.map((_, k) => `x${k}`).join(", ")})` : constructor(name);
  const clauses = [
    ...(d.kind === "free" ? [`${constructor("gen")}(a) => g(a);`] : []),
    ...operationShapes.map(f => `${pattern(f.name, f.binders)} => target.${f.name}${f.binders.length ? `(${f.binders.map(mapped).join(", ")})` : ""};`),
    ...lawShapes.map(f => `${pattern(f.name, f.binders)} @ i => target.${f.name}${f.binders.length ? `(${f.binders.map(mapped).join(", ")})` : ""} @ i;`),
  ];
  const foldMap = `def ${own("fold_map")}${names.length ? paramsText.replace(/\)$/, ", ") : "("}target : ${theoryText}, evidence : ${
    level === "set" ? "IsSet" : "IsProp"}(${universeText}, target.${carrier})${generator}, x : ${selfText}) : target.${carrier} := match x {
    ${clauses.join("\n    ")}
  };`;
  const fold = `def ${own("fold")}${names.length ? paramsText.replace(/\)$/, ", ") : "("}target : ${theoryText}${generator}) : ${T}.Hom(${own("model")}${applied}, target) := ${T}.Hom.make(
    ${own("model")}${applied}, target, map := fun x => ${recurse("x").replace("evidence", `target.${evidence.name}`)}, ${
    operationShapes.map(f => `map_${f.name} := ${lambdas(f.binders.map((b, k) => ({ name: `x${k}` })),
      `refl(target.${f.name}${f.binders.length ? `(${f.binders.map(mapped).join(", ").replaceAll("evidence", `target.${evidence.name}`)})` : ""})`)}`).join(", ")});`;
  const dotted = new Map(["model", "fold_map", "fold"].map(suffix => [own(suffix), `${N}.${suffix}`]));
  const generated = renamed(parse(`${model}\n${foldMap}\n${fold}\n`).declarations, dotted);
  return [inductive, ...generated.map(g => ({ ...relocated(g, at), ...(d.uses ? { uses: d.uses } : {}), generated: { initial: N } }))];
}

// A copy of a node with each name the map gives replaced, binders shadowing.
function substituted(node, map, bound = new Set()) {
  if (Array.isArray(node)) return node.map(item => substituted(item, map, bound));
  if (!node || typeof node !== "object") return node;
  if (node.kind === "name" && map.has(node.name) && !bound.has(node.name)) return map.get(node.name);
  const binders = ["forall", "exists", "lambda"].includes(node.kind) && node.name?.text ? [node.name.text] : [];
  const copy = {};
  for (const [key, value] of Object.entries(node))
    copy[key] = substituted(value, map, binders.length && key === "body" ? new Set([...bound, ...binders]) : bound);
  return copy;
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
const mentions = (node, name) => {
  if (Array.isArray(node)) return node.some(item => mentions(item, name));
  if (!node || typeof node !== "object") return false;
  if (node.kind === "name" && node.name === name) return true;
  return Object.values(node).some(value => mentions(value, name));
};
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
