// module::name (web/reference/first-proof.html#qualified-names): one of a
// module's declarations, by a name nothing in scope shadows, since no
// binder is named with ::. The parser reads it as one token wherever a name
// refers to something and refuses it wherever a name is introduced. A
// binding is the module's own declaration of the name when it is a
// declaration's (a theory's and a generated one's among them) whose origin
// is in the module and whose label is the name: a parameter, a local name
// or a field never is. The environment has each available binding by its
// identity, and each notation and theory by its qualified name.
import {notationBinding,theoryBinding} from "./theories.mjs";
import {bindingResolution,failedResolution} from "../cubist/bindings.mjs";
import {declaredNames} from "./declarations.mjs";

export const qualifiedName = name => /^([A-Za-z_][A-Za-z_0-9]*)::(.+)$/.exec(name);
// A declaration's identity joins its module's name and its own with __, so
// two modules' spellings can meet in one, as a::b__c and a__b::c do in
// a__b__c. The later declaration is refused, whatever either declares.
export const identityCollision = (module, local, holder, key) =>
  Error(`${module}::${local} and ${holder}::${key.slice(holder.length + 2)} would be one identity, ${key}: rename one of them.`);
export const ownedBy = (record, module, local) => record?.role === "declaration"
  && record.origin?.module === module && record.label === local;

// The qualified names a syntax tree writes, as names or as tokens: a
// clause's constructor, a rule's name, a hint.
export function qualifiedNamesIn(syntax) {
  const names = new Set(), visited = new WeakSet();
  const visit = node => {
    if (!node || typeof node !== "object" || visited.has(node)) return;
    visited.add(node);
    for (const text of [node.name, node.text]) if (typeof text === "string" && qualifiedName(text)) names.add(text);
    for (const value of Object.values(node)) visit(value);
  };
  visit(syntax);
  return names;
}

// The available binding the module owns under that label in `env`: the
// compilation's declaration of module__local first, then any other entry
// by identity, as a theory's generated names are.
function ownTerm(env, module, local, { bindings, adapter }) {
  const declaration = bindings.declaration(`${module}__${local}`);
  if (declaration && ownedBy(bindings.table.get(declaration.binding.id), module, local) && env.has(adapter.key(declaration.binding.id)))
    return env.get(adapter.key(declaration.binding.id));
  for (const [key, value] of env)
    if (key.startsWith("\u0000id ") && ownedBy(adapter.bindingForKey(key), module, local)) return value;
  return null;
}

// Each qualified name `syntax` writes, bound in `env` by its own spelling to
// its term where it is available. For a.b.c, the longest prefix the module
// declares is bound, so that a field of a model is read as m.f is. One
// available nowhere is bound to its refusal, so that every reader reports
// it, retained syntax too. Every reader of a name then reads it as it reads
// any name; the term namespace grows by the qualified names a module
// writes, not by its declarations. The notation and theory namespaces,
// which have few entries, have each by its qualified name from its
// declaration (theories.mjs).
export function bindQualifiedNames(env, syntax, options) {
  for (const name of qualifiedNamesIn(syntax)) {
    const [, module, local] = qualifiedName(name), parts = local.split(".");
    if (!env.has(name) || env.get(name)?.tag === "QualifiedFailure") {
      let bound = false;
      for (let length = parts.length; length > 0 && !bound; length--) {
        const prefix = parts.slice(0, length).join("."), value = ownTerm(env, module, prefix, options);
        if (value) {
          env.set(`${module}::${prefix}`, value); bound = true;
          // A refusal of the whole name, from before its prefix was
          // declared, gives way to the prefix's field.
          if (length < parts.length && env.get(name)?.tag === "QualifiedFailure") env.delete(name);
        }
      }
      // A notation alone, as unat::unat, is no refusal.
      if (!bound && !env.has(notationBinding(name)) && !env.has(theoryBinding(name)))
        env.set(name, { tag: "QualifiedFailure", name, message: unknownQualifiedName(name, env, options).message });
    }
  }
}

// A clause's constructor written qualified, unat::succ, as the name its
// type declares it by (one of `names`), where it is a constructor that
// module declares of the type whose kernel name is `binding`, as the
// compilation's `bindings` record its constructors; else as written, which
// no constructor is. No environment entry is read, so that a notation's
// retained body reads alike wherever it is used.
export function constructorText(text, bindings, binding, names) {
  const [, module, local] = qualifiedName(text) ?? [];
  if (!module) return text;
  for (let k = 0, record; (record = bindings.declaration(`${binding}:constructor:${k}`)?.binding); k++)
    if (ownedBy(record, module, local) && names.includes(local)) return local;
  return text;
}

// The names a module's source declares, constructors among them, from its
// items, as prepared syntax holds them too.
export const declaredIn = ast => new Set((ast.items ?? ast.declarations ?? []).filter(d => d.name)
  .flatMap(d => declaredNames(d).map(({ name }) => name)));

// Whether a prefix of `name`, qualified, is available in `env`, as main::m
// of main::m.c: then `name` is a member of it, and one it lacks is refused
// as any name's member is.
export function availablePrefix(name, env) {
  const [, module, local] = qualifiedName(name), parts = local.split(".");
  return parts.slice(1).some((_, k) => {
    const value = env.get(`${module}::${parts.slice(0, k + 1).join(".")}`);
    return value && value.tag !== "QualifiedFailure";
  });
}

// Why `name`, qualified, is available nowhere, with no prefix available
// either: its module declares it, or a prefix of it, below the use; its
// module is not imported; or it declares no such name. The module whose
// scope this is is `current`, whose source declares `declaredHere` and
// imports `imports`; `declares` says whether any available binding is a
// module's.
function unavailable(name, { current, declaredHere = new Set(), imports = new Set(), declares }) {
  const [, module, local] = qualifiedName(name), parts = local.split(".");
  if (module === current && parts.some((_, k) => declaredHere.has(parts.slice(0, k + 1).join("."))))
    return Error(`${name} is declared below its use: a declaration uses only the declarations above it.`);
  if (!(module === current || imports.has(module) || declares(module)))
    return Error(`${name} names a declaration of ${module}, which is not imported here: import ${module};`);
  return Error(`${module} declares no ${local}, so ${name} names nothing.`);
}
const ofModule = (record, module) => ["declaration", "notation"].includes(record?.role) && record.origin?.module === module;
// In a module's environment, whose bindings are keyed by identity.
export const unknownQualifiedName = (name, env, { adapter, ...options }) => unavailable(name, { ...options,
  declares: module => [...env.keys()].some(key => key.startsWith("\u0000id ") && ofModule(adapter.bindingForKey(key), module)) });

// The lexical entries of the qualified names `syntax` writes, for a context
// whose available values `values` holds by identity and whose notation
// inventory is `notations`, as a contextual console entry's: each its
// module's own declaration, the longest prefix the module declares, or,
// unless it names a notation, its refusal (unavailable, whose `current`,
// `declaredHere` and `imports` the context's module gives).
export function qualifiedLexical(syntax, values, table, notations, scope) {
  const declares = name => [...values.keys()].some(id => ofModule(table.get(id), name));
  const entries = [];
  for (const name of qualifiedNamesIn(syntax)) {
    const [, module, local] = qualifiedName(name), parts = local.split(".");
    let found = null;
    for (let length = parts.length; length > 0 && !found; length--) {
      const prefix = parts.slice(0, length).join(".");
      const id = [...values.keys()].find(id => ownedBy(table.get(id), module, prefix));
      if (id) found = [`${module}::${prefix}`, bindingResolution(id)];
    }
    if (found) entries.push(found);
    else if (!notations?.some(entry => entry.name === name))
      entries.push([name, failedResolution({ message: unavailable(name, { ...scope, declares }).message })]);
  }
  return entries;
}
