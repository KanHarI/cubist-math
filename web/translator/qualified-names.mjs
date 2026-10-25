// module::name (web/reference/first-proof.html#qualified-names): one of a
// module's declarations, by a name nothing in scope shadows, since no
// binder is named with ::. The parser reads it as one token wherever a name
// refers to something and refuses it wherever a name is introduced. A
// binding is the module's own declaration of the name when it is a
// declaration's (a theory's and a generated one's among them), or a
// notation's, whose origin is in the module and whose label is the name: a
// parameter, a local name or a field never is. The environment has each
// available binding by its identity.
import {notationBinding} from "./theories.mjs";
import {bindingResolution,failedResolution} from "../cubist/bindings.mjs";

export const qualifiedName = name => /^([A-Za-z_][A-Za-z_0-9]*)::(.+)$/.exec(name);
export const ownedBy = (record, module, local, role = "declaration") => record?.role === role
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
// The module's own notation of that label: the one in scope by it, or,
// where another module's takes the label, any available one, by identity
// too.
function ownNotation(env, module, local, bindings) {
  const own = value => value?.tag === "Notation" && ownedBy(bindings.table.get(value.bindingId), module, local, "notation");
  const plain = env.get(notationBinding(local));
  if (!plain || own(plain)) return plain ?? null;
  for (const value of env.values()) if (own(value)) return value;
  return null;
}

// Each qualified name `syntax` writes, bound in `env` by its own spelling:
// to its term where it is available, and to its notation, looked up again
// each time, as a notation can be declared after its model is first used.
// For a.b.c, the longest prefix the module declares is bound, so that a
// field of a model is read as m.f is. One available nowhere is bound to its
// refusal, so that every reader reports it, retained syntax too. Every
// reader of a name then reads it as it reads any name; the environment
// grows by the qualified names a module writes, not by its declarations.
export function bindQualifiedNames(env, syntax, options) {
  for (const name of qualifiedNamesIn(syntax)) {
    const [, module, local] = qualifiedName(name), parts = local.split(".");
    if (!env.has(name) || env.get(name)?.tag === "QualifiedFailure") {
      let bound = false;
      for (let length = parts.length; length > 0 && !bound; length--) {
        const prefix = parts.slice(0, length).join("."), value = ownTerm(env, module, prefix, options);
        if (value) { env.set(`${module}::${prefix}`, value); bound = true; }
      }
      if (!bound) env.set(name, { tag: "QualifiedFailure", name, message: unknownQualifiedName(name, env, options).message });
    }
    const notation = ownNotation(env, module, local, options.bindings);
    if (notation) env.set(notationBinding(name), notation);
  }
}

// A clause's constructor written qualified, unat::succ, as the name its
// type declares it by (`names`, in order), where `env` has it as a
// constructor of that type, whose binding is `binding`; else as written,
// which no constructor is.
export function constructorText(text, env, binding, names) {
  if (!qualifiedName(text)) return text;
  const value = env.get(text);
  return value?.tag === "InductiveConstructor" && value.inductive?.binding === binding ? names[value.index] ?? text : text;
}

// Why `name`, qualified, is not available in `env`: its module is not
// imported, declares no such name, or declares it below the use. The
// module being translated is `current`, whose source declares the names
// `declaredHere`.
export function unknownQualifiedName(name, env, { current, declaredHere = new Set(), adapter }) {
  const [, module, local] = qualifiedName(name);
  if (module === current && declaredHere.has(local))
    return Error(`${name} is declared below its use: a declaration uses only the declarations above it.`);
  // A notation's identity is in the environment too.
  const imported = module === current || [...env.keys()].some(key => key.startsWith("\u0000id ") && ofModule(adapter.bindingForKey(key), module));
  return refusal(name, imported);
}
const ofModule = (record, module) => ["declaration", "notation"].includes(record?.role) && record.origin?.module === module;
const refusal = (name, imported) => {
  const [, module, local] = qualifiedName(name);
  return imported ? Error(`${module} declares no ${local}, so ${name} names nothing.`)
    : Error(`${name} names a declaration of ${module}, which is not imported here: import ${module};`);
};

// The lexical entries of the qualified names `syntax` writes, for a context
// whose available values `values` holds by identity, as a contextual
// console entry's: each its module's own declaration, the longest prefix
// the module declares, or its refusal.
export function qualifiedLexical(syntax, values, table) {
  const entries = [];
  for (const name of qualifiedNamesIn(syntax)) {
    const [, module, local] = qualifiedName(name), parts = local.split(".");
    let found = null;
    for (let length = parts.length; length > 0 && !found; length--) {
      const prefix = parts.slice(0, length).join(".");
      const id = [...values.keys()].find(id => ownedBy(table.get(id), module, prefix));
      if (id) found = [`${module}::${prefix}`, bindingResolution(id)];
    }
    entries.push(found ?? [name, failedResolution({ message: refusal(name, [...values.keys()].some(id => ofModule(table.get(id), module))).message })]);
  }
  return entries;
}
