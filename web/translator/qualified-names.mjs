// module::name (web/reference/first-proof.html#qualified-names): one of a
// module's declarations, by a name nothing in scope shadows, since no
// binder is named with ::. The compilation knows the declaration by its
// kernel name, module__name, and its binding's owner names the module and
// its label the name; the environment has it under its identity where it is
// available: this module's, above the use, or an imported module's.
import {notationBinding} from "./theories.mjs";

export const qualifiedName = name => /^([A-Za-z_][A-Za-z_0-9]*)::(.+)$/.exec(name);
// A declaration's or a notation's binding, which its module owns.
const owned = (binding, module, local) => ["declarations", "notations"].includes(binding?.owner?.[0])
  && binding.owner[1] === module && binding.label === local;

// Each qualified name `syntax` writes, bound in `env` by its own spelling
// where it is available: to its term, and to its notation where it has one
// (a model's or a notation's own, in the notation namespace). Every reader
// of a name, a call's head, a pattern, a selection or the lexical context of
// retained syntax, then reads it as it reads any name. The environment grows
// by the qualified names a module writes, not by its declarations.
export function bindQualifiedNames(env, syntax, { bindings, adapter }) {
  const visited = new WeakSet(), names = new Set();
  const visit = node => {
    if (!node || typeof node !== "object" || visited.has(node)) return;
    visited.add(node);
    if (node.kind === "name" && node.moduleQualifier) names.add(node.name);
    for (const value of Object.values(node)) visit(value);
  };
  visit(syntax);
  for (const name of names) {
    if (env.has(name)) continue;
    const [, module, local] = qualifiedName(name), declaration = bindings.declaration(`${module}__${local}`);
    if (owned(declaration?.binding, module, local) && env.has(adapter.key(declaration.binding.id)))
      env.set(name, env.get(adapter.key(declaration.binding.id)));
    // The notation of that label in scope, or, where another module's
    // takes the label, the module's own among all in scope.
    const ownNotation = value => value?.tag === "Notation" && owned(bindings.table.get(value.bindingId), module, local);
    const plain = env.get(notationBinding(local));
    const notation = !plain || ownNotation(plain) ? plain
      : [...env].find(([label, value]) => label.startsWith(notationBinding("")) && ownNotation(value))?.[1];
    if (notation) env.set(notationBinding(name), notation);
  }
}

// Why `name`, qualified, is not available in `env`: its module is not
// imported, declares no such name, or declares it below the use. The
// module being translated is `current`, whose source declares the names
// `declaredHere`.
export function unknownQualifiedName(name, env, { current, declaredHere, bindings, adapter }) {
  const [, module, local] = qualifiedName(name);
  if (module === current && declaredHere.has(local))
    return Error(`${name} is declared below its use: a declaration uses only the declarations above it.`);
  const imported = module === current || [...bindings.declarationEntries()].some(([, { binding }]) =>
    binding.owner[0] === "declarations" && binding.owner[1] === module && env.has(adapter.key(binding.id)));
  if (!imported) return Error(`${name} names a declaration of ${module}, which is not imported here: import ${module};`);
  return Error(`${module} declares no ${local}, so ${name} names nothing.`);
}
