// module::name (web/reference/first-proof.html#qualified-names): one of a
// module's declarations, by a name nothing in scope shadows, since no
// binder is named with ::. The compilation knows the declaration by its
// kernel name, module__name (CompilationBindings), and the environment has
// it under its identity, which no binder shadows either, where it is
// available: this module's, above the use, or an imported module's.
export const qualifiedName = name => /^([A-Za-z_][A-Za-z_0-9]*)::(.+)$/.exec(name);

// The value of `name`, qualified, where `env` is the environment, or null.
export function qualifiedValue(name, env, bindings, adapter) {
  const [, module, local] = qualifiedName(name), declaration = bindings.declaration(`${module}__${local}`);
  const key = declaration && adapter.key(declaration.binding.id);
  return key && env.has(key) ? env.get(key) : null;
}

// Why `name`, qualified, is not available in `env`: its module is not
// imported, declares no such name, or declares it below the use. The
// module being translated is `current`, whose source declares the names
// `declaredHere`.
export function unknownQualifiedName(name, env, { current, declaredHere, bindings, adapter }) {
  const [, module, local] = qualifiedName(name);
  if (module === current && declaredHere.has(local))
    return Error(`${name} is declared below its use: a declaration uses only the declarations above it.`);
  const imported = module === current || [...bindings.declarationEntries()].some(([key, { binding }]) =>
    key.startsWith(`${module}__`) && env.has(adapter.key(binding.id)));
  if (!imported) return Error(`${name} names a declaration of ${module}, which is not imported here: import ${module};`);
  return Error(`${module} declares no ${local}, so ${name} names nothing.`);
}
