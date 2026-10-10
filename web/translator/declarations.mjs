// Module-local ownership is independent of the lookup environment: imports
// may be shadowed, but a second local declaration cannot replace the first.
// A generated family reserves its complete set of names before checking any
// member. Checking and publication state belong to these identities too.
export function declaredNames(declaration) {
  const names = [{name: declaration.name.text, at: declaration.name, kind: declaration.kind}];
  if (declaration.kind === "inductive") {
    for (const constructor of declaration.constructors)
      names.push({name: constructor.name.text, at: constructor.name, kind: "constructor"});
    if (declaration.result?.modifier && declaration.result.modifier.kind !== "type")
      names.push({name: `${declaration.name.text}.squash`, at: declaration.name, kind: "constructor"});
  }
  return names;
}

export class DeclarationOwnership {
  constructor(module) { this.module = module; this.entries = new Map(); }
  reserve(declarations, owner) {
    const proposed = declarations.flatMap(declaration => declaredNames(declaration).map(entry => ({...entry, declaration})));
    const seen = new Map();
    // First inspect the entire request: a late collision must not reserve a
    // prefix of a refused expansion, or alter an earlier declaration's state.
    for (const entry of proposed) {
      const previous = this.entries.get(entry.name);
      if (previous && previous.owner !== owner || seen.has(entry.name) && seen.get(entry.name) !== entry.declaration) return entry;
      seen.set(entry.name, entry.declaration);
    }
    for (const entry of proposed) if (!this.entries.has(entry.name))
      this.entries.set(entry.name, {...entry, module: this.module, owner,
        identity: `${this.module}__${entry.name}`, state: "reserved"});
    return null;
  }
  finish(declaration, result) {
    for (const {name} of declaredNames(declaration)) {
      const entry = this.entries.get(name);
      if (entry) Object.assign(entry, {state: result.status === "not-translated" ? "failed" : "checked",
        cause: result.status === "not-translated" ? result.reason : null});
    }
  }
}

export const duplicateDeclaration = name => Error(`Duplicate declaration ${name}: a declaration in this module already owns that name.`);

// Generator-assigned family roles, never dotted-name heuristics, determine
// the publication boundary. A base theory (including parent projections)
// remains usable if an optional derived operation or morphism family fails.
export function publicationGroups(owner, declarations) {
  const families = new Map();
  for (const declaration of declarations) {
    const family = declaration.generated.initial ? "initial" : declaration.generated.family;
    if (!family) throw new TypeError("Missing publication family");
    if (!families.has(family)) families.set(family, []);
    families.get(family).push(declaration);
  }
  const groups = [...families].map(([family, members]) => ({
    id: `${owner.name.text}:${family}`, owner: owner.name.text, family, members,
    head: members[0], state: "reserved", dependencies: [],
  }));
  const base = groups.find(group => group.family === "base");
  const hom = groups.find(group => group.family === "hom");
  for (const group of groups) {
    if (base && group !== base) group.dependencies.push(base);
    if (group.family === "iso" && hom) group.dependencies.push(hom);
  }
  return groups;
}

export function restoreMap(target, snapshot) {
  target.clear(); for (const [key, value] of snapshot) target.set(key, value);
}
