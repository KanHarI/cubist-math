// Module-local ownership is independent of the lookup environment: imports
// may be shadowed, but a second local declaration cannot replace the first.
// A generated family reserves its complete set of names before checking any
// member. A reservation is only a name's owner: whether that owner checked is
// the value the name stands for in the environment (`untranslated` below).
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
  constructor() { this.entries = new Map(); }
  reserve(declarations, owner) {
    const proposed = declarations.flatMap(declaration => declaredNames(declaration).map(entry => ({...entry, declaration})));
    const seen = new Map();
    // Inspect the entire request, then claim every still-free name, even
    // on refusal. Those names belong to the failed local declaration, not
    // to an import. A collision never changes an earlier owner.
    let conflict = null;
    for (const entry of proposed) {
      const previous = this.entries.get(entry.name);
      if (previous && previous.owner !== owner || seen.has(entry.name) && seen.get(entry.name) !== entry.declaration)
        conflict ??= entry;
      seen.set(entry.name, entry.declaration);
    }
    for (const entry of proposed) if (!this.entries.has(entry.name)) this.entries.set(entry.name, {...entry, owner});
    return conflict;
  }
  owns(name, owner) { return this.entries.get(name)?.owner === owner; }
}

export const duplicateDeclaration = name => Error(`Duplicate declaration ${name}: a declaration in this module already owns that name.`);

// A failure's root: the declaration that failed on its own, and its reason.
// A failure caused by a failed dependency carries that dependency's root
// (blockedBy, cause), which passes on unchanged; otherwise `binding` is it.
export const failureRoot = (failure, binding) =>
  ({binding: failure.blockedBy ?? binding, reason: failure.cause ?? failure.reason ?? failure.message});

// The value a failed or unpublished name stands for. Every client of it
// reports the same root, however many failed declarations lie between.
export const untranslated = (name, binding, reason, root) =>
  ({tag: "Untranslated", name, binding, reason, blockedBy: root.binding, cause: root.reason});

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
