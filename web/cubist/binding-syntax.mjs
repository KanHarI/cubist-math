// Explicit migration boundary for ordinary binding-aware syntax. Later
// packages move retained theories and goal-dependent blocks through this
// same representation; an unmigrated family is rejected here, not retried
// through nominal capture on failure.
import {scopeMapped, binderName, bindingRole} from "./scopes.mjs";
import {members} from "./references.mjs";
import {sourceOrigin, bindingResolution, SlotOutcomes} from "./bindings.mjs";
import {declarationTelescope, parameterLambdas} from "./telescopes.mjs";

const format = "cubist-bindings-1";
const unmigrated = new Set(["theory", "free", "initial", "select", "use", "useScope", "notationScope", "sectionScope",
  "scoped", "instantiated", "intro", "obtain", "ext", "simpOnly", "withUnfolding", "operatorOf", "notation"]);
const freeze = value => {
  if (!value || typeof value !== "object" || Object.isFrozen(value)) return value;
  for (const child of Object.values(value)) freeze(child);
  return Object.freeze(value);
};
const occurrence = (at, value, spelling, origin) => ({kind: "bindingReference", resolution: value, spelling, origin,
  start: at.start, end: at.end});

export function resolveBindingSyntax(tree, {table, owner, context, source, constructors = []}) {
  constructors = Object.freeze(constructors.map(({id, label, nullary}) => {
    table.get(id);
    if (typeof label !== "string" || typeof nullary !== "boolean") throw new TypeError("Invalid source constructor inventory.");
    return Object.freeze({id, label, nullary});
  }));
  const canonical = tree.kind === "def" ? declarationTelescope(tree) : {tree, inferred: false};
  tree = canonical.tree;
  const owned = [];
  const origin = at => sourceOrigin({...source, start: at.start, end: at.end});
  tree = scopeMapped(tree, {
    deferred: true,
    enter(node, at) {
      if (node.kind === "reference" || node.kind === "bindingReference")
        throw new TypeError("Source resolution cannot accept already resolved syntax.");
      if (unmigrated.has(node.kind)) throw new TypeError(`Binding syntax family has not migrated: ${node.kind}`);
      if (node.kind !== "name" || node.name === "_") return node;
      const {value, fields} = at.qualified(node.name);
      const spelling = fields.length ? node.name.slice(0, -(fields.join(".").length + 1)) : node.name;
      const ref = occurrence(node, value, spelling, origin(node));
      return fields.length ? members(node, {...ref, end: node.start + spelling.length}, fields) : ref;
    },
    bind(token, node, scope, at) {
      if (token.bindingId) throw new TypeError("Source resolution cannot allocate an existing binder twice.");
      if (binderName(token) === "_") return token;
      const record = table.allocate(owner, {role: bindingRole(node, scope, token), label: binderName(token), origin: origin(token)});
      owned.push(record.id);
      return {...token, bindingId: record.id, bindingRole: record.role,
        ...(record.role === "pattern" ? {constructorInventory: constructors, patternEnclosing: at.lookup(binderName(token))} : {})};
    },
    extend(at, binders) {
      for (const token of binders) {
        if (!token.bindingId) continue;
        at = token.bindingRole === "pattern" ? at.defer(binderName(token), token.bindingId)
          : at.bind(binderName(token), bindingResolution(token.bindingId));
      }
      return at;
    },
  }, context);
  return freeze({format, tree, owned, inferred: canonical.inferred});
}

const requireSyntax = syntax => {
  if (syntax?.format !== format || !Array.isArray(syntax.owned)) throw new TypeError("Expected binding-aware syntax.");
};
const mappedResolution = (value, ids) => value.tag === "binding" ? {...value, id: ids.get(value.id) ?? value.id}
  : value.tag === "slot" ? {...value, id: ids.get(value.id) ?? value.id, enclosing: mappedResolution(value.enclosing, ids)} : value;

export function cloneBindingSyntax(syntax, table, owner) {
  requireSyntax(syntax);
  const correspondence = table.freshen(syntax.owned, owner);
  const map = tree => scopeMapped(tree, {
    deferred: true,
    enter: node => node.kind === "bindingReference" ? {...node, resolution: mappedResolution(node.resolution, correspondence),
      ...(node.substitutions ? {substitutions: node.substitutions.map(([id, value]) => [correspondence.get(id) ?? id, map(value)])} : {})} : node,
    bind: token => token.bindingId ? {...token, bindingId: correspondence.get(token.bindingId) ?? token.bindingId,
      ...(token.patternEnclosing ? {patternEnclosing: mappedResolution(token.patternEnclosing, correspondence)} : {})} : token,
    extend: at => at,
  }, null);
  const tree = map(syntax.tree);
  return {syntax: freeze({...syntax, tree, owned: [...correspondence.values()]}), correspondence};
}

// Simultaneous substitution for an explicit open interface. An inserted
// argument keeps its own references; it never passes through source name
// resolution again. Under a pending slot its enclosing alternative may need
// substitution, so retain that argument until the slot's role is known.
export function substituteBindingSyntax(syntax, replacements, table, owner) {
  requireSyntax(syntax);
  const owned = [...syntax.owned];
  for (const [id, replacement] of replacements) {
    table.get(id); requireSyntax(replacement);
    if (owned.includes(id)) throw new TypeError("Substitution requires an open binding, not an owned binder.");
  }
  let insertion = 0;
  const insert = replacement => {
    const {syntax: copy} = cloneBindingSyntax(replacement, table, [...owner, "argument", String(insertion++)]);
    owned.push(...copy.owned);
    return copy.tree;
  };
  const map = tree => scopeMapped(tree, {
    deferred: true,
    enter(node) {
      if (node.kind !== "bindingReference") return node;
      if (node.resolution.tag === "binding" && replacements.has(node.resolution.id)) return insert(replacements.get(node.resolution.id));
      const pending = new Map((node.substitutions ?? []).map(([id, value]) => [id, map(value)]));
      for (let value = node.resolution; value; value = value.tag === "slot" ? value.enclosing : null) {
        if (value.tag === "binding" && !pending.has(value.id) && replacements.has(value.id))
          pending.set(value.id, insert(replacements.get(value.id)));
      }
      return pending.size ? {...node, substitutions: [...pending]} : node;
    },
    extend: at => at,
  }, null);
  return freeze({...syntax, tree: map(syntax.tree), owned});
}

// Entry lowering handles decided references and ordinary binder tokens. A
// candidate pattern's token keeps its spelling for the matched constructor
// table. Its body occurrences keep their slots until resolution time.
export function lowerBindingSyntax(syntax, adapter, outcomes = new SlotOutcomes()) {
  requireSyntax(syntax);
  const tree = scopeMapped(syntax.tree, {
    deferred: true,
    enter: node => node.kind === "bindingReference" ? lowerBindingReference(node, adapter, outcomes, {deferMissing: true}) : node,
    bind: token => token.bindingId && token.bindingRole !== "pattern"
      ? {...token, text: adapter.key(token.bindingId), label: token.label ?? binderName(token)} : token,
    extend: at => at,
  }, null);
  return syntax.inferred ? {...tree, value: parameterLambdas(tree.params, tree.value), valueParameters: tree.params, params: []} : tree;
}

// Structural consumers (for example recursion's fixed-argument checks)
// inspect source nodes before calling term elaboration. Resolve the slots
// decided by this branch there too, through the same adapter. Binders and
// still-pending nested slots are unchanged.
export function lowerBindingReferences(tree,adapter,outcomes=new SlotOutcomes()) {
  return scopeMapped(tree,{
    deferred:true,
    enter:node=>node.kind==="bindingReference"?lowerBindingReference(node,adapter,outcomes,{deferMissing:true}):node,
    extend:at=>at,
  },null);
}

export function lowerBindingReference(node, adapter, outcomes = new SlotOutcomes(), options = {}) {
  const resolved = adapter.resolve(node.resolution, outcomes);
  if (resolved.tag === "binding") {
    const replacement = node.substitutions?.find(([id]) => id === resolved.id)?.[1];
    if (replacement) return lowerBindingSyntax({format, tree: replacement, owned: []}, adapter, outcomes);
  }
  const name = adapter.lower(node.resolution, outcomes, options);
  return name === null ? node : {...node, kind: "name", name};
}
