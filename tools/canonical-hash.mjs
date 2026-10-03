// Hash checked syntax up to the names of bound variables and dimensions,
// so two checks of one meaning hash alike. tools/proof-migration.mjs compares
// declarations by it, and tools/elaboration-fingerprint.mjs fingerprints
// elaboration with it.
import { createHash } from "node:crypto";

const termBinders = new Set(["Pi", "Lam", "Sigma", "W", "LPi", "LLam"]);
// Which fields a dimension binder scopes, matching the core syntax rules.
const dimensionScope = { Path: ["family"], PLam: ["family", "body"], Comp: ["family", "system"],
  HComp: ["system"], Trans: ["family"] };

// Hash checked syntax up to renaming of bound term variables and dimensions.
// Shared subterms are hashed once for each assignment of their free names, so
// a compact DAG is never expanded into a tree.
export function canonicalHasher({ definitionName = name => name, signatureName = name => name,
  freeVariableName = name => name } = {}) {
  const freeMemo = new WeakMap(), hashMemo = new WeakMap();
  const formulaNames = formula => formula.flat().map(literal => literal.slice(0, -2));
  function free(node) {
    if (!node || typeof node !== "object") return [];
    if (freeMemo.has(node)) return freeMemo.get(node);
    const names = new Set();
    const add = (values, except = null) => { for (const name of values) if (name !== except) names.add(name); };
    if (Array.isArray(node)) node.forEach(child => add(free(child)));
    else if (node.tag === "Var") names.add(`t:${node.name}`);
    else for (const [key, value] of Object.entries(node)) {
      // face and arg hold interval formulas, except App.arg, which is a term.
      if ((key === "face" || key === "arg") && Array.isArray(value)) { add(formulaNames(value).map(name => `d:${name}`)); continue; }
      if (!value || typeof value !== "object") continue;
      let except = null;
      if (termBinders.has(node.tag) && key === "body") except = `t:${node.name}`;
      if (dimensionScope[node.tag]?.includes(key)) except = `d:${node.dim}`;
      add(free(value), except);
    }
    const result = [...names].sort();
    freeMemo.set(node, result);
    return result;
  }
  // scope maps each bound name to the depth of its binder. A bound name is
  // hashed as its distance to that binder (a de Bruijn index), so a subterm's
  // hash depends only on the subterm and the indices of its free names.
  function hash(node, scope, depth) {
    if (node === null || typeof node !== "object") return JSON.stringify(node ?? null);
    const index = name => scope.has(name) ? `#${depth - 1 - scope.get(name)}` : null;
    const names = free(node), key = names.map(name => index(name) ?? name).join("\u0000");
    let byScope = hashMemo.get(node);
    if (!byScope) hashMemo.set(node, byScope = new Map());
    if (byScope.has(key)) return byScope.get(key);
    const digest = createHash("sha1");
    const inner = name => new Map(scope).set(name, depth);
    if (Array.isArray(node)) {
      digest.update("[");
      for (const child of node) digest.update(hash(child, scope, depth) + ",");
    } else {
      digest.update(node.tag ?? "{");
      for (const fieldName of Object.keys(node).sort()) {
        const value = node[fieldName];
        if (fieldName === "tag") continue;
        // Con.name is display metadata. Constructor identity is its index
        // in a sort whose admitted schema also compares constructor names.
        if ((termBinders.has(node.tag) && fieldName === "name") || (dimensionScope[node.tag] && fieldName === "dim")
          || node.tag === "Con" && fieldName === "name") continue;
        digest.update(`|${fieldName}=`);
        if (node.tag === "Var" && fieldName === "name") digest.update(index(`t:${value}`) ?? `free:${freeVariableName(value)}`);
        else if (node.tag === "DefRef" && fieldName === "name") digest.update(definitionName(value));
        else if ((node.tag === "Sort" || node.tag === "Elim") && fieldName === "signature") digest.update(signatureName(value));
        else if ((fieldName === "face" || fieldName === "arg") && Array.isArray(value))
          digest.update(JSON.stringify(value.map(clause => clause.map(literal => {
            const name = literal.slice(0, -2);
            return `${index(`d:${name}`) ?? `free:${name}`}${literal.slice(-2)}`;
          }).sort()).sort()));
        else if (value && typeof value === "object") {
          let childScope = scope, childDepth = depth;
          if (termBinders.has(node.tag) && fieldName === "body") { childScope = inner(`t:${node.name}`); childDepth++; }
          if (dimensionScope[node.tag]?.includes(fieldName)) { childScope = inner(`d:${node.dim}`); childDepth++; }
          digest.update(hash(value, childScope, childDepth));
        } else digest.update(JSON.stringify(value));
      }
    }
    const result = digest.digest("hex");
    byScope.set(key, result);
    return result;
  }
  return term => hash(term, new Map(), 0);
}
