// Syntax reused outside its declaration keeps the identity of each global.
// These environment keys cannot be written by source or bound by a local.
// Their values are ordinary elaboration entries, still checked by the kernel.
import {rewritten} from "../cubist/scopes.mjs";
import {reference, members} from "../cubist/references.mjs";

const identities = new WeakMap();
const contexts = new WeakMap();
let serial = 0;
export const lexicalBinding = binding => "\u0000binding " + binding.replaceAll(".", "%2E");
const identity = value => value.tag === "DefRef" ? value.name
  : value.binding ?? (value.tag === "InductiveConstructor" ? `${value.inductive.binding}.${value.index}`
    : identities.get(value) ?? identities.set(value, `captured:${++serial}`).get(value));

// Equal selections use one identity within a kernel session. In particular,
// the same notation in a parent and child's parameter type compares alike.
export function lexicalNotation(checker, aliases) {
  const owner = checker.kernel ?? checker;
  const known = contexts.get(owner) ?? contexts.set(owner, new Map()).get(owner);
  const key = JSON.stringify(aliases, (_, value) => value instanceof Map ? [...value]
    : value instanceof Set ? [...value].sort() : value);
  if (!known.has(key)) known.set(key, lexicalBinding(`notation:${++serial}`));
  return known.get(key);
}

export function capturedName(node, env, namespaces = []) {
  const value = env.get(node.name);
  const companions = namespaces.map(key => [key, env.get(key(node.name))]).filter(([, entry]) => entry);
  if (!value && !companions.length) return node;
  const name = lexicalBinding(identity(value ?? companions[0][1]));
  if (value) env.set(name, value);
  for (const [key, entry] of companions) env.set(key(name), entry);
  return reference(name, node.spelling ?? node.name, node);
}

// Resolve qualified declarations as a whole; a model projection retains
// its captured receiver. Local binders, parameters and fields stay syntax.
export function capturedNames(node, env, bound = new Set(), namespaces = []) {
  return rewritten(node, (n, inner) => {
    if (n.kind !== "name" || n.name.startsWith("\u0000")) return n;
    const [root, ...fields] = n.name.split(".");
    const receiver = {...n, name: root, end: n.start + root.length};
    if (inner.has(root)) return fields.length ? members(n, receiver, fields) : n;
    if (env.has(n.name) || namespaces.some(key => env.has(key(n.name)))) return capturedName(n, env, namespaces);
    if (!env.has(root) && !namespaces.some(key => env.has(key(root)))) return n;
    return members(n, capturedName(receiver, env, namespaces), fields);
  }, bound);
}
