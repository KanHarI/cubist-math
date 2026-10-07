// Patterns on the expected side of evaluate (L2.9a; the proof-ergonomics
// roadmap's computability milestone): `evaluate e expecting p;` where p has
// holes. The evaluated term's normal form, closed and free of assumptions,
// is matched against p part by part:
//   _ matches anything;
//   (p, q) matches a pair whose components match p and q;
//   left(p) and right(p) match a sum's injections;
//   c(p, …), a constructor of the part's declared type, matches c applied to
//     parts that match the p's, each read at its field's type in c's
//     signature, and a constructor written alone, c, matches c with no
//     arguments;
//   typed(T, p) matches what p matches, where T is the part's type;
//   any other expression, as nat.(2 + 3), is elaborated at the part's type
//     and matches a part with the same normal form.
// left, right and typed are the builtins where the module does not bind
// them, as in elaboration, and a builtin's or a constructor's arguments are
// written out as elaboration requires, a hole aside: a hole elsewhere in the
// pattern does not change what any part of it says.
// The pattern is no term, so nothing about it reaches the kernel but the
// expressions elaborated at its leaves; the value is the kernel's.
import {T,substituteTerm} from "./core.mjs";
import {isHole,writtenOut} from "./arguments.mjs";

// Whether an expected value is a pattern: whether a hole is in it.
export function hasHole(node) {
  if (!node || typeof node !== "object") return false;
  if (Array.isArray(node)) return node.some(hasHole);
  if (isHole(node)) return true;
  return Object.entries(node).some(([key, value]) => key !== "start" && key !== "end" && hasHole(value));
}

// A value that does not match a pattern: the part of the value, and the part
// of the pattern it fails; and a hole where no part can be read.
export const valueMismatch = (shown, pattern, part, expected) =>
  Error(`The term evaluates to ${shown}, which does not match ${pattern}: ${part} is not ${expected}.`);
export const holeInExpression = expression =>
  Error(`A hole in an expected value stands for a pair's component, an injection's value or a constructor's argument; ${expression} is none of these, so write it out.`);

// The first part of `value` that does not match `pattern`, as
// { value, pattern }, or null when it matches. `type` is the value's type;
// `elaborate(node, type)` elaborates a leaf at a type and gives its normal
// form, and `source(node)` is a node's text.
export function mismatch(pattern, value, type, scope, elaborate, source) {
  if (isHole(pattern)) return null;
  const fails = { value, pattern };
  const head = scope.nf(type);
  const call = pattern.kind === "call" && pattern.fn?.kind === "name" ? pattern.fn.name
    : pattern.kind === "name" ? pattern.name : null;
  const args = pattern.kind === "call" ? pattern.args : [];
  const builtin = call && !scope.env.has(call) ? call : null;
  if (pattern.kind === "call") writtenOut(pattern, scope, true);
  // typed(T, p) is p, read at T, which is the part's type.
  if (builtin === "typed" && args.length === 2) {
    if (hasHole(args[0])) throw holeInExpression(source(args[0]));
    return scope.equal(elaborate(args[0], null), type) ? mismatch(args[1], value, type, scope, elaborate, source) : fails;
  }
  if (pattern.kind === "pair" && head.tag === "Sigma") {
    if (value.tag !== "Pair") return fails;
    return mismatch(pattern.left, value.first, head.domain, scope, elaborate, source)
      ?? mismatch(pattern.right, value.second, substituteTerm(head.body, head.name, value.first), scope, elaborate, source);
  }
  if ((builtin === "left" || builtin === "right") && args.length === 1 && head.tag === "Sum") {
    if (value.tag !== (builtin === "left" ? "Inl" : "Inr")) return fails;
    return mismatch(args[0], value.value, builtin === "left" ? head.left : head.right, scope, elaborate, source);
  }
  const bound = call && scope.env.get(call);
  if (bound?.tag === "InductiveConstructor" && head.tag === "Sort" && bound.inductive?.binding === head.signature) {
    let constructor = value;
    const parts = [];
    for (; constructor?.tag === "App"; constructor = constructor.fn) parts.unshift(constructor.arg);
    if (constructor?.tag !== "Con" || constructor.index !== bound.index || parts.length !== bound.order.length
      || args.length !== bound.order.length) return fails;
    // The kernel holds a constructor's arguments in its own order. Each is
    // read at its field's type, from the constructor's type at this
    // instance with the arguments before it applied, as elaboration reads
    // it: not at the type its value alone infers, which may be a smaller
    // universe.
    let fn = T.constructor(bound.index, head, bound.source);
    for (const [kernelIndex, sourceIndex] of bound.order.entries()) {
      const field = scope.nf(scope.infer(fn).type).domain;
      const found = mismatch(args[sourceIndex], parts[kernelIndex], field, scope, elaborate, source);
      if (found) return found;
      fn = T.app(fn, parts[kernelIndex]);
    }
    return null;
  }
  if (hasHole(pattern)) throw holeInExpression(source(pattern));
  return scope.equal(value, elaborate(pattern, type)) ? null : fails;
}
