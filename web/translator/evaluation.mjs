// Patterns on the expected side of evaluate (L2.9a), with demand marks
// (EVAL5; docs/roadmaps/runtime/evaluation-demand-marks.md):
// `evaluate e expecting p;` where p has holes or marks. The evaluated term,
// closed and free of assumptions, is matched against p part by part, and
// each part is computed only as far as p observes it:
//   _ matches anything and computes nothing;
//   !p computes the part's weak head, then matches p;
//   !!p computes the part's full normal form, then matches p against it;
//   (p, q) matches a pair whose components match p and q;
//   left(p) and right(p) match a sum's injections;
//   c(p, …), a constructor of the part's declared type, matches c applied to
//     parts that match the p's, each read at its field's type in c's
//     signature, and a constructor written alone, c, matches c with no
//     arguments;
//   typed(T, p) matches what p matches, where T is the part's type,
//     compared by their weak heads, part by part, then by conversion;
//   any other expression, as nat.(2 + 3), is elaborated at the part's type
//     and matches a part with the same normal form.
// A pair, an injection and a constructor compute the part's weak head and
// read it; an expression computes the part's full normal form. A part is
// read by its type, never by its weak head's kind: after eta a function's
// weak head can be a constructor. A bare `_` would compute nothing, and is
// refused where the whole value is expected (translate.mjs).
// left, right and typed are the builtins, reserved names no module binds,
// and a builtin's or a constructor's arguments are written out as
// elaboration requires, a hole aside: a hole elsewhere in the pattern does
// not change what any part of it says.
// The pattern is no term, so nothing about it reaches the kernel but the
// queries its marks and parts ask and the expressions elaborated at its
// leaves; the value is the kernel's.
import {T,substituteTerm} from "./core.mjs";
import {isHole,writtenOut} from "./arguments.mjs";

const within = (node, found) => {
  if (!node || typeof node !== "object") return false;
  if (Array.isArray(node)) return node.some(item => within(item, found));
  if (found(node)) return true;
  return Object.entries(node).some(([key, value]) => key !== "start" && key !== "end" && within(value, found));
};
// Whether an expected value is a pattern: whether a hole or a demand mark is
// in it. One that is neither is compared whole, as an expression.
export const hasHole = node => within(node, isHole);
export const hasMark = node => within(node, item => item.kind === "demand");
export const isPattern = node => hasHole(node) || hasMark(node);

// A marker in a shown value: a part evaluation did not compute, or one
// whose weak head it computed and does not show (cubical-source-text.mjs).
export const marker = text => ({ tag: "Marker", text });
const unevaluated = marker("<unevaluated>");

// A value that does not match a pattern: the part of the value, and the part
// of the pattern it fails; and a hole or a mark where no part can be read.
export const valueMismatch = (shown, pattern, part, expected) =>
  Error(`The term evaluates to ${shown}, which does not match ${pattern}: ${part} is not ${expected}.`);
export const typedMismatch = (shown, pattern, type, expected) =>
  Error(`The term evaluates to ${shown}, which does not match ${pattern}: a part of type ${type} is not ${expected}.`);
export const holeInExpression = expression =>
  Error(`A hole in an expected value stands for a pair's component, an injection's value or a constructor's argument; ${expression} is none of these, so write it out.`);
export const markInExpression = expression =>
  Error(`A demand mark, ! or !!, starts a part of an expected value: the whole value, a pair's component, an injection's value or a constructor's argument; ${expression} is none of these.`);
export const bareHole = () =>
  Error("evaluate e expecting _; would compute nothing: write !_ to compute the value's weak head, or !!_ for its full normal form.");

// A hole or a mark where no part can be read: a mark is refused first, as
// writing the term for a hole would not make its place one.
const misplaced = (pattern, source) => (hasMark(pattern) ? markInExpression : holeInExpression)(source(pattern));

// Whether a typed pattern's annotation is the part's type. Types that differ
// in their weak heads, compared part by part, differ: a failed conversion
// would decide that only after normalizing both, computing parts of the
// type, as a dependent pair's ignored component, that the pattern leaves
// unobserved. Types the comparison cannot tell apart, as where eta or a
// cubical construction relates them, are compared by conversion.
const sameType = (annotation, type, scope) => !scope.differ(annotation, type) && scope.equal(annotation, type);

// The first part of the normal form `value` that does not match `pattern`,
// as { value, pattern }, or null when it matches: a pattern under `!!`,
// whose marks change nothing. `type` is the value's type, and `at` gives
// elaborate, annotation and source, as observe takes them. A failure is
// located at the part of the pattern that met it.
export function mismatch(pattern, value, type, scope, at) {
  try { return mismatched(pattern, value, type, scope, at); }
  catch (error) { throw scope.unit.locate(error, pattern); }
}
function mismatched(pattern, value, type, scope, at) {
  if (isHole(pattern)) return null;
  if (pattern.kind === "demand") return mismatch(pattern.value, value, type, scope, at);
  const fails = { value, pattern };
  const head = scope.nf(type);
  const call = pattern.kind === "call" && pattern.fn?.kind === "name" ? pattern.fn.name
    : pattern.kind === "name" ? pattern.name : null;
  const args = pattern.kind === "call" ? pattern.args : [];
  const builtin = call && !scope.env.has(call) ? call : null;
  if (pattern.kind === "call") writtenOut(pattern, scope, true);
  // typed(T, p) is p, read at T, which is the part's type.
  if (builtin === "typed" && args.length === 2) {
    if (isPattern(args[0])) throw misplaced(args[0], at.source);
    return sameType(at.annotation(args[0]), type, scope) ? mismatch(args[1], value, type, scope, at) : { ...fails, type };
  }
  if (pattern.kind === "pair" && head.tag === "Sigma") {
    if (value.tag !== "Pair") return fails;
    return mismatch(pattern.left, value.first, head.domain, scope, at)
      ?? mismatch(pattern.right, value.second, substituteTerm(head.body, head.name, value.first), scope, at);
  }
  if ((builtin === "left" || builtin === "right") && args.length === 1 && head.tag === "Sum") {
    if (value.tag !== (builtin === "left" ? "Inl" : "Inr")) return fails;
    return mismatch(args[0], value.value, builtin === "left" ? head.left : head.right, scope, at);
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
      const found = mismatch(args[sourceIndex], parts[kernelIndex], field, scope, at);
      if (found) return found;
      fn = T.app(fn, parts[kernelIndex]);
    }
    return null;
  }
  if (isPattern(pattern)) throw misplaced(pattern, at.source);
  return scope.equal(value, at.elaborate(pattern, type)) ? null : fails;
}

// The kinds of weak head a value can stop at, as a shown value marks them.
// An eliminator not applied to a value is a function: eta makes
// fun (n : UNat) => induction n … one.
const typeKinds = new Set(["U", "Pi", "Sigma", "Path", "Sum", "Unit", "Void", "Glue", "Sort", "LPi"]);
const headMarker = kind => marker(kind === "Lam" || kind === "Elim" ? "<fun>" : kind === "PLam" ? "<path>" : kind === "LLam" ? "<level fun>"
  : typeKinds.has(kind) ? "<type>" : ["Comp", "HComp", "Trans"].includes(kind) ? "<composition>" : "<neutral>");
// A value as far as it was computed: a weak head with its parts shown as
// `parts(index, handle, below)` gives them, by their places and handles,
// from the left; `below` is how many levels under the head's own a part is
// shown (a constructor's first argument is under every application). A head
// that is no constructor, pair, injection or tt is shown by its marker.
function shownHead(head, at, parts = () => unevaluated) {
  const { root, args } = at.spine(head);
  if (root.kind === "Con") return args.reduce((fn, arg, index) => T.app(fn, parts(index, arg, args.length - index)), at.constructor(root.id));
  if (args.length) return marker("<neutral>");
  if (root.kind === "Pair") { const first = parts(0, root.children[1], 1); return { tag: "Pair", first, second: parts(1, root.children[2], 1) }; }
  if (root.kind === "Inl" || root.kind === "Inr") return { tag: root.kind, value: parts(0, root.children[1], 1) };
  if (root.kind === "Point") return { tag: "Point" };
  return headMarker(root.kind);
}
const once = compute => { let done = false, value; return () => done ? value : (done = true, value = compute()); };

// The value form of a term (DM3): its weak head, and the value forms of the
// parts of a constructor, a pair or an injection, from the left; any other
// head is shown by its marker. A printer shows at most `budget` nodes, so
// the walk computes at most that many heads; and it shows nothing deeper
// than the kernel's own syntax, `depth` levels (K344), which is as deep as
// any printer is given a term. A part past either is shown as …,
// uncomputed. The walk keeps its own stack, as a value's parts can nest
// deeper than JavaScript's. `at` is as observe takes it; `node`, the source
// a failure is located at.
export function valueForm(handle, at, node, budget = 4000, depth = 512) {
  const value = {}, pending = [[handle, value, 1]];
  while (pending.length) {
    const [part, place, level] = pending.pop(), parts = [];
    if (budget-- <= 0 || level > depth) { Object.assign(place, marker("…")); continue; }
    Object.assign(place, shownHead(at.head(part, node), at, (_, inner, below) => {
      const shown = {};
      parts.push([inner, shown, level + below]);
      return shown;
    }));
    // The leftmost part is computed first.
    pending.push(...parts.reverse());
  }
  return value;
}

// Match a part on demand: `handle` is the part's kernel term, which only the
// pattern's demands compute, `type()` gives its type, and `head`, when
// known, its weak head. The result is { shown, failed }: the part as far as
// it was computed, with markers for the rest, and the first failure, as
// { shown, pattern } for a value that does not match or { type, pattern }
// for a part of another type, or none. `at` asks the kernel:
//   head(handle, node), normal(handle, node): a weak head, a normal form
//     decoded, each a query for the pattern node `node`, which a failure
//     names;
//   spine(handle), decoded(handle): a term as the kernel holds it, nothing
//     computed; constructor(handle), a constructor as a display shows it,
//     without its type's parameters;
//   elaborate(node, type): a leaf elaborated at a type, and its normal form;
//   annotation(node): a typed pattern's type, elaborated and checked, and
//     not normalized: sameType compares it with the part's type;
//   source(node): a node's text;
//   locate(error, node): the error, located at the pattern node whose
//     demand failed, unless a part inside it already located it.
export function observe(pattern, handle, type, scope, at, head = null) {
  try { return observed(pattern, handle, type, scope, at, head); }
  catch (error) { throw at.locate(error, pattern); }
}
function observed(pattern, handle, type, scope, at, head) {
  if (isHole(pattern)) return { shown: head === null ? unevaluated : shownHead(head, at) };
  if (pattern.kind === "demand") {
    if (pattern.mark === "!") return observe(pattern.value, handle, type, scope, at, head ?? at.head(handle, pattern));
    const normal = at.normal(handle, pattern);
    const found = isHole(pattern.value) ? null : mismatch(pattern.value, normal, type(), scope, at);
    return { shown: normal, failed: found && (found.type ? { type: found.type, pattern: found.pattern } : { shown: found.value, pattern: found.pattern }) };
  }
  const call = pattern.kind === "call" && pattern.fn?.kind === "name" ? pattern.fn.name
    : pattern.kind === "name" ? pattern.name : null;
  const args = pattern.kind === "call" ? pattern.args : [];
  const builtin = call && !scope.env.has(call) ? call : null;
  if (pattern.kind === "call") writtenOut(pattern, scope, true);
  // typed(T, p) is p, read at T, which is the part's type.
  if (builtin === "typed" && args.length === 2) {
    if (isPattern(args[0])) throw misplaced(args[0], at.source);
    if (!sameType(at.annotation(args[0]), type(), scope))
      return { shown: head === null ? unevaluated : shownHead(head, at), failed: { type: type(), pattern } };
    return observe(args[1], handle, type, scope, at, head);
  }
  // The part's weak head, read; a value of another shape fails the pattern.
  const read = () => {
    head ??= at.head(handle, pattern);
    return at.spine(head);
  };
  const differs = () => { const shown = shownHead(head, at); return { shown, failed: { shown, pattern } }; };
  const typeHead = pattern.kind === "pair" || builtin === "left" || builtin === "right" || scope.env.get(call)?.tag === "InductiveConstructor"
    ? scope.nf(type()) : null;
  if (pattern.kind === "pair" && typeHead.tag === "Sigma") {
    const { root, args: applied } = read();
    if (root.kind !== "Pair" || applied.length) return differs();
    const [, first, second] = root.children;
    const left = observe(pattern.left, first, () => typeHead.domain, scope, at);
    if (left.failed) return { shown: { tag: "Pair", first: left.shown, second: unevaluated }, failed: left.failed };
    const right = observe(pattern.right, second, once(() => substituteTerm(typeHead.body, typeHead.name, at.decoded(first))), scope, at);
    return { shown: { tag: "Pair", first: left.shown, second: right.shown }, failed: right.failed };
  }
  if ((builtin === "left" || builtin === "right") && args.length === 1 && typeHead.tag === "Sum") {
    const { root, args: applied } = read();
    if (root.kind !== (builtin === "left" ? "Inl" : "Inr") || applied.length) return differs();
    const inner = observe(args[0], root.children[1], () => builtin === "left" ? typeHead.left : typeHead.right, scope, at);
    return { shown: { tag: root.kind, value: inner.shown }, failed: inner.failed };
  }
  const bound = call && scope.env.get(call);
  if (bound?.tag === "InductiveConstructor" && typeHead.tag === "Sort" && bound.inductive?.binding === typeHead.signature) {
    const { root, args: parts } = read();
    if (root.kind !== "Con" || root.payload !== bound.index || parts.length !== bound.order.length
      || args.length !== bound.order.length) return differs();
    // The kernel holds a constructor's arguments in its own order. Each is
    // read at its field's type: the constructor's type at this instance,
    // instantiated with the arguments before it as the kernel holds them,
    // computed only as far as a field's pattern reads its type.
    const shown = [];
    const result = failed => ({ shown: shownHead(head, at, index => shown[index] ?? unevaluated), failed });
    let fnType = once(() => scope.infer(T.constructor(bound.index, typeHead, bound.source)).type);
    for (const [kernelIndex, sourceIndex] of bound.order.entries()) {
      const before = fnType, pi = once(() => scope.nf(before())), part = parts[kernelIndex];
      const found = observe(args[sourceIndex], part, () => pi().domain, scope, at);
      shown[kernelIndex] = found.shown;
      if (found.failed) return result(found.failed);
      fnType = once(() => substituteTerm(pi().body, pi().name, at.decoded(part)));
    }
    return result(null);
  }
  if (isPattern(pattern)) throw misplaced(pattern, at.source);
  // An expression: elaborated first, so that one in error computes nothing.
  const expected = at.elaborate(pattern, type()), normal = at.normal(handle, pattern);
  return { shown: normal, failed: scope.equal(normal, expected) ? null : { shown: normal, pattern } };
}

// A closed truncation's witness (L2.9b): its normal form is a truncated
// declared type's constructor, other than the squash, perhaps under formal
// compositions, whose bases are read. The witness is that constructor's
// argument, or the constructor applied where it has several; the kernel
// gives its type. Under a composition whose type changes along it, the base
// is of the type at its start, which is refused, so that the witness is of
// the truncated type's own parameter. No eliminator out of the truncation is
// defined: this reads a closed value. `show` displays a term.
export function witnessOf(normal, type, scope, show) {
  const head = scope.nf(type);
  const record = head.tag === "Sort" ? scope.checker.kernel?.signatures.get(head.signature) : null;
  const info = record && scope.checker.kernel.signature(record.index);
  if (!info?.modifier) throw notTruncated(show(type));
  let value = normal;
  while (["Comp", "HComp", "Trans"].includes(value?.tag)) value = value.base;
  let constructor = value;
  const parts = [];
  for (; constructor?.tag === "App"; constructor = constructor.fn) parts.unshift(constructor.arg);
  if (constructor?.tag !== "Con" || info.constructors[constructor.index]?.generated) throw noWitness(show(normal));
  // The kernel checks the constructor's value at the truncation's type: a
  // base built in another type is refused. Its own inferred type is not
  // compared, as it may lie in a smaller universe and still be accepted:
  // point(tt) infers Trunc(U0, Unit) for a Trunc(U1, A) with A := Unit.
  if (!scope.accepts(value, type)) throw transportedWitness(show(scope.infer(value).type), show(type));
  const witness = parts.length === 1 ? parts[0] : value;
  // A truncation of one type, as Trunc(U, A), states the witness's type as
  // written, A, once the kernel accepts the witness at it.
  const stated = type.tag === "Sort" && type.parameters?.length === 1 && parts.length === 1 ? type.parameters[0] : null;
  return { witness, type: stated && scope.accepts(witness, stated) ? stated : scope.infer(witness).type };
}

export const notTruncated = type =>
  Error(`witness reads a closed truncation, a value of a truncated declared type such as Trunc(U, A); this is a value of ${type}.`);
export const noWitness = normal =>
  Error(`The truncation evaluates to ${normal}, which holds no constructor to read a witness from.`);
export const transportedWitness = (built, type) =>
  Error(`The truncation's witness lies under a composition whose type changes: it is built in ${built}, not ${type}.`);

