import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { RuntimeQuery } from "../web/cubical-runtime.mjs";
import { Translator } from "../web/translator/translate.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// The fallback per node, W2 of docs/roadmaps/runtime/typed-readback.md
// (section 5): a node the runtime does not execute, a composition, a path
// applied, Glue, unglue, a glue value or a path constructor, is settled by
// the kernel's syntax-only conditions where one holds, and otherwise read
// back as its closure, its weak head asked of the kernel, and the walk goes
// on with that head. A head the runtime cannot interpret is opaque: a frame
// that consumes it rebuilds its node around it, and where it is the value
// asked, the kernel's head queries complete that part's value form. A node
// whose readback reaches a higher-order recursive hypothesis restarts the
// walk on the kernel's queries, as every fallback did before. Each value
// form is the kernel's queries' alone, or more where those stop.
const module = await createCubical();

// Each print of a source, by the runtime and by the kernel's queries alone:
// its outcome, what computed it (the value form's record) and the kernel's
// query steps (ticks) it took.
async function printed(t, source) {
  const run = async runtimeEvaluation => {
    const program = new CubicalProgram(module, sourceReader(), { runtimeEvaluation, collectReferences: false });
    t.after(() => program.dispose());
    const kernel = program.kernel, print = Translator.prototype.printed, ticks = [];
    Translator.prototype.printed = function (...args) {
      const before = kernel.work().querySteps;
      try { return print.apply(this, args); } finally { ticks.push(Number(kernel.work().querySteps - before)); }
    };
    let result;
    try { result = await program.check(source, "main"); } finally { Translator.prototype.printed = print; }
    assert.deepEqual(result.gaps.filter(gap => !gap.directive).map(gap => gap.reason), []);
    return [...result.prints.map(print => [print.start, { text: print.text, by: print.valueForm }]),
      ...result.gaps.filter(gap => gap.directive).map(gap => [gap.declarationStart, { text: `${gap.code}: ${gap.reason.replace(/ at \d+:\d+$/, "")}` }])]
      .sort(([a], [b]) => a - b).map(([, outcome], i) => ({ ...outcome, ticks: ticks[i] }));
  };
  return { runtime: await run(true), kernel: await run(false) };
}
const texts = prints => prints.map(print => print.text);

const unary = `import unat;
use unat;
def count_into(n, total : UNat) : UNat := match n {
  zero => total;
  succ(k) => count_into(k, succ(total));
};
def unit_of(n : UNat) : Unit := match n {
  zero => tt;
  succ(k) => unit_of(k);
};
def id_after(n : UNat) : Unit -> Unit := match n {
  zero => fun (u : Unit) => u;
  succ(k) => id_after(k);
};
`;

// A fallback forces nothing: the node is read back with its parts as the
// walk left them, and the kernel computes only what its rule inspects. A
// composition at a function type is a λ at once, so slow(2 * 255) is never
// computed. The cells the walk forced, in the node's environment or as
// definitions it references outside its term binders, are read back as
// values: expensive, which the kernel stops with K344, is the first
// field's definition cell, tt, in the composition's base.
test("a fallback forces nothing, and reads back what the walk forced as values", async t => {
  const { runtime, kernel } = await printed(t, `${unary}
def slow(n : UNat) : Unit -> Unit := match n {
  zero => fun (u : Unit) => u;
  succ(k) => slow(k);
};
def expensive : Unit := unit_of(count_into(2 * 255, 0));
print(evaluate(comp(fun (i : Interval) => Unit -> Unit, slow(2 * 255))));
print(evaluate(typed(Unit and Unit, (expensive, comp(fun (i : Interval) => Unit, expensive)))));
`);
  assert.deepEqual(texts(runtime), ["<fun>", "(tt, tt)"]);
  assert.deepEqual(texts(kernel), ["<fun>", "K344: Native prototype syntax depth exceeds 512."]);
  const [slow, pair] = runtime;
  // slow is never demanded, nor even copied; one node is asked of the
  // kernel, whose composition rule builds the λ in a few steps.
  assert.deepEqual([slow.by.by, slow.by.fallbacks, slow.by.iota, slow.by.snapshotDefinitions], ["runtime", 1, 0, 0]);
  assert.ok(slow.ticks < 100, `the composition took ${slow.ticks} ticks`);
  // The composition's base is tt, read from the definition cell: the
  // kernel's ticks for it do not include expensive's computation.
  assert.deepEqual([pair.by.by, pair.by.fallbacks], ["runtime", 1]);
  assert.ok(pair.ticks < 100, `the composition took ${pair.ticks} ticks`);
});

// A readback across forcing: the first field's composition reads back the
// suspended x as its closure; the second forces x, the identity after a
// countdown of count_into(2 * 255, 0); and the third's composition reads x
// back from its value, not from the first readback's memo of its closure,
// whose computation the kernel stops with K344. The same holds for x a
// definition, read back first before it has a cell, then demanded and
// forced: the third field takes the forced cell, not the definition's
// handle.
test("a readback after a cell is forced reads its value, not an earlier readback's closure", async t => {
  const { runtime, kernel } = await printed(t, `${unary}
def x_ : Unit -> Unit := id_after(count_into(2 * 255, 0));
print(evaluate((fun (x : Unit -> Unit) => typed((Unit -> Unit) and Unit and Unit,
  (comp(fun (i : Interval) => Unit -> Unit, x), x(tt), comp(fun (i : Interval) => Unit, x(tt)))))(id_after(count_into(2 * 255, 0)))));
print(evaluate(typed((Unit -> Unit) and Unit and Unit, (comp(fun (i : Interval) => Unit -> Unit, x_), x_(tt), comp(fun (i : Interval) => Unit, x_(tt))))));
`);
  assert.deepEqual(texts(runtime), ["(<fun>, tt, tt)", "(<fun>, tt, tt)"]);
  assert.deepEqual(texts(kernel), Array(2).fill("K344: Native prototype syntax depth exceeds 512."));
  // Neither composition computes the countdown, which the kernel's walk
  // stops in after thousands of ticks.
  for (const [i, print] of runtime.entries()) {
    assert.deepEqual([print.by.by, print.by.fallbacks], ["runtime", 2]);
    assert.ok(print.ticks < 1000 && print.ticks < kernel[i].ticks, `the compositions took ${print.ticks} ticks`);
  }
});

// The syntax-only conditions settle a node without the kernel: p @ 0 under
// its Path annotation is the annotation's endpoint, and p, whose
// computation the kernel stops with K344, is neither forced nor read back.
// A composition with a tube on the total face is that tube's end, the tube
// alone read back: here n's value, which the kernel's answer, meeting it
// again, continues with as n's cell, copying nothing of it.
test("a path at an endpoint and a total tube are settled by syntax, reading back only what they keep", async t => {
  const { runtime, kernel } = await printed(t, `${unary}
def slow_path(n : UNat) : tt = tt := match n {
  zero => refl(tt);
  succ(k) => slow_path(k);
};
print(evaluate((fun (p : tt = tt) => p @ 0)(slow_path(count_into(2 * 255, 0)))));
print(evaluate((fun (n : UNat) => typed(UNat and UNat, (n, comp(fun (j : Interval) => UNat, n, face_when(1, fun (j : Interval) => n)))))(2 * 100)));
`);
  assert.deepEqual(texts(runtime), ["tt", "(200, 200)"]);
  assert.deepEqual(texts(kernel), texts(runtime));
  const [endpoint, tube] = runtime;
  assert.deepEqual([endpoint.by.shortcuts, endpoint.by.fallbacks, endpoint.by.iota, endpoint.ticks], [1, 0, 0, 0]);
  assert.deepEqual([tube.by.shortcuts, tube.by.fallbacks], [1, 0]);
  // The program's own syntax, with nothing of the 200 successors the
  // readback built.
  assert.ok(tube.by.snapshotNodes < 200, `the walk copied ${tube.by.snapshotNodes} nodes`);
});

// A higher-order recursive hypothesis (a Lift) is the one value readback
// refuses (3.7). A shortcut that discards it needs no readback, so the
// path applied at 0 shows tt in the runtime; a composition whose base it
// is cannot be read back, and the walk restarts on the kernel's queries,
// which show tt.
test("a discarded higher-order hypothesis needs no restart, and a node whose readback reaches one restarts", async t => {
  const { runtime, kernel } = await printed(t, `
inductive Tree : U0 {
  leaf;
  node(children : Unit -> Tree);
}
def discarded(t : Tree) : Unit := induction t return Unit {
  leaf => tt;
  node(children) with below => ((fun (g : Unit -> Unit) => refl(tt))(below)) @ 0;
};
def rebuilt(t : Tree) : Unit := induction t return Unit {
  leaf => tt;
  node(children) with below => comp(fun (i : Interval) => Unit -> Unit, below)(tt);
};
print(evaluate(discarded(node(fun (u : Unit) => leaf))));
print(evaluate(rebuilt(node(fun (u : Unit) => leaf))));
`);
  assert.deepEqual(texts(runtime), ["tt", "tt"]);
  assert.deepEqual(texts(kernel), texts(runtime));
  const [discarded, rebuilt] = runtime.map(print => print.by);
  assert.deepEqual([discarded.by, discarded.shortcuts, discarded.fallbacks], ["runtime", 1, 0]);
  assert.deepEqual([rebuilt.by, rebuilt.unsupported], ["kernel", "Readback of a higher-order recursive hypothesis is not implemented."]);
});

// A fallback never evaluates under a dimension binder, so no value mentions
// a dimension: in comp^i hold(swapped @ i) [] (tt, 3), with hold(A) the
// composition comp^i U0 [1 ↦ A] A on the same dimension slot, the outer
// family is never forced, and the kernel's substitution, which renames
// the inner binder, computes the transport of (tt, 3) along swapped. An
// unglue whose Glue type mentions a variable is read back with that type
// literal, as weak reads it: with an empty system, through the kernel; on
// the total face, by syntax, as the equivalence's first projection applied
// to the value.
test("two binders on one dimension slot and an unglue over the environment compute as the kernel's queries", async t => {
  const { runtime, kernel } = await printed(t, `import contractible_maps;
import paths_;
import unat;
use unat;
def swap(p : Unit and UNat) := unpack p as (u, n) return UNat and Unit { typed(UNat and Unit, (n, u)); };
def swap_back(p : UNat and Unit) := unpack p as (n, u) return Unit and UNat { typed(Unit and UNat, (u, n)); };
computable def swap_equivalence : Equiv(U0, Unit and UNat, UNat and Unit) {
  exact (swap, swap_back, fun (p : Unit and UNat) => refl(p), fun (q : UNat and Unit) => refl(q),
    fun (p : Unit and UNat) => refl(refl(swap(p))));
}
computable def swapped : (Unit and UNat) = (UNat and Unit) {
  exact ua(U0, Unit and UNat, UNat and Unit, swap_equivalence);
}
def hold(A : U0) : U0 := comp(fun (i : Interval) => U0, A, face_when(1, fun (i : Interval) => A));
print(evaluate(comp(fun (i : Interval) => hold(swapped @ i), typed(Unit and UNat, (tt, 3)))));
print(evaluate((fun (A : U0) => fun (a : A) => unglue(typed(Glue(A), glue(a))))(UNat, 2 + 2)));
print(evaluate((fun (A : U0) => fun (a : A) => unglue(typed(Glue(A, face_when(1, A, id_contr_equiv(U0, A))), a)))(UNat, 2 + 3)));
`);
  assert.deepEqual(texts(runtime), ["(3, tt)", "4", "5"]);
  assert.deepEqual(texts(kernel), texts(runtime));
  const [swappedPair, empty, total] = runtime.map(print => print.by);
  assert.equal(swappedPair.by, "runtime");
  assert.ok(swappedPair.fallbacks > 0);
  assert.deepEqual([empty.by, empty.fallbacks, empty.shortcuts], ["runtime", 1, 0]);
  assert.deepEqual([total.by, total.fallbacks, total.shortcuts], ["runtime", 0, 1]);
});

// An opaque head: the kernel's head of c is a formal composition at the
// circle, which the runtime does not interpret. Asked for itself, the
// kernel's walk completes it, <composition> as it shows one; consumed by
// the circle's eliminator, the elimination is rebuilt around it and sent
// through the fallback, and computes 3, as both clauses do. A glue value
// is opaque too: its value form is the kernel's walk's, glue(2), its base
// computed.
test("an opaque head is completed by the kernel's walk, or rebuilt into the node that consumes it", async t => {
  const { runtime, kernel } = await printed(t, `import contractible_maps;
import unat;
use unat;
inductive Circle : U0 {
  base;
  loop : base = base;
}
def to_nat(c : Circle) : UNat := match c {
  base => 3;
  loop @ i => 3;
};
def c : Circle := transport(fun (x : Circle) => Circle, base, base, loop, base);
def g : Glue(UNat) := glue(1 + 1);
print(evaluate(c));
print(evaluate(to_nat(c)));
print(evaluate(g));
`);
  assert.deepEqual(texts(runtime), ["<composition>", "3", "glue(2)"]);
  assert.deepEqual(texts(kernel), texts(runtime));
  for (const print of runtime) assert.equal(print.by.by, "runtime");
});

// The other readbacks a fallback refuses restart the walk too. A value
// form's query keeps no type value's environment (W1): T is shown first,
// forced to the type A -> A, and the composition's readback reads T's
// cell, whose node mentions A. And a value deeper than the kernel's syntax
// cannot be read back (K344): n, 511, shown first, is the base of a
// composition at UNat.
test("a type value whose environment the value form's query does not keep, or a value past the syntax depth, restarts the walk", async t => {
  const { runtime, kernel } = await printed(t, `import unat;
use unat;
print(evaluate((fun (T : U0) => typed(U0 and U0, (T, comp(fun (i : Interval) => U0, T))))((fun (A : U0) => A -> A)(Unit))));
print(evaluate((fun (n : UNat) => typed(UNat and UNat, (n, comp(fun (j : Interval) => UNat, n))))(succ(2 * 255))));
`);
  assert.equal(texts(runtime)[0], "(<type>, <type>)");
  assert.match(texts(runtime)[1], /^\(succ\(succ\(/);
  assert.deepEqual(texts(kernel), texts(runtime));
  assert.deepEqual(runtime.map(print => [print.by.by, print.by.unsupported]), [
    ["kernel", "Readback of a type value whose environment the query does not keep is not implemented."],
    ["kernel", "Readback of a term past the kernel's syntax depth is not implemented."]]);
});

// A kernel stop in a fallback's head query is reported as the kernel's: in
// euclid(7).1, the search of 70 candidates passes the kernel's syntax depth
// where the kernel computes a transported base, and the value form fails
// with the kernel's K344, as the kernel's queries alone fail.
test("a kernel stop in a fallback is reported as the kernel's", async t => {
  const { runtime, kernel } = await printed(t, "import euclid;\nuse nat;\nprint(evaluate(euclid(7).1));\n");
  assert.deepEqual(texts(runtime), ["K344: Native prototype syntax depth exceeds 512."]);
  assert.deepEqual(texts(kernel), texts(runtime));
});

// No node is asked twice: each term the fallback reads back is asked of
// the kernel's head query once, a head is its own head, and an opaque head
// is never asked again, by the runtime or by the kernel's walk that
// completes it.
test("no node is asked of the kernel twice", async t => {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const kernel = program.kernel, head = kernel.head, asked = [], opaque = [];
  let walking = false;
  kernel.head = function (handle) { if (walking) asked.push(handle); return head.call(this, handle); };
  const valueFormOf = Translator.prototype.valueFormOf, observeNow = RuntimeQuery.prototype.observeNow;
  Translator.prototype.valueFormOf = function (...args) {
    walking = true;
    try { return valueFormOf.apply(this, args); } finally { walking = false; }
  };
  RuntimeQuery.prototype.observeNow = function (...args) {
    const observed = observeNow.apply(this, args);
    if (observed.kind === "Opaque") opaque.push([observed.head, asked.length]);
    return observed;
  };
  let result;
  try {
    result = await program.check(`import euclid;
import contractible_maps;
use nat;
def g : Glue(Nat) := glue(1 + 1);
print(evaluate(euclid(4)));
print(evaluate(g));
`, "main");
  } finally { Object.assign(Translator.prototype, { valueFormOf }); RuntimeQuery.prototype.observeNow = observeNow; kernel.head = head; }
  assert.deepEqual(result.prints.map(print => print.text), ["(5, (tt, <fun>), tt)", "glue(2)"]);
  assert.ok(result.prints.every(print => print.valueForm.by === "runtime" && print.valueForm.fallbacks > 0));
  assert.ok(asked.length > result.prints.reduce((sum, print) => sum + print.valueForm.fallbacks, 0), "the kernel's walk asks heads too");
  assert.equal(new Set(asked).size, asked.length, "a handle asked twice");
  assert.equal(opaque.length, 1);
  const [[glued, at]] = opaque;
  assert.ok(!asked.slice(at).includes(glued), "the opaque head is asked again");
});
