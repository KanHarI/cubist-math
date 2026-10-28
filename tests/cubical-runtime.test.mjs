import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { CubicalDeclarationTransaction } from "../web/cubical-transaction.mjs";
import { RuntimeQuery, RuntimeError } from "../web/cubical-runtime.mjs";
import { checkProgram } from "./check-program.mjs";
import { budget } from "./timing.mjs";

async function setup(t, source) {
  const { program, result } = await checkProgram(t, source, { options: { collectReferences: false } });
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const kernel = program.kernel, graph = new InstructionGraph(kernel);
  const query = (name, options) => {
    const reference = kernel.definitions.get(`main__${name}`);
    assert.ok(reference, `missing ${name}`);
    const runtime = new RuntimeQuery(kernel, graph.lookup(reference), options);
    t.after(() => runtime.dispose());
    return runtime;
  };
  const normal = name => graph.judgement(graph.step(graph.refl(graph.lookup(
    kernel.definitions.get(`main__${name}`))), "other", [], "normalize")).other;
  return { program, kernel, graph, query, normal };
}
const fails = kind => error => error instanceof RuntimeError && error.kind === kind;

function nativeUnary(kernel, signature, handle) {
  for (let n = 0; n < 1000; n++) {
    const value = kernel.node(handle);
    if (value.kind === "Con") {
      assert.equal(value.payload, 0);
      assert.equal(kernel.node(value.children[0]).payload, signature);
      return n;
    }
    assert.equal(value.kind, "App");
    const constructor = kernel.node(value.children[0]);
    assert.equal(constructor.kind, "Con"); assert.equal(constructor.payload, 1);
    assert.equal(kernel.node(constructor.children[0]).payload, signature);
    handle = value.children[1];
  }
  throw new Error("Native unary test output exceeded its bound.");
}

async function unary(query, signature, handle = query.root) {
  for (let n = 0; n < 1000; n++) {
    const value = await query.observe(handle);
    assert.equal(value.kind, "Con"); assert.equal(value.signature, signature);
    if (value.index === 0) { assert.equal(value.args.length, 0); return n; }
    assert.equal(value.index, 1); assert.equal(value.args.length, 1);
    handle = value.args[0];
  }
  throw new Error("Unary test output exceeded its bound.");
}

test("only existing, closed typing judgements enter the runtime", async t => {
  const kernel = new CubicalKernel(await createCubical()), g = new InstructionGraph(kernel);
  t.after(() => kernel.dispose());
  const point = g.point(), unit = g.unit(), entry = g.extend(unit, "assumption");
  const open = g.variable(entry);
  for (const judgement of [0, -1, 1.5, g.count, g.refl(point), open])
    assert.throws(() => new RuntimeQuery(kernel, judgement), fails("input"));
  // The resulting Point has no free variable, but its judgement still has
  // the unused premise in context. Lazy execution must not erase assumptions.
  const ignored = g.apply(g.lambda(g.extend(unit, "unused"), point), open);
  assert.equal(kernel.node(g.judgement(ignored).term).kind, "App");
  assert.throws(() => new RuntimeQuery(kernel, ignored), fails("input"));
  const query = new RuntimeQuery(kernel, point);
  t.after(() => query.dispose());
  assert.deepEqual(await query.observe(), { kind: "Point" });
});

test("closures preserve capture and shadowing and do not force unused cubical arguments", async t => {
  const { query, kernel, normal } = await setup(t, `
inductive Flag { disabled; enabled; }
def capture : Flag := (fun (x : Flag) =>
  (fun (f : Flag -> Flag) => (fun (x : Flag) => f(x))(disabled))
    (fun (y : Flag) => x))(enabled);
def unused : Unit := (fun (p : tt = tt) => tt)(refl(tt));
`);
  const captured = await query("capture").observe();
  assert.equal(captured.signature, kernel.signatures.get("main__Flag").index);
  assert.equal(captured.index, 1);
  assert.equal(kernel.node(normal("capture")).payload, captured.index);
  assert.deepEqual(await query("unused").observe(), { kind: "Point" });
  assert.equal(kernel.node(normal("unused")).kind, "Point");
});

test("level application, sums and Unit elimination agree with native full normalization", async t => {
  const { query, kernel, normal } = await setup(t, `
def identity(U < UU0, A : U, x : A) : A := x;
def polymorphic : Unit := identity(U0, Unit, tt);
def branch(s : Unit or Unit) : Unit := match s return Unit { left x => x; right y => y; };
def left_value : Unit := branch(left(tt));
def right_value : Unit := branch(right(tt));
def unit_match : Unit := unit_induction(fun (x : Unit) => Unit, tt, tt);
`);
  for (const name of ["polymorphic", "left_value", "right_value", "unit_match"]) {
    assert.deepEqual(await query(name).observe(), { kind: "Point" });
    assert.equal(kernel.node(normal(name)).kind, "Point");
  }
});

test("two fields share a demanded argument and unsupported siblings remain suspended", async t => {
  const { query } = await setup(t, `
def shared : Unit and Unit := (fun (x : Unit) => typed(Unit and Unit, (x, x)))((fun (y : Unit) => y)(tt));
inductive Circle { base; loop : base = base; }
def suspended : Unit and Circle := (tt, loop @ 0);
def abstraction : Unit and (tt = tt) := (tt, refl(tt));
`);
  const shared = query("shared"), pair = await shared.observe();
  assert.equal(pair.kind, "Pair");
  assert.deepEqual(await shared.observe(pair.first), { kind: "Point" });
  const beta = shared.stats.beta, hits = shared.stats.hits;
  assert.deepEqual(await shared.observe(pair.second), { kind: "Point" });
  assert.equal(shared.stats.beta, beta);
  assert.ok(shared.stats.hits > hits);
  const suspended = query("suspended"), fields = await suspended.observe();
  for (let i = 0; i < 2; i++) {
    await assert.rejects(suspended.observe(fields.second), fails("unsupported"));
    assert.deepEqual(await suspended.observe(fields.first), { kind: "Point" });
  }
  // A path abstraction is a weak head; only applying it is cubical demand.
  const abstraction = query("abstraction"), parts = await abstraction.observe();
  assert.deepEqual(await abstraction.observe(parts.second), { kind: "PathAbstraction" });
});

test("admitted metadata preserves field order and higher-order hypothesis argument order", async t => {
  const { query, kernel, normal } = await setup(t, `
import unat; use unat;
inductive Flag { disabled; enabled; }
inductive Tree(A : U0) { leaf; node(l : Tree(A), datum : A, r : Tree(A)); }
inductive Forest { empty_forest; grow(children : Flag -> Flag -> Forest); }
def size(t : Tree(UNat)) : UNat := induction t return UNat {
  leaf => 0; node(l, datum, r) with ih_l, ih_r => datum + ih_l + ih_r;
};
def left_depth(t : Tree(UNat)) : UNat := induction t return UNat {
  leaf => 0; node(l, datum, r) with ih_l, ih_r => succ(ih_l);
};
def right_depth(t : Tree(UNat)) : UNat := induction t return UNat {
  leaf => 0; node(l, datum, r) with ih_l, ih_r => succ(ih_r);
};
def datum(t : Tree(UNat)) : UNat := match t { leaf => 0; node(l, d, r) => d; };
def depth(t : Forest) : UNat := induction t return UNat {
  empty_forest => 0; grow(children) with below => succ(below(enabled)(disabled));
};
def tree_result : UNat := size(node(node(leaf, 2, leaf), 3, node(leaf, 4, leaf)));
def asymmetric : Tree(UNat) := node(node(node(leaf, 1, leaf), 2, leaf), 17, leaf);
def left_result := left_depth(asymmetric);
def right_result := right_depth(asymmetric);
def datum_result := datum(asymmetric);
def forest_result : UNat := depth(grow(fun (a, b : Flag) => match a return Forest {
  disabled => empty_forest;
  enabled => grow(fun (x, y : Flag) => empty_forest);
}));
`);
  const natural = kernel.signatures.get("unat__UNat").index;
  for (const [name, expected] of [["tree_result", 9], ["left_result", 3], ["right_result", 1],
    ["datum_result", 17], ["forest_result", 2]]) {
    assert.equal(await unary(query(name), natural), expected);
    assert.equal(nativeUnary(kernel, natural, normal(name)), expected);
  }
});

test("eliminators and lifted hypotheses are functions, and a partial constructor tells its arity", async t => {
  const { program, kernel, graph, query } = await setup(t, `
inductive Tree { leaf; node(children : Unit -> Tree); }
inductive Out { base_out; branches(children : Unit -> Out); }
def to_out(t : Tree) : Out := induction t return Out {
  leaf => base_out; node(children) with below => branches(below);
};
def lifted := to_out(node(fun (u : Unit) => leaf));
def identity(x : Unit) : Unit := x;
`);
  const tree = kernel.signatures.get("main__Tree").index;
  // The kernel constructor is a function here, whose weak head is the
  // constructor itself: its arity, not its arguments, tells it from a
  // saturated nullary constructor.
  const partial = new RuntimeQuery(kernel, graph.construct(graph.sortBegin(tree), 1));
  t.after(() => partial.dispose());
  const unapplied = await partial.observe();
  assert.deepEqual([unapplied.kind, unapplied.signature, unapplied.index, unapplied.args, unapplied.arity], ["Con", tree, 1, [], 1]);
  const lifted = query("lifted"), outer = await lifted.observe();
  assert.equal(outer.kind, "Con");
  assert.deepEqual(await lifted.observe(outer.args[0]), { kind: "Function" });
  assert.deepEqual(await query("identity").observe(), { kind: "Function" });
  const unit = { tag: "Unit" }, point = { tag: "Point" };
  const treeType = { tag: "Sort", signature: "main__Tree", parameters: [], levels: [] };
  const lam = (name, domain, body) => ({ tag: "Lam", name, domain, body });
  const pi = (name, domain, body) => ({ tag: "Pi", name, domain, body });
  const eliminator = program.checker.syntax.encode({ tag: "Elim", signature: "main__Tree",
    motive: lam("t", treeType, unit), clauses: [point,
      lam("children", pi("u", unit, treeType), lam("below", pi("v", unit, unit), point))] });
  const typing = new InstructionDriver(kernel).infer(eliminator);
  assert.equal(kernel.node(graph.judgement(typing).term).kind, "Elim");
  const bare = new RuntimeQuery(kernel, typing);
  t.after(() => bare.dispose());
  assert.deepEqual(await bare.observe(), { kind: "Function" });
});

test("an observation is the kernel's weak head: η, functions, types and path abstractions", async t => {
  const { query, kernel, graph } = await setup(t, `
import lists; use unat;
def identity_(U < UU0, A : U, x : A) : A := x;
def successor := fun (n : UNat) => succ(n);
def prepend := fun (xs : List(U0, UNat)) => cons(1, xs);
def doubled := fun (n : UNat) => n + n;
def generic := fun (U < UU0) => identity_(U);
def carrier : U0 := UNat;
def reflexive : tt = tt := refl(tt);
def returned : tt = tt := path i => reflexive @ i;
`);
  // The kernel's weak head of each definition, as its spine names it.
  const kernelHead = name => {
    const { root, args } = kernel.spine(kernel.head(graph.judgement(graph.lookup(kernel.definitions.get(`main__${name}`))).term));
    return root.kind === "Con" ? `Con ${root.payload}/${args.length}` : root.kind;
  };
  const observed = async name => {
    const value = await query(name).observe();
    return value.kind === "Con" ? `Con ${value.index}/${value.args.length}` : value.kind;
  };
  // η makes the successor function the constructor and the prepending one
  // cons applied to its first argument; n + n uses its variable twice and
  // is a function. Level lambdas contract alike.
  for (const [name, kind, head] of [["successor", "Con 1/0", "Con 1/0"], ["prepend", "Con 1/1", "Con 1/1"],
    ["doubled", "Function", "Lam"], ["generic", "LevelFunction", "LLam"], ["carrier", "Type", "Sort"],
    ["reflexive", "PathAbstraction", "PLam"]]) {
    assert.equal(await observed(name), kind, name);
    assert.equal(kernelHead(name), head, name);
  }
  const prepend = query("prepend"), cons = await prepend.observe();
  assert.equal(cons.arity, 2);
  assert.equal(await unary(prepend, kernel.signatures.get("unat__UNat").index, cons.args[0]), 1);
  // path i => p @ i contracts to p in the kernel, by reading the
  // application's interval formula; the runtime does not interpret
  // formulas, and says so.
  await assert.rejects(query("returned").observe(), fails("unsupported"));
  assert.equal(kernelHead("returned"), "PLam");
});

test("observeNow runs the same machine at once, under the same limits", async t => {
  const { query } = await setup(t, "def pair : Unit and Unit := ((fun (x : Unit) => x)(tt), tt);");
  const runtime = query("pair", { slice: 1 }), pair = runtime.observeNow();
  assert.equal(pair.kind, "Pair");
  assert.deepEqual(runtime.observeNow(pair.first), { kind: "Point" });
  const forces = runtime.stats.forces;
  assert.deepEqual(await runtime.observe(pair.first), { kind: "Point" });
  assert.equal(runtime.stats.forces, forces, "the asynchronous observation reads the same forced cell");
  // A deadline that passes mid-force resets the pending cells, and the
  // query stays usable.
  let now = 0;
  t.mock.method(performance, "now", () => now += 1);
  const timed = query("pair", { slice: 1, milliseconds: 3 });
  assert.throws(() => timed.observeNow(), fails("deadline"));
  t.mock.restoreAll();
  assert.equal(timed.observeNow().kind, "Pair");
  // One observation at a time, either kind, and none after disposal.
  const busy = query("pair", { slice: 1 }), pending = busy.observe();
  assert.throws(() => busy.observeNow(), fails("input"));
  assert.equal((await pending).kind, "Pair");
  busy.dispose();
  assert.throws(() => busy.observeNow(), fails("disposed"));
});

test("definition sharing does not depend on syntax interning", async t => {
  const { kernel, graph } = await setup(t, "def value : Unit := (fun (x : Unit) => x)(tt);");
  kernel.setOptimizations({ shareSyntax: false });
  const payload = kernel.node(kernel.definitions.get("main__value")).payload;
  const first = kernel.term("DefRef", payload), second = kernel.term("DefRef", payload);
  assert.notEqual(first, second);
  const driver = new InstructionDriver(kernel), unit = graph.unit();
  const pair = graph.pair(graph.sigma(graph.extend(unit, "x"), unit), driver.infer(first), driver.infer(second));
  const query = new RuntimeQuery(kernel, pair); t.after(() => query.dispose());
  const fields = await query.observe();
  await query.observe(fields.first);
  const beta = query.stats.beta;
  await query.observe(fields.second);
  assert.equal(query.stats.beta, beta);
});

// A query reads the kernel when its walk first demands a node, a definition
// or a signature: what it never demands is never copied.
test("a query copies only what its walk demands", async t => {
  const { query, kernel } = await setup(t, `
import unat; use unat;
def unused_ : UNat := 2 * 255;
def helper(x : Unit) : Unit := x;
def value : Unit and UNat := (helper(tt), unused_);
`);
  const runtime = query("value");
  assert.deepEqual([runtime.stats.snapshotNodes, runtime.stats.snapshotDefinitions], [0, 0]);
  const pair = await runtime.observe();
  // The root's definition: its reference, the application of an identity
  // that ascribes its type, without the type, and the pair, without its
  // components or their definitions.
  assert.equal(runtime.stats.snapshotDefinitions, 1);
  assert.equal(runtime.stats.snapshotNodes, 5);
  assert.deepEqual(await runtime.observe(pair.first), { kind: "Point" });
  assert.equal(runtime.stats.snapshotDefinitions, 2, "helper, and still not the unused component");
  // Demanded, the second component's definitions are copied: unused_, the
  // multiplication and what it reaches.
  const natural = kernel.signatures.get("unat__UNat").index;
  assert.equal(await unary(runtime, natural, pair.second), 510);
  assert.ok(runtime.stats.snapshotDefinitions > 2);
  assert.equal(runtime.retainedObjects().snapshotNodes, runtime.stats.snapshotNodes);
});

// The kernel's handles name what they named when the query was made until
// the session is disposed or a checkpoint open then ends; a read after that
// expires, and what the query copied and computed before stays observable.
test("unread syntax expires with the kernel's handles, and what was read survives", async t => {
  const { program, query, kernel, graph } = await setup(t, "def value : Unit and Unit := (tt, (fun (u : Unit) => u)(tt));");
  // Made with no checkpoint open, a query survives later declarations,
  // accepted or refused: no handle it holds moves.
  const outside = query("value");
  const later = await program.check("def other : Unit := tt;\ndef refused : Unit := Unit;", "later");
  assert.deepEqual(later.outputs.filter(output => output.name !== "value").map(output => [output.name, output.verified]),
    [["other", true], ["refused", false]]);
  const fields = await outside.observe();
  assert.deepEqual(await outside.observe(fields.second), { kind: "Point" });
  // Made while a declaration's checkpoint is open, a query expires when it
  // is committed or rolled back, which move or drop the handles made since.
  for (const accept of [false, true]) {
    const transaction = new CubicalDeclarationTransaction(kernel, program.checker), unit = graph.unit(), point = graph.point();
    const applied = graph.apply(graph.lambda(graph.extend(unit, "y"), point), point);
    const inner = new RuntimeQuery(kernel, graph.pair(graph.sigma(graph.extend(unit, "x"), unit), point, applied));
    t.after(() => inner.dispose());
    const pair = await inner.observe();
    assert.deepEqual(await inner.observe(pair.first), { kind: "Point" });
    transaction.finish(accept);
    assert.equal((await inner.observe(inner.root)).kind, "Pair", "computed before, still observable");
    assert.deepEqual(await inner.observe(pair.first), { kind: "Point" });
    await assert.rejects(inner.observe(pair.second), fails("expired"));
  }
  // Disposal expires every query; handles stay local to their query.
  const first = query("value"), second = query("value"), root = first.root;
  const pair = await first.observe(root);
  assert.deepEqual(await first.observe(pair.first), { kind: "Point" });
  kernel.dispose();
  assert.equal((await first.observe(root)).kind, "Pair");
  assert.deepEqual(await first.observe(pair.first), { kind: "Point" });
  await assert.rejects(first.observe(pair.second), fails("expired"));
  await assert.rejects(second.observe(root), fails("input"));
  first.dispose();
  await assert.rejects(first.observe(root), fails("disposed"));
});

// A lazy read is work and cells of the observation that demands it: a
// limit can stop the query in the middle of copying, as it stops a force.
// After a cell stop what was computed stays observable; an exhausted work
// budget ends the query's observations, as before.
test("lazy reads count against the query's work and cells", async t => {
  const { query } = await setup(t, `
def helper(x : Unit) : Unit := x;
def value : Unit and Unit := (helper(tt), tt);
`);
  const calibration = query("value");
  await calibration.observe();
  const before = calibration.stats;
  await calibration.observe((await calibration.observe()).first);
  const after = calibration.stats;
  assert.ok(after.snapshotNodes > before.snapshotNodes && after.snapshotDefinitions > before.snapshotDefinitions);
  for (const [option, counter, kind] of [["maxCells", "allocatedCells", "resource"], ["maxSteps", "steps", "budget"]]) {
    // Enough for the pair, and for the force of its first component up to
    // the read of its syntax.
    const runtime = query("value", { [option]: before[counter] + 2 }), pair = await runtime.observe();
    assert.deepEqual(runtime.stats, before);
    await assert.rejects(runtime.observe(pair.first), error => fails(kind)(error)
      && error.limit === before[counter] + 2 && error.stats.snapshotNodes === before.snapshotNodes);
    if (kind === "resource") assert.equal((await runtime.observe()).kind, "Pair");
    else await assert.rejects(runtime.observe(), fails("budget"));
  }
});

test("disposal rejects completed forces before the default-slice observation publishes", async t => {
  const { query } = await setup(t, `
inductive Flag { disabled; enabled; }
def constructor_value : Flag := enabled;
def pair_value : Unit and Unit := (tt, tt);
def point_value : Unit := tt;
`);
  for (const name of ["constructor_value", "pair_value", "point_value"]) {
    const runtime = query(name), pending = runtime.observe();
    assert.ok(runtime.stats.forces > 0 && runtime.stats.steps < 20000,
      "the force must finish before its first cooperative yield");
    runtime.dispose();
    await assert.rejects(pending, fails("disposed"));
  }
});

test("an allocation stop preserves observations that need no further allocation", async t => {
  const { query } = await setup(t, "def pair : Unit and Unit := (tt, tt);");
  const calibration = query("pair"), measured = await calibration.observe();
  await calibration.observe(measured.first);
  const maxCells = calibration.stats.allocatedCells;
  const runtime = query("pair", { maxCells }), pair = await runtime.observe();
  await runtime.observe(pair.first);
  assert.equal(runtime.stats.allocatedCells, maxCells);
  await assert.rejects(runtime.observe(pair.second), fails("resource"));
  assert.deepEqual(await runtime.observe(pair.first), { kind: "Point" });
  assert.equal(runtime.stats.allocatedCells, maxCells);
  assert.ok(runtime.retainedObjects().runtimeObjects > 0);
});

test("work, allocation, cancellation and disposal have controlled failures", async t => {
  const { query } = await setup(t, "def value : Unit := (fun (x : Unit) => x)(tt);");
  assert.throws(() => query("value", { maxSteps: 1 }), fails("budget"));
  assert.throws(() => query("value", { maxCells: 1 }), fails("resource"));
  for (const maxSteps of [0, -1, 1.5, Infinity])
    assert.throws(() => query("value", { maxSteps }), TypeError);
  const aborted = new AbortController(); aborted.abort();
  assert.throws(() => query("value", { signal: aborted.signal }), fails("cancelled"));
  const controller = new AbortController(), running = query("value", { slice: 1 });
  const pending = running.observe(running.root, { signal: controller.signal });
  await new Promise(setImmediate);
  assert.ok(running.stats.forces > 0, "cancellation must interrupt pending thunk updates");
  controller.abort();
  await assert.rejects(pending, fails("cancelled"));
  assert.deepEqual(await running.observe(), { kind: "Point" }, "a cancelled observation does not expire the query");
  const disposed = query("value", { slice: 1 }), active = disposed.observe();
  disposed.dispose();
  await assert.rejects(active, fails("disposed"));
  const concurrent = query("value", { slice: 1 }), first = concurrent.observe();
  await assert.rejects(concurrent.observe(), fails("input"));
  assert.deepEqual(await first, { kind: "Point" });
});

test("observation deadlines exclude idle time and expiry leaves the query usable", async t => {
  const { query } = await setup(t, "def value : Unit := (fun (x : Unit) => x)(tt);");
  let now = 0;
  t.mock.method(performance, "now", () => now);
  const runtime = query("value", { slice: 1, milliseconds: 5 });
  now = 1000; // Time between construction and a request is not execution time.
  const pending = runtime.observe();
  await new Promise(setImmediate);
  assert.ok(runtime.stats.forces > 0, "deadline must interrupt pending thunk updates");
  now = 1006;
  await assert.rejects(pending, fails("deadline"));
  now = 2000;
  assert.deepEqual(await runtime.observe(), { kind: "Point" });
  for (const milliseconds of [0, -1, 1.5, Infinity])
    await assert.rejects(runtime.observe(runtime.root, { milliseconds }), TypeError);
  assert.deepEqual(await runtime.observe(), { kind: "Point" });
});

// A path constructor, the squash among them, and a point constructor with a
// position whose cube is a path type are refused when demanded, not because
// their signature occurs; the point constructors beside them compute.
test("path constructors and cubical positions are refused only when demanded", async t => {
  const { query } = await setup(t, `
import h1_truncation;
inductive Cube { cbase; pack(p : cbase = cbase); }
inductive Circle { base; loop : base = base; }
def unused_cube : Unit := (fun (c : Cube) => tt)(pack(refl(cbase)));
def cube_leaf : Cube := cbase;
def cube_path : Cube := pack(refl(cbase));
def circle_value : Circle := base;
def circle_loop : base = base := loop;
def circle_endpoint : Circle := loop @ 1;
def unused_loop : Unit := (fun (p : base = base) => tt)(loop);
def squashed := Trunc.squash(typed(Trunc(U0, Unit), point(tt)), typed(Trunc(U0, Unit), point(tt)));
`);
  const refused = message => error => fails("unsupported")(error) && error.message === message;
  assert.deepEqual(await query("unused_cube").observe(), { kind: "Point" });
  assert.equal((await query("cube_leaf").observe()).kind, "Con");
  await assert.rejects(query("cube_path").observe(), refused("Execution of a constructor with cubical recursive positions is not implemented."));
  assert.deepEqual((({ kind, index, args, arity }) => ({ kind, index, args, arity }))(await query("circle_value").observe()),
    { kind: "Con", index: 0, args: [], arity: 0 });
  await assert.rejects(query("circle_loop").observe(), refused("Execution of a path constructor is not implemented."));
  await assert.rejects(query("squashed").observe(), refused("Execution of a path constructor is not implemented."));
  await assert.rejects(query("circle_endpoint").observe(), refused("Runtime execution of PApp is not implemented."));
  assert.deepEqual(await query("unused_loop").observe(), { kind: "Point" });
});

// The eliminator of a higher or truncated sort, applied to a point
// constructor, selects the clause the kernel's iota selects; its other
// clauses, for paths and the squash, are never demanded.
test("point constructors of higher and truncated sorts compute, with their eliminators' point clauses", async t => {
  const { query, kernel, normal } = await setup(t, `
import quotients; import h1_truncation; use unat;
inductive Circle { base; loop : base = base; }
def R(m, n : UNat) : U0 := Unit;
def doubled(q : Quotient(U0, UNat, R)) : Quotient(U0, UNat, R) := match q {
  class(a) => class(a + a);
} obligations by (fun (a, b : UNat, r : R(a, b)) => class_path(U0, UNat, R, a + a, b + b, tt));
def to_nat(c : Circle) : UNat := match c { base => 3; loop @ i => 3; };
def doubled_class : Quotient(U0, UNat, R) := doubled(class(2));
def circle_nat : UNat := to_nat(base);
def mapped : Trunc(U0, UNat) := mere_map(U0, U0, UNat, UNat, fun (n : UNat) => n + 1, point(4));
`);
  const natural = kernel.signatures.get("unat__UNat").index;
  // The constructor's index and its one argument, by the runtime and in the
  // kernel's normal form.
  for (const [name, signature, value] of [["doubled_class", "quotients__Quotient", 4], ["mapped", "h1_truncation__Trunc", 5]]) {
    const runtime = query(name), observed = await runtime.observe();
    assert.deepEqual([observed.kind, observed.signature, observed.index, observed.arity],
      ["Con", kernel.signatures.get(signature).index, 0, 1], name);
    assert.equal(await unary(runtime, natural, observed.args[0]), value, name);
    const native = kernel.node(normal(name)), constructor = kernel.node(native.children[0]);
    assert.deepEqual([native.kind, constructor.kind, constructor.payload], ["App", "Con", 0], name);
    assert.equal(nativeUnary(kernel, natural, native.children[1]), value, name);
  }
  assert.equal(await unary(query("circle_nat"), natural), 3);
  assert.equal(nativeUnary(kernel, natural, normal("circle_nat")), 3);
});

test("the MessageChannel scheduler yields and releases its ports", () => {
  // Exercise the browser scheduling branch in an isolated process. Its exit
  // also detects a MessagePort left live after the observation completes.
  const environment = { ...process.env };
  delete environment.NODE_TEST_CONTEXT;
  const output = execFileSync(process.execPath, ["--input-type=module", "--eval", `
    import createCubical from './web/dist/cubical.mjs';
    import { CubicalKernel } from './web/cubical-kernel.mjs';
    import { InstructionGraph } from './web/cubical-instructions.mjs';
    const immediate = globalThis.setImmediate;
    globalThis.setImmediate = undefined;
    const { RuntimeQuery } = await import('./web/cubical-runtime.mjs');
    globalThis.setImmediate = immediate;
    const kernel = new CubicalKernel(await createCubical());
    const query = new RuntimeQuery(kernel, new InstructionGraph(kernel).point(), { slice: 1 });
    try { console.log(JSON.stringify(await query.observe())); }
    finally { query.dispose(); kernel.dispose(); }
  `], { cwd: new URL("..", import.meta.url), env: environment, encoding: "utf8", timeout: budget(5000) });
  assert.deepEqual(JSON.parse(output), { kind: "Point" });
});

test("the fixed Euclid source exposes its prime without native substitution chains", async t => {
  const { query, kernel } = await setup(t, `
import euclid; use unat;
def four := euclid(4);
def five := euclid(5);
def six := euclid(6);
`);
  const natural = kernel.signatures.get("unat__UNat").index;
  for (const [name, expected] of [["four", 5], ["five", 11]]) {
    const before = kernel.arena().nodes, runtime = query(name, { milliseconds: budget(30000) }), pair = await runtime.observe();
    assert.equal(pair.kind, "Pair");
    assert.equal(await unary(runtime, natural, pair.first), expected);
    assert.equal(kernel.arena().nodes, before, "runtime allocated native substitution syntax");
    const retained = runtime.retainedObjects();
    assert.ok(retained.runtimeObjects > 0);
    assert.ok(retained.snapshotNodes < 5000);
    runtime.dispose();
  }
  const bounded = query("six", { maxSteps: 2000000 }), pair = await bounded.observe();
  await assert.rejects(unary(bounded, natural, pair.first), fails("budget"));
  assert.ok(bounded.stats.maxFrames > 3500, "workload did not reach the old host stack failure");
});
