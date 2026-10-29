import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { CubicalDeclarationTransaction } from "../web/cubical-transaction.mjs";
import { KernelError } from "../web/cubical-kernel.mjs";
import { RuntimeQuery } from "../web/cubical-runtime.mjs";
import { Translator } from "../web/translator/translate.mjs";
import { valueForm } from "../web/translator/evaluation.mjs";
import { checkProgram } from "./check-program.mjs";
import { watchReadbacks, disagreements } from "./runtime-readback-oracle.mjs";

// Readback, W1 of docs/roadmaps/runtime/typed-readback.md: a runtime value
// as the closed kernel term it stands for (RuntimeQuery.readback). These
// tests read back the cases of the note's W1 list; the differential over
// every value form the runtime computes runs where those value forms are
// checked (tests/runtime-readback-oracle.mjs). Terms are compared by syntax
// only, never by conversion.
const module = await createCubical();
const fails = kind => error => error?.kind === kind;
const deep = error => error instanceof KernelError && error.message === "Native prototype syntax depth exceeds 512.";

async function setup(t, source) {
  const { program, result } = await checkProgram(t, source, { module, options: { collectReferences: false } });
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const { kernel, checker } = program, graph = new InstructionGraph(kernel), defined = new Map();
  // A term written as kernel syntax, derived by the instruction driver: the
  // elaborator names a shadowing binder apart, the kernel need not.
  const define = (name, written) => defined.set(name, new InstructionDriver(kernel).infer(checker.syntax.encode(written)));
  const judgement = name => defined.get(name) ?? graph.lookup(kernel.definitions.get(`main__${name}`));
  // A definition's checked term, which normalize accepts.
  const term = name => { const handle = graph.judgement(judgement(name)).term; (kernel.derivedHandles ??= new Set()).add(handle); return handle; };
  const query = (made, options = {}, Query = RuntimeQuery) => {
    const runtime = new Query(kernel, typeof made === "string" ? judgement(made) : made, options);
    t.after(() => runtime.dispose());
    return runtime;
  };
  // The value form's walk, as print(evaluate(e)) takes it (valueFormOf in
  // web/translator/translate.mjs), and the handles it observed.
  const quiet = { spend() {} }, kernelAt = Translator.prototype.demandQueries.call({ checker }, quiet, () => "");
  const walk = runtime => {
    const at = Translator.prototype.runtimeQueries.call({ checker }, quiet, runtime, kernelAt), observed = [], head = at.head;
    at.head = handle => { observed.push(handle); return head(handle); };
    valueForm(runtime.root, at);
    return observed;
  };
  const same = (a, b) => kernel.alphaEqual(a, b);
  return { program, kernel, checker, graph, define, judgement, term, query, walk, same, decoded: handle => checker.decoded(handle),
    normal: handle => kernel.normalize(handle), folded: handle => kernel.normalizeFolded(handle) };
}
// Kernel syntax as the encoder takes it (web/cubical-syntax.mjs).
const v = name => ({ tag: "Var", name }), U0 = { tag: "U", level: 0 }, unit = { tag: "Unit" }, point = { tag: "Point" };
const lam = (name, domain, body) => ({ tag: "Lam", name, domain, body }), app = (fn, arg) => ({ tag: "App", fn, arg });
const flag = index => ({ tag: "Con", index, sort: { tag: "Sort", signature: "main__Flag", parameters: [], levels: [] } });
const flagType = { tag: "Sort", signature: "main__Flag", parameters: [], levels: [] };
// (λ (x : Flag). (λ (x : Flag). λ (u : Unit). x)(disabled))(enabled), one
// symbol bound twice; and (λ (x : U0). λ (x : x). λ (u : Unit). x)(Unit, tt),
// whose inner binder's domain is the outer x.
const shadowed = app(lam("x", flagType, app(lam("x", flagType, lam("u", unit, v("x"))), flag(0))), flag(1));
const shadowedDomain = app(app(lam("x", U0, lam("x", v("x"), lam("u", unit, v("x")))), unit), point);
// The distinct nodes of a term.
const dagSize = (kernel, handle) => {
  const seen = new Set(), pending = [handle];
  while (pending.length) {
    const id = pending.pop();
    if (!id || seen.has(id)) continue;
    seen.add(id); pending.push(...kernel.node(id).children);
  }
  return seen.size;
};

// Capture and shadowing: a closure is the telescope of the frames its code
// needs, the nearest binding of each variable as the machine's lookup
// takes it, applied to their cells; its full normal form is the kernel's.
test("closures read back as redexes keep capture and shadowing", async t => {
  const s = await setup(t, `
inductive Flag { disabled; enabled; }
def capture : Flag := (fun (x : Flag) => (fun (f : Flag -> Flag) => (fun (x : Flag) => f(x))(disabled))(fun (y : Flag) => x))(enabled);
def outer := (fun (x : Flag) => (fun (y : Flag) => fun (u : Unit) => x)(disabled))(enabled);
def escaped := (fun (x : Flag) => (fun (f : Unit -> Flag) => (fun (x : Flag) => f)(disabled))(fun (u : Unit) => x))(enabled);
`);
  s.define("shadowed", shadowed); s.define("shadowed_domain", shadowedDomain);
  for (const name of ["capture", "outer", "escaped", "shadowed", "shadowed_domain"]) {
    const runtime = s.query(name);
    s.walk(runtime);
    const read = runtime.readback();
    assert.ok(s.same(s.normal(read), s.normal(s.term(name))), name);
    new InstructionDriver(s.kernel).check(read, s.graph.judgement(s.judgement(name)).type);
  }
  // fun (u : Unit) => x with x bound twice: one binding, the nearest,
  // disabled; in outer, x's frame, enabled, without y's; and a closure
  // escaping the scope that shadows its variable keeps its own frame.
  for (const [name, index] of [["shadowed", 0], ["outer", 1], ["escaped", 1]]) {
    const runtime = s.query(name);
    s.walk(runtime);
    const read = s.decoded(runtime.readback());
    assert.equal(read.tag, "App", name);
    assert.deepEqual([read.fn.tag, read.fn.body.tag, read.arg.tag, read.arg.index], ["Lam", "Lam", "Con", index], name);
    assert.equal(runtime.readbackStats.bindings, 1, name);
  }
  // The inner x's domain is the outer x: both frames are bound, in order,
  // the outer applied to Unit and the inner to tt.
  const runtime = s.query("shadowed_domain");
  s.walk(runtime);
  const read = s.decoded(runtime.readback());
  assert.deepEqual([read.arg.tag, read.fn.arg.tag, read.fn.fn.domain.tag, read.fn.fn.body.domain.tag], ["Point", "Unit", "U", "Var"]);
  assert.equal(read.fn.fn.body.domain.name, read.fn.fn.name);
});

// A closure whose code needs no frame is the code itself: an argument it
// does not use is never read back, and nothing is written. A cell reached
// twice is read back once.
test("an unused argument is never read back, and a cell reached twice is one handle", async t => {
  const s = await setup(t, `
import unat; use unat;
def unused := (fun (x : UNat) => fun (y : Unit) => y)(2 * 255);
def twice := (fun (x : UNat) => typed(UNat and UNat, (x, x)))(2 * 3);
`);
  const unused = s.query("unused");
  s.walk(unused);
  const arena = s.kernel.arena().nodes, read = unused.readback();
  assert.deepEqual(s.decoded(read), { tag: "Lam", name: s.decoded(read).name, domain: { tag: "Unit" }, body: { tag: "Var", name: s.decoded(read).name } });
  assert.deepEqual([unused.readbackStats.cells, unused.readbackStats.writes, s.kernel.arena().nodes], [1, 0, arena]);
  const twice = s.query("twice");
  s.walk(twice);
  const pair = s.kernel.node(twice.readback());
  assert.equal(pair.kind, "Pair");
  assert.equal(pair.children[1], pair.children[2]);
  assert.ok(twice.readbackStats.hits > 0);
  assert.ok(s.same(s.normal(s.term("twice")), s.normal(twice.readback())));
});

// A level argument whose code mentions a level variable bound in its
// environment is read off the kernel's weak head of the universe at that
// level, closed by its telescope: the kernel substitutes and canonicalizes.
test("a level argument that mentions a bound level variable comes back canonical", async t => {
  const s = await setup(t, "def placeholder := tt;");
  const succ = level => ({ tag: "LSucc", count: 1, level }), max = (left, right) => ({ tag: "LMax", left, right });
  // (Λ l. (Λ m. λ (u : Unit). U(max(m, l) + 1)){max(l + 1, 1)}){2}
  const term = { tag: "LApp", level: 2, fn: { tag: "LLam", name: "l", body: { tag: "LApp", level: max(succ(v("l")), 1),
    fn: { tag: "LLam", name: "m", body: lam("u", unit, { tag: "U", level: succ(max(v("m"), v("l"))) }) } } } };
  const typing = new InstructionDriver(s.kernel).infer(s.checker.syntax.encode(term)), { term: checked, type } = s.graph.judgement(typing);
  (s.kernel.derivedHandles ??= new Set()).add(checked);
  const runtime = s.query(typing);
  s.walk(runtime);
  const read = runtime.readback(), shown = s.decoded(read);
  // The telescope binds l and m, applied to 2 and to m's level, 3.
  assert.deepEqual([shown.tag, shown.level, shown.fn.tag, shown.fn.level], ["LApp", 3, "LApp", 2]);
  assert.ok(s.same(s.normal(read), s.normal(checked)));
  assert.deepEqual(s.decoded(s.normal(read)), { tag: "Lam", name: s.decoded(s.normal(read)).name, domain: { tag: "Unit" }, body: { tag: "U", level: 4 } });
  new InstructionDriver(s.kernel).check(read, type);
});

// R(root) is a closed term well typed at the value's type (3.6, claim 1):
// a telescope closes its domains together, a type value is read from its
// node under its environment, and a constructor's instance is a literal
// Sort, which the kernel eliminates.
test("readbacks of closures, a type value and a constructor are well typed, and the constructor eliminates", async t => {
  const s = await setup(t, `
inductive Box(A : U0) { box(a : A); }
def unbox(b : Box(Unit)) : Unit := match b { box(a) => a; };
def captured := (fun (A : U0) => fun (x : A) => fun (u : Unit) => typed(A and A, (x, x)))(Unit, tt);
def endo := (fun (A : U0) => A -> A)(Unit);
def boxed := (fun (A : U0) => fun (a : A) => typed(Box(A), box(a)))(Unit, tt);
`);
  const read = name => { const runtime = s.query(name); s.walk(runtime); return runtime.readback(); };
  for (const name of ["captured", "endo", "boxed"]) {
    const handle = read(name);
    assert.ok(s.same(s.normal(handle), s.normal(s.term(name))), name);
    new InstructionDriver(s.kernel).check(handle, s.graph.judgement(s.judgement(name)).type);
  }
  assert.deepEqual(s.decoded(s.normal(read("endo"))), { tag: "Pi", name: s.decoded(s.normal(read("endo"))).name, domain: { tag: "Unit" }, body: { tag: "Unit" } });
  // Closed one by one, A's domain outside or x's, the same body is refused;
  // the telescope is typed.
  const body = lam("u", unit, { tag: "Pair", as: { tag: "Sigma", name: "_", domain: v("A"), body: v("A") }, first: v("x"), second: v("x") });
  for (const closed of [app(lam("A", U0, app(lam("x", v("A"), body), point)), unit), app(lam("x", unit, app(lam("A", U0, body), unit)), point)])
    assert.throws(() => new InstructionDriver(s.kernel).infer(s.checker.syntax.encode(closed)), Error);
  new InstructionDriver(s.kernel).infer(s.checker.syntax.encode(app(app(lam("A", U0, lam("x", v("A"), body)), unit), point)));
  // The constructor eliminates; with its instance a redex, Box(A) under
  // (λ (A : U0). …)(Unit), the kernel's head refuses it.
  const unbox = s.kernel.definitions.get("main__unbox");
  assert.equal(s.kernel.node(s.kernel.head(s.kernel.term("App", 0, unbox, read("boxed")))).kind, "Point");
  const redex = s.checker.syntax.encode(app({ tag: "Con", index: 0, sort: app(lam("A", U0, { tag: "Sort", signature: "main__Box", parameters: [v("A")], levels: [] }), unit) }, point));
  assert.throws(() => s.kernel.head(s.kernel.term("App", 0, unbox, redex)), KernelError);
});

// η leaves a cell holding its λ, so R(root) never reads back the head an
// observation computed: a query made with heads keeps that head, read back
// on its own, and its full normal form is its cell's. A query made without
// them, as a value form's is, keeps none, and reads none back.
test("the head an observation computed by η reads back to its cell's full normal form", async t => {
  const s = await setup(t, `
import lists; use unat;
inductive Flag { disabled; enabled; }
def successor := fun (n : UNat) => succ(n);
def prepend := fun (xs : List(U0, UNat)) => cons(1, xs);
def toggle := fun (f : Flag) => match f return Flag { disabled => enabled; enabled => disabled; };
`);
  for (const [name, kind] of [["successor", "Con"], ["prepend", "App"], ["toggle", "Elim"]]) {
    const runtime = s.query(name, { heads: true }), observed = s.walk(runtime);
    assert.equal(observed[0], runtime.root, name);
    const head = runtime.readback(runtime.root, { head: true }), cell = runtime.readback();
    assert.deepEqual([s.kernel.node(cell).kind, s.kernel.node(head).kind], ["Lam", kind], name);
    // Each head the walk observed, cons(1)'s argument too.
    for (const handle of observed) assert.ok(s.same(s.normal(runtime.readback(handle, { head: true })), s.normal(runtime.readback(handle))), name);
    // The kept head is retained, and counted: more objects than a value
    // form's query holds after the same walk.
    const plain = s.query(name);
    s.walk(plain);
    assert.throws(() => plain.readback(plain.root, { head: true }), fails("input"), name);
    assert.ok(runtime.retainedObjects().runtimeObjects > plain.retainedObjects().runtimeObjects, name);
  }
  // For successor, three more: the constructor value, its instance cell and
  // its argument list.
  const [kept, plain] = [{ heads: true }, {}].map(options => { const runtime = s.query("successor", options); s.walk(runtime); return runtime; });
  assert.equal(kept.retainedObjects().runtimeObjects, plain.retainedObjects().runtimeObjects + 3);
});

// A type value keeps of its environment only the bindings its node uses,
// so a value form whose result is a type retains nothing of the
// computation that chose it: traverse(100 * 100) retains what traverse(10
// * 10) does, the 13 objects the runtime retained before readback.
test("a type value keeps only the bindings its node uses", async t => {
  const s = await setup(t, `
import unat; use unat;
def traverse(n : UNat) : U0 := match n { zero => Unit; succ(k) => traverse(k); };
def far := traverse(100 * 100);
def near := traverse(10 * 10);
def endo := (fun (A : U0) => fun (n : UNat) => A -> A)(Unit, 100 * 100);
`);
  const retained = name => { const runtime = s.query(name); s.walk(runtime); return runtime.retainedObjects().runtimeObjects; };
  assert.deepEqual([retained("far"), retained("near")], [13, 13]);
  // A -> A keeps A's binding, which its readback reads, and not n's.
  const endo = s.query("endo");
  s.walk(endo);
  assert.ok(endo.retainedObjects().runtimeObjects < 10);
  assert.ok(s.same(s.normal(endo.readback()), s.normal(s.term("endo"))));
});

// With origins, a non-data part is read back as the computation it was
// forced from, so that folding passes the definition spines the kernel's
// folded normal form keeps (3.4); read by value, each folds away. The
// note's regressions: a closure over cert(x) in a pair; x.1 with x data;
// a Tag(x) constructor beside (fun y => y.1)(x); x.1(tt); and two more,
// x itself, data read by value, beside (fun y => y.1)(x), which reads it by
// origin, so that the memo must not answer one mode with the other's
// readback; and x.1 inside a constructor's instance and a pair's type,
// annotations no value form forces, as inside an origin.
test("read back by origin, each part folds as the kernel's folded normal form does", async t => {
  const s = await setup(t, `
def cert(x : Unit) : Unit -> Unit := fun (y : Unit) => tt;
def certPair(u : Unit) : (Unit -> Unit) and Unit := (fun (y : Unit) => tt, tt);
def certPair2(u : Unit) : (Unit -> Unit -> Unit) and Unit := (fun (a : Unit) => fun (b : Unit) => tt, tt);
inductive Tag(p : (Unit -> Unit) and Unit) { tag; }
inductive Marked(f : Unit -> Unit) { mark; }
def wrapped := (fun (x : Unit) => typed(Unit and (Unit -> Unit), (x, cert(x))))(tt);
def projected := (fun (x : (Unit -> Unit) and Unit) => typed(Unit and (Unit -> Unit), (tt, x.1)))(certPair(tt));
def tagged := (fun (x : (Unit -> Unit) and Unit) => typed(Tag(x) and (Unit -> Unit), (tag, (fun (y : (Unit -> Unit) and Unit) => y.1)(x))))(certPair(tt));
def applied := (fun (x : (Unit -> Unit -> Unit) and Unit) => typed(Unit and (Unit -> Unit), (tt, x.1(tt))))(certPair2(tt));
def shared := (fun (x : (Unit -> Unit) and Unit) => typed(((Unit -> Unit) and Unit) and (Unit -> Unit), (x, (fun (y : (Unit -> Unit) and Unit) => y.1)(x))))(certPair(tt));
def annotated := (fun (x : (Unit -> Unit) and Unit) => typed(((Unit -> Unit) and Unit) and Marked(x.1), (x, mark)))(certPair(tt));
`);
  // What each keeps folded in its second part: cert(tt), certPair(tt).1,
  // certPair(tt).1, certPair2(tt).1(tt) and certPair(tt).1, each a
  // definition applied or projected, and mark, whose instance keeps
  // certPair(tt).1 as the pair's type does.
  for (const [name, kept] of [["wrapped", "App"], ["projected", "Fst"], ["tagged", "Fst"], ["applied", "App"], ["shared", "Fst"], ["annotated", "Con"]]) {
    const runtime = s.query(name, { origins: true });
    s.walk(runtime);
    const kernelFolded = s.folded(s.term(name)), second = s.kernel.node(s.kernel.node(kernelFolded).children[2]);
    assert.equal(second.kind, kept, name);
    assert.ok(s.same(s.folded(runtime.readback(runtime.root, { origins: true })), kernelFolded), name);
    // By value, the same query's readback has the same full normal form,
    // and folds the definition away.
    const byValue = runtime.readback();
    assert.ok(s.same(s.normal(byValue), s.normal(s.term(name))), name);
    assert.ok(!s.same(s.folded(byValue), kernelFolded), name);
  }
  // A query made without origins keeps none to read.
  const plain = s.query("wrapped");
  s.walk(plain);
  assert.throws(() => plain.readback(plain.root, { origins: true }), fails("input"));
});

// A readback starts, writes and returns a handle only while the kernel's
// handles are the query's (section 7): after a checkpoint's rollback or
// commit it is "expired", whether it would write or not, as a closed code's
// own handle and a memoized handle are.
test("after a rollback or a commit, a readback is expired, whether it writes or not", async t => {
  const s = await setup(t, `inductive Flag { disabled; enabled; }
def pair : Flag and Flag := ((fun (x : Flag) => x)(enabled), disabled);
def flag : Flag := (fun (x : Flag) => x)(enabled);`);
  for (const accept of [false, true]) {
    const writing = s.query("pair"), closed = s.query("pair"), memoized = s.query("flag");
    s.walk(writing); s.walk(memoized);
    // Never observed, the root is its closed code, and nothing is written.
    const root = s.graph.judgement(s.judgement("pair")).term, arena = s.kernel.arena().nodes;
    assert.equal(closed.readback(), root);
    assert.deepEqual([closed.readbackStats.writes, s.kernel.arena().nodes], [0, arena]);
    // Read back once, every cell it reads forced: the second readback is
    // the memo's, and writes nothing.
    const first = memoized.readback(), { writes } = memoized.readbackStats;
    assert.equal(memoized.readback(), first);
    assert.equal(memoized.readbackStats.writes, writes);
    new CubicalDeclarationTransaction(s.kernel, s.checker).finish(accept);
    for (const runtime of [writing, closed, memoized]) assert.throws(() => runtime.readback(), fails("expired"));
    // What the walk computed stays observable.
    assert.equal(writing.observeNow().kind, "Pair");
  }
});

// A higher-order recursive hypothesis is refused (3.7); a value deeper than
// the kernel's syntax is refused by the kernel's own guard (K344), whatever
// its depth, since readback keeps its own stack.
test("a lifted hypothesis is refused, and a value past the kernel's syntax depth fails with K344", async t => {
  const s = await setup(t, `
import unat; use unat;
inductive Tree { leaf; node(children : Unit -> Tree); }
inductive Out { base_out; branches(children : Unit -> Out); }
def to_out(t : Tree) : Out := induction t return Out { leaf => base_out; node(children) with below => branches(below); };
def lifted := to_out(node(fun (u : Unit) => leaf));
def edge : UNat := 2 * 255;
def past : UNat := succ(2 * 255);
def far : UNat := 100 * 100;
`);
  const lifted = s.query("lifted");
  s.walk(lifted);
  assert.throws(() => lifted.readback(), error => fails("unsupported")(error)
    && error.message === "Readback of a higher-order recursive hypothesis is not implemented.");
  const unary = (runtime, count) => {
    for (let at = runtime.root, n = 0; n <= count; n++) {
      const value = runtime.observeNow(at);
      if (!value.args.length) return n;
      at = value.args[0];
    }
    return -1;
  };
  const [edge, past, far] = ["edge", "past", "far"].map(name => s.query(name));
  assert.deepEqual([unary(edge, 600), unary(past, 600), unary(far, 20000)], [510, 511, 10000]);
  assert.ok(s.same(s.normal(edge.readback()), s.normal(s.term("edge"))));
  assert.throws(() => past.readback(), deep);
  assert.throws(() => far.readback(), deep);
});

// A readback's work and cells are the query's, under its limits (3.7): a
// query whose walk leaves too few for its readback stops it, as an
// observation stops.
test("a readback spends the query's work and cells, and stops at its limits", async t => {
  const s = await setup(t, "inductive Flag { disabled; enabled; }\ndef pair : Flag and Flag := ((fun (x : Flag) => x)(enabled), disabled);");
  const calibration = s.query("pair");
  s.walk(calibration);
  const walked = calibration.stats;
  calibration.readback();
  assert.ok(calibration.stats.steps > walked.steps && calibration.stats.allocatedCells > walked.allocatedCells);
  for (const [option, counter, kind] of [["maxSteps", "steps", "budget"], ["maxCells", "allocatedCells", "resource"]]) {
    const runtime = s.query("pair", { [option]: walked[counter] + 2 });
    s.walk(runtime);
    assert.throws(() => runtime.readback(), error => fails(kind)(error) && error.limit === walked[counter] + 2, option);
  }
});

// n closures over the same n variables: each closure's telescope binds all
// n, so the readback grows as n², and stays within 3.5's bound, a node
// per cell reached, per node rebuilt and two per binding, its DAG within
// the cells and code nodes reached and the bindings.
test("readback size stays within its bound and grows as n² for n closures over n variables", async t => {
  const sizes = [];
  for (const n of [4, 8, 16]) {
    const xs = Array.from({ length: n }, (_, i) => `x${i}`), tuple = Array(n).fill("Unit").join(" and ");
    const closures = xs.map((_, i) => `fun (u${i} : Unit) => typed(${tuple}, (${xs.join(", ")}))`);
    const s = await setup(t, `def scaled := (fun (${xs.join(", ")} : Unit) => typed(${Array(n).fill(`(Unit -> (${tuple}))`).join(" and ")}, (${closures.join(", ")})))(${Array(n).fill("tt").join(", ")});`);
    const runtime = s.query("scaled");
    s.walk(runtime);
    const read = runtime.readback(), stats = runtime.readbackStats;
    assert.equal(stats.bindings, n * n, `${n}: n telescopes of n bindings`);
    assert.ok(stats.writes <= stats.cells + stats.rebuilt + 2 * stats.bindings, `${n}: ${JSON.stringify(stats)}`);
    assert.ok(dagSize(s.kernel, read) <= runtime.stats.snapshotNodes + stats.cells + 2 * stats.bindings, `${n}: DAG`);
    assert.ok(s.same(s.normal(read), s.normal(s.term("scaled"))), `${n}: full normal form`);
    sizes.push(stats.writes);
  }
  for (let i = 1; i < sizes.length; i++) {
    const ratio = sizes[i] / sizes[i - 1];
    assert.ok(ratio > 3 && ratio < 5, `doubling n multiplies the writes by ${ratio}: ${sizes}`);
  }
});

// Mutations that must fail (W1): each changes web/cubical-runtime.mjs at
// one site, in a copy imported as a module of its own, and an oracle that
// the unchanged runtime passes must then fail. The runtime's own walk
// completes under each, so it is the readback that tells. A value mutation
// changes a value's own fields, the node it was made from left as it was.
const runtimeURL = new URL("../web/cubical-runtime.mjs", import.meta.url), runtimeText = await readFile(runtimeURL, "utf8");
async function mutant(edits) {
  let text = runtimeText;
  for (const [from, to] of edits) {
    assert.equal(text.split(from).length, 2, `the mutation site occurs once: ${from}`);
    text = text.replace(from, () => to);
  }
  text = text.replace(/from "\.\/([^"]+)"/g, (_, path) => `from "${new URL(path, runtimeURL).href}"`);
  return (await import(`data:text/javascript,${encodeURIComponent(text)}`)).RuntimeQuery;
}
const mutations = [
  ["swapped pair components", "value", "pair", [["first: delay(c[1]), second: delay(c[2])", "first: delay(c[2]), second: delay(c[1])"]]],
  ["a constructor's index", "value", "flag", [["index: n.payload, instance", "index: n.payload ^ 1, instance"]]],
  ["a constructor's signature", "value", "flag", [["signature: instance.payload, index", "signature: instance.payload + 1, index"]]],
  ["a constructor's instance", "value", "boxed", [["instance: delay(c[0]), args", "instance: this.#delay(c[0], null), args"]]],
  ["a dropped instance", "value", "observed_instance", [["{ tag: \"Type\", node: cell.code, env: this.#pruned(cell.code, env) }", "{ tag: \"Type\" }"]]],
  ["a λ's body", "value", "constant", [["body: c[1], env, domain", "body: this.#node(c[1]).kind === \"Point\" ? c[0] : c[1], env, domain"]]],
  ["a λ's symbol", "value", "pairing", [["symbol: n.payload, body: c[1], env, domain",
    "symbol: this.#node(c[1]).kind === \"App\" ? this.#kernel().symbol(\"mutated\") : n.payload, body: c[1], env, domain"]]],
  ["a λ's environment", "value", "shadowed", [["body: c[1], env, domain: delay(c[0])",
    "body: c[1], env: this.#node(c[1]).kind === \"Var\" ? env?.parent ?? env : env, domain: delay(c[0])"]]],
  ["an eliminator's motive", "heads", "toggle", [["motive: delay(c[0]), clauses", "motive: delay(this.#node(c[1]).children[0]), clauses"]]],
  ["an eliminator's clauses", "heads", "toggle", [["clauses: this.#list(c[1], env) }", "clauses: this.#list(c[1], env).reverse() }"]]],
  ["an η-produced constructor's index", "heads", "successor", [["value = yield* this.#run(this.#delay(f, value.env));",
    "value = yield* this.#run(this.#delay(f, value.env)); if (value.tag === \"Con\") value = { ...value, index: 0 };"]]],
  ["a function replaced by another of its type", "value", "family", [["body: c[1], env, domain",
    "body: this.#node(c[1]).kind === \"Unit\" ? this.#kernel().term(\"Void\") : c[1], env, domain"]]],
  ["a value read instead of its origin", "folded", "projected", [["mode === \"outer\" && !data.has(value.tag))) return", "false)) return"]]],
  ["a data cell inside a non-data origin read by its value", "folded", "projected",
    [["(mode === \"origin\" ||", "(mode === \"origin\" && !data.has(value.tag) ||"]]],
  ["the farthest binding instead of the nearest", "value", "shadowed", [["if (at.symbol === symbol) return at;\n    }\n    return fail(",
    "if (at.symbol === symbol) env = at;\n    }\n    if (env?.symbol === symbol) return env;\n    return fail("]]],
  ["a free variable skipped", "value", "domain_only", [["if (!child) return [];", "if (!child || binder && i === 0) return [];"]]],
  ["domains closed one by one", "typed", "captured", [[
    "for (let i = frames.length; i-- > 0;) term = this.#write(binder(frames[i]).kind, frames[i].symbol, binder(frames[i]).children[0], term);\n"
    + "        frames.forEach((frame, i) => { term = this.#write(level(frame) ? \"LApp\" : \"App\", 0, term, args[i]); });",
    "for (let i = frames.length; i-- > 0;) term = this.#write(level(frames[i]) ? \"LApp\" : \"App\", 0, "
    + "this.#write(binder(frames[i]).kind, frames[i].symbol, binder(frames[i]).children[0], term), args[i]);"]]],
  ["a memo reused across generations", "expired", "flag", [["this.#kernel();\n      this.#epoch++;", "this.#epoch++;"],
    ["kernel = this.#kernel();\n      (kernel", "kernel = this.#image.kernel;\n      (kernel"]]],
];
test("every listed mutation of the runtime or its readback fails an oracle the runtime passes", async t => {
  const s = await setup(t, `
import unat; use unat;
inductive Flag { disabled; enabled; }
inductive Lamp { dark; lit; }
inductive Box(A : U0) { box(a : A); }
def pair := typed(Flag and Flag, (enabled, disabled));
def flag : Flag := enabled;
def boxed := (fun (A : U0) => fun (a : A) => typed(Box(A), box(a)))(Unit, tt);
def observed_instance := (fun (A : U0) => fun (a : A) => typed(Box(A), box(a)))(Unit, tt);
def constant : Unit -> Unit := fun (x : Unit) => tt;
def pairing := fun (x : Unit) => typed(Unit and Unit, (x, tt));
def toggle := fun (f : Flag) => match f return Flag { disabled => enabled; enabled => disabled; };
def successor := fun (n : UNat) => succ(n);
def family : Unit -> U0 := fun (u : Unit) => Unit;
def certPair(u : Unit) : (Unit -> Unit) and Unit := (fun (y : Unit) => tt, tt);
def projected := (fun (x : (Unit -> Unit) and Unit) => typed(Unit and (Unit -> Unit), (tt, x.1)))(certPair(tt));
def domain_only := (fun (A : U0) => fun (u : Unit) => fun (y : A) => y)(Unit);
def captured := (fun (A : U0) => fun (x : A) => fun (u : Unit) => typed(A and A, (x, x)))(Unit, tt);
`);
  s.define("shadowed", shadowed);
  assert.equal(s.kernel.signatures.get("main__Lamp").index, s.kernel.signatures.get("main__Flag").index + 1);
  // An oracle's verdict on a definition, read back by a query of a class:
  // "agrees", "differs", or the readback's failure. The walk must complete.
  const oracles = {
    value: (runtime, name) => s.same(s.normal(runtime.readback()), s.normal(s.term(name))),
    heads: (runtime, name, observed) => observed.every(handle => s.same(s.normal(runtime.readback(handle, { head: true })), s.normal(runtime.readback(handle)))),
    folded: (runtime, name) => s.same(s.folded(runtime.readback(runtime.root, { origins: true })), s.folded(s.term(name))),
    typed: runtime => { new InstructionDriver(s.kernel).check(runtime.readback(), s.graph.judgement(runtime.judgement).type); return true; },
    expired: runtime => {
      runtime.readback();
      new CubicalDeclarationTransaction(s.kernel, s.checker).finish(false);
      try { runtime.readback(); return false; } catch (error) { if (fails("expired")(error)) return true; throw error; }
    },
  };
  const verdict = (Query, oracle, name) => {
    const judgement = s.judgement(name), runtime = s.query(judgement, { origins: oracle === "folded", heads: oracle === "heads" }, Query);
    runtime.judgement = judgement;
    const observed = s.walk(runtime);
    if (name === "observed_instance") runtime.observeNow(runtime.observeNow().instance);
    try { return oracles[oracle](runtime, name, observed) ? "agrees" : "differs"; }
    catch (error) { return `fails: ${error.message}`; }
  };
  for (const [label, oracle, name, edits] of mutations) {
    assert.equal(verdict(RuntimeQuery, oracle, name), "agrees", `${label}: the runtime passes`);
    const Mutant = await mutant(edits), outcome = verdict(Mutant, oracle, name);
    assert.notEqual(outcome, "agrees", `${label}: the mutant passes`);
    // A function replaced by another of its type passes the folding check,
    // which reads its origin; an η-produced head passes R(root) alone.
    if (label === "a function replaced by another of its type") assert.equal(verdict(Mutant, "folded", name), "agrees", label);
    if (label === "an η-produced constructor's index") assert.equal(verdict(Mutant, "value", name), "agrees", label);
    if (label === "domains closed one by one") assert.equal(verdict(Mutant, "value", name), "agrees", label);
  }
});

// The differential's observed heads (tests/runtime-readback-oracle.mjs)
// compare every head the walk observed: an undecided comparison, here the
// pair's and its first part's, whose full normal forms the kernel cannot
// build (K344), is counted, and a later disagreement still fails the
// oracle, as the η-produced index mutation makes successor's.
test("the differential compares every observed head, past an undecided one", async t => {
  const indexed = mutations.find(([label]) => label === "an η-produced constructor's index")[3];
  const source = `import unat; use unat;
def count_into(n, total : UNat) : UNat := match n { zero => total; succ(k) => count_into(k, succ(total)); };
print(evaluate(typed((Unit -> UNat) and (UNat -> UNat), (fun (u : Unit) => count_into(2 * 255, 0), fun (n : UNat) => succ(n)))));`;
  for (const [Query, heads] of [[RuntimeQuery, "deep"], [await mutant(indexed), false]]) {
    const watched = watchReadbacks({ Query });
    try { await checkProgram(t, source, { module }); } finally { watched.restore(); }
    assert.deepEqual(watched.outcomes.map(outcome => [outcome.heads, outcome.undecidedHeads]), [[heads, 2]]);
    assert.equal(disagreements(watched.outcomes).length, heads === false ? 1 : 0);
  }
});
