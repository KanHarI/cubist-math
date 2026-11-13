// The names the driver keeps for the kernel's handles
// (docs/roadmaps/kernel/locally-nameless-kernel.md, section 5.3): entries
// named by name and type, across driver resets and checkpoints; definitions
// and signatures named by their indices; constructors through their
// instances' signatures; a declaration's levels compared as written; and
// decodings kept by the names they show.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { CubicalSyntax } from "../web/cubical-syntax.mjs";
import { CubicalDeclarationTransaction } from "../web/cubical-transaction.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { hiddenIn, pushName } from "../web/cubical-variables.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";

const module = await createCubical();
const unit = { tag: "Unit" }, point = { tag: "Point" }, x = { tag: "Var", name: "x" };
const lam = (name, domain, body) => ({ tag: "Lam", name, domain, body });
function fresh(t, options = {}) {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false, ...options });
  t.after(() => program.dispose());
  return program;
}

test("an entry is found again by its name and its type, across drivers, and never one in scope", async t => {
  const program = fresh(t), { kernel, checker } = program;
  const derive = (term, context) => checker.checkSyntax(term, null, new Map(context), new Map());
  const first = derive(x, [["x", unit]]), graph = checker.driver.graph;
  const [entry] = graph.judgement(first.judgement).context;
  assert.equal(kernel.entryNames.name(entry), "x");
  // A new driver, as each inspection and definition starts, binds x at Unit
  // to the same entry, and the kernel answers the repeated derivation from
  // its memo: no judgement is added.
  kernel.instructionDriver = null;
  const count = checker.driver.graph.count, again = derive(x, [["x", unit]]);
  assert.equal(again.judgement, first.judgement);
  assert.equal(checker.driver.graph.count, count);
  // The scope that holds the entry already gets another for a binder of the
  // same name and type: two variables are never one.
  const driver = checker.driver, type = driver.asType(driver.infer(checker.syntax.encode(unit)));
  const symbol = kernel.symbol("x"), scope = new Map([["dims", 0n], [symbol, entry]]);
  assert.equal(driver.bind(symbol, type), entry);
  const inner = driver.bind(symbol, type, scope);
  assert.notEqual(inner, entry);
  assert.equal(kernel.entryNames.name(inner), "x");
  assert.notEqual(kernel.entryNames.spelled(inner), "x", "spelled apart from the live entry");
  // A fresh entry is always new, and the driver never asks the kernel to
  // reuse one by its symbol: two fresh entries at one type are two. A binder
  // of its name takes none.
  assert.notEqual(driver.freshEntry(type, "x"), driver.freshEntry(type, "x"));
  const made = driver.freshEntry(type, "w");
  assert.notEqual(driver.bind(kernel.symbol("w"), type), made);
});

// The entries the λ and Π judgements of a derivation discharge, outermost first.
const discharged = (graph, id) => {
  const judgement = graph.judgement(id);
  return [...["lambda", "pi"].includes(judgement.rule) ? [judgement.entry] : [], ...judgement.premises.flatMap(premise => discharged(graph, premise))];
};

test("λ (x : A). λ (x : A). x binds two entries, the inner x the inner binder's", async t => {
  const program = fresh(t), { kernel, checker } = program, driver = checker.driver;
  const term = lam("x", unit, lam("x", unit, x));
  const id = driver.infer(checker.syntax.encode(term)), judgement = driver.graph.judgement(id);
  // The inner binder's narrowed scope hides the outer entry, which its own
  // name could take: it takes another.
  const [outer, inner] = discharged(driver.graph, id);
  assert.notEqual(outer, inner);
  assert.deepEqual([outer, inner].map(entry => kernel.entryNames.name(entry)), ["x", "x"]);
  const second = checker.syntax.encode(lam("a", unit, lam("b", unit, { tag: "Var", name: "b" })));
  const first = checker.syntax.encode(lam("a", unit, lam("b", unit, { tag: "Var", name: "a" })));
  assert.ok(kernel.alphaEqual(judgement.term, second));
  assert.ok(!kernel.alphaEqual(judgement.term, first));
  // A third binder of the name takes neither: the outermost entry, shadowed,
  // is still the scope's.
  const three = discharged(driver.graph, driver.infer(checker.syntax.encode(lam("x", unit, term))));
  assert.equal(new Set(three).size, 3);
});

test("a binder never takes an entry its scope holds, even one a later variable depends on", async t => {
  // λ (x : A). λ (y : B(x)). λ (x : A). y: the innermost binder's scope keeps
  // y, whose entry depends on the outer x's. Were the inner x to take that
  // entry, its λ would discharge it while y's still depends on it, which the
  // kernel refuses, as main's reuse by symbol did. A fourth binder, x again,
  // takes neither the third's entry, which it shadows, nor the first's, which
  // the third shadowed: with the kernel sharing syntax and without.
  for (const shareSyntax of [true, false]) {
    const program = fresh(t, { optimizations: { shareSyntax } }), { kernel, checker } = program, driver = checker.driver, syntax = checker.syntax;
    const A = { tag: "Var", name: "A" }, B = { tag: "Var", name: "B" }, Bx = { tag: "App", fn: B, arg: x }, u0 = { tag: "U", level: 0 };
    const encode = (term, scope) => syntax.encode(term, new Map(), scope);
    const scopeOf = context => driver.scopeOf(context.map(([name, type]) => [kernel.symbol(name), type]), 0n, encode);
    const context = [["A", u0], ["B", { tag: "Pi", name: "_", domain: A, body: u0 }]], scope = scopeOf(context);
    const pi = (name, domain, body) => ({ tag: "Pi", name, domain, body });
    for (const inner of [["x"], ["x", "x"]]) {
      const term = lam("x", A, lam("y", Bx, inner.reduceRight((body, name) => lam(name, A, body), { tag: "Var", name: "y" })));
      const type = pi("x", A, pi("y", Bx, inner.reduceRight(body => pi("z", A, body), Bx)));
      const entries = discharged(driver.graph, driver.checkIn(encode(term, scope), encode(type, scope), scope));
      assert.equal(new Set(entries).size, entries.length, `${entries.length} binders`);
      assert.deepEqual(entries.map(entry => kernel.entryNames.name(entry)), ["x", "y", ...inner]);
    }
    // So in a context whose second x shadows the first, on which y depends:
    // λ (x : A). y takes neither x's entry.
    const held = scopeOf([...context, ["x", A], ["y", Bx], ["x", A]]);
    const [entry] = discharged(driver.graph, driver.derive(encode(lam("x", A, { tag: "Var", name: "y" }), held), held));
    assert.ok(![...held.values(), ...hiddenIn(held)].includes(entry));
  }
});

test("a type equal up to a dimension's name binds the same entry", async t => {
  // Path(0; U0, Unit, Unit) and Path(1; U0, Unit, Unit) are two handles the
  // kernel calls alpha-equal; one entry for x at both keeps a Transitivity
  // that joins judgements derived under each.
  const program = fresh(t), { kernel, checker } = program, driver = checker.driver, g = driver.graph;
  const u0 = checker.syntax.encode({ tag: "U", level: 0 }), at = dimension => kernel.term("Path", dimension, u0, checker.syntax.encode(unit), checker.syntax.encode(unit));
  assert.notEqual(at(0), at(1));
  const typed = dimension => driver.asType(driver.derive(at(dimension), new Map([["dims", 0n]])));
  const entries = [0, 1].map(dimension => driver.bind(kernel.symbol("x"), typed(dimension)));
  assert.equal(entries[0], entries[1]);
  const [left, right] = [0, 1].map(dimension => {
    const scope = driver.contextScope([[kernel.symbol("x"), at(dimension)]], 0n);
    return g.refl(driver.derive(checker.syntax.encode(x, new Map(), scope), scope));
  });
  assert.ok(g.transitivity(left, right));
});

test("an entry found again after a reset is the one kept judgements use, whatever was made since", async t => {
  // x at Path(1; …) is the entry made for x at Path(0; …). A λ of x in that
  // scope takes another, made at Path(1; …)'s own handle. After a reset, x
  // at Path(1; …) is the first entry again, the first made for its name and
  // type that the scope does not hold, not the one made at the same handle,
  // and a Transitivity with the judgement kept from before the reset meets.
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax;
  const u0 = syntax.encode({ tag: "U", level: 0 }), at = dimension => kernel.term("Path", dimension, u0, syntax.encode(unit), syntax.encode(unit));
  // A term in a context: encoded against the context's scope, made first.
  const context = dimension => [[kernel.symbol("x"), at(dimension)]];
  const infer = (term, context) => {
    const scope = checker.driver.contextScope(context, 0n);
    return checker.driver.derive(syntax.encode(term, new Map(), scope), scope);
  };
  const contextOf = id => checker.driver.graph.judgement(id).context;
  const first = infer(x, context(0)), kept = infer(x, context(1));
  assert.deepEqual(contextOf(kept), contextOf(first));
  const shadowing = infer(lam("x", syntax.decode(at(1), new Map(), null, null), x), context(1));
  assert.ok(!contextOf(kept).includes(discharged(checker.driver.graph, shadowing)[0]));
  kernel.instructionDriver = null;
  const g = checker.driver.graph, again = infer(x, context(1));
  assert.deepEqual(g.judgement(again).context, g.judgement(kept).context);
  assert.ok(g.transitivity(g.refl(kept), g.refl(again)));
});

test("an entry's name lives as long as the entry: across inspections, and to its checkpoint", async t => {
  const program = fresh(t), { kernel, checker } = program;
  const result = await program.check("def identity(y : Unit) : Unit := y;", "main");
  assert.deepEqual(result.gaps, []);
  // An open judgement retained across an inspection, which drops the driver,
  // keeps its variable's name; deriving again with that name and type reuses
  // its entry, so the next instruction combines with it.
  const open = checker.checkView(x, null, [["x", unit]]);
  const [entry] = checker.driver.graph.judgement(open.judgement).context;
  program.inspect("main__identity");
  assert.equal(kernel.entryNames.name(entry), "x");
  const again = checker.checkView(x, null, [["x", unit]]), g = checker.driver.graph;
  assert.deepEqual(g.judgement(again.judgement).context, [entry]);
  assert.ok(g.transitivity(g.refl(open.judgement), g.refl(again.judgement)));
  // An entry made after a checkpoint loses its name at the checkpoint's
  // rollback and at its commit; one made before keeps it.
  for (const accept of [false, true]) {
    const transaction = new CubicalDeclarationTransaction(kernel, checker);
    const made = checker.checkView({ tag: "Var", name: "z" }, null, [["z", unit]]);
    const [late] = checker.driver.graph.judgement(made.judgement).context;
    assert.ok(late > entry);
    transaction.finish(accept);
    assert.throws(() => kernel.entryNames.name(late), /no context entry/);
    assert.equal(kernel.entryNames.name(entry), "x");
  }
});

test("a type handle met in a rolled-back declaration is forgotten with it", async t => {
  // Path(1; …), made after the checkpoint, binds x at the entry made at
  // Path(0; …). The rollback frees its handle, and the next node made takes
  // it: x at that type, Unit → Unit, is another entry.
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, symbol = kernel.symbol("x");
  const u0 = syntax.encode({ tag: "U", level: 0 }), at = dimension => kernel.term("Path", dimension, u0, syntax.encode(unit), syntax.encode(unit));
  const contextOf = type => {
    const scope = checker.driver.contextScope([[symbol, type]], 0n);
    return checker.driver.graph.judgement(checker.driver.derive(syntax.encode(x, new Map(), scope), scope)).context;
  };
  const [entry] = contextOf(at(0));
  const transaction = new CubicalDeclarationTransaction(kernel, checker), transient = at(1);
  assert.deepEqual(contextOf(transient), [entry]);
  transaction.finish(false);
  const function_ = kernel.term("Pi", 0, syntax.encode(unit), syntax.encode(unit));
  assert.equal(function_, transient, "the freed handle is made again");
  assert.notDeepEqual(contextOf(function_), [entry]);
});

test("definitions are named by index: shared or not, relocated, and freed at a rollback", async t => {
  for (const shareSyntax of [true, false]) {
    const program = fresh(t, { optimizations: { shareSyntax } }), { kernel, checker } = program;
    const result = await program.check("def one : Unit := tt; def two : Unit := one;", "main");
    assert.deepEqual(result.gaps, []);
    // The committed reference was relocated; it and a second node for the
    // same definition, which the kernel makes apart without sharing, decode
    // to its name.
    const reference = kernel.definitions.get("main__one"), index = kernel.node(reference).payload;
    const copy = kernel.term("DefRef", index);
    assert.equal(copy === reference, shareSyntax);
    for (const handle of [reference, copy]) assert.deepEqual(checker.syntax.decode(handle, new Map(), null, null), { tag: "DefRef", name: "main__one" });
    // A definition rolled back leaves no name, and the next one at its index
    // is named by its own.
    const transaction = new CubicalDeclarationTransaction(kernel, checker);
    const ghost = checker.define("main__ghost", point, unit);
    const freed = kernel.node(kernel.definitions.get("main__ghost")).payload;
    assert.equal(ghost.name, "main__ghost");
    transaction.finish(false);
    assert.equal(kernel.definitionNames.has(freed), false);
    const next = new CubicalDeclarationTransaction(kernel, checker);
    checker.define("main__real", point, unit);
    next.finish(true);
    const real = kernel.definitions.get("main__real");
    assert.equal(kernel.node(real).payload, freed);
    assert.deepEqual(checker.syntax.decode(real, new Map(), null, null), { tag: "DefRef", name: "main__real" });
  }
});

test("signatures are named by index, and constructors through their instances", async t => {
  const program = fresh(t), { kernel, checker } = program;
  // Two constructors of number 0, of two signatures: each named by its own.
  const result = await program.check(`inductive A {
  a;
}

inductive B {
  b;
}

def pick(s : B) : A := match s {
    b => a;
  };
def picked : A := pick(b);
`, "main");
  assert.deepEqual(result.gaps, []);
  const value = name => checker.syntax.decode(kernel.definition(kernel.definitions.get(name)).value, new Map(), null, null);
  const constructors = [];
  const visit = term => {
    if (!term || typeof term !== "object") return;
    if (term.tag === "Con") constructors.push([term.name, term.sort.signature]);
    Object.values(term).forEach(visit);
  };
  visit(value("main__pick"));
  visit(value("main__picked"));
  assert.deepEqual(new Map(constructors), new Map([["a", "main__A"], ["b", "main__B"]]));
  // A signature rolled back frees its index and its name with it; the next
  // signature admitted there is named by its own.
  const index = () => kernel.signatures.size;
  const transaction = new CubicalDeclarationTransaction(kernel, checker);
  const ghost = checker.admitSignature({ name: "main__Ghost", constructors: [{ name: "g", type: { tag: "Var", name: "main__Ghost" } }] });
  transaction.finish(false);
  assert.equal(kernel.signatureRecords.has(ghost.index), false);
  const next = new CubicalDeclarationTransaction(kernel, checker);
  const real = checker.admitSignature({ name: "main__Real", constructors: [{ name: "r", type: { tag: "Var", name: "main__Real" } }] });
  next.finish(true);
  assert.equal(real.index, ghost.index);
  assert.equal(checker.syntax.signatureRecord(real.index).name, "main__Real");
  assert.equal(index(), 3);
});

test("a declaration's universe levels are compared as written, for E514", async t => {
  const { result } = await checkProgram(t, `inductive Bad(U < UU0, A : U) : U0 {
  pack(x : A);
}
`, { module });
  const failure = result.outputs.find(output => output.name === "Bad");
  assert.equal(failure.code, "E514");
  assert.match(failure.reason, /pack's argument x lives in a universe above Bad's declared one/);
});

// A binder the kernel built, with no name, binds entries of its own node
// (binderKey). Encoding the same node later with a source name names it for
// display, and must not change the name its entries are chosen by: in
// A : U0, B : A → U0, x : A, y : B(x), the unnamed λ (_ : A). y derived, then
// written λ (x : A). y, derives again with one more live dimension as a
// fresh driver derives it, not at x's entry, on which y's depends.
test("a binder's key for its entries stays what it was when a source name names it later", async t => {
  const program = fresh(t), { kernel, checker } = program, driver = checker.driver, syntax = checker.syntax;
  const encode = (term, scope) => syntax.encode(term, new Map(), scope);
  const A = { tag: "Var", name: "A" }, B = { tag: "Var", name: "B" }, y = { tag: "Var", name: "y" };
  const context = [["A", { tag: "U", level: 0 }], ["B", { tag: "Pi", name: "_", domain: A, body: { tag: "U", level: 0 } }],
    ["x", A], ["y", { tag: "App", fn: B, arg: x }]];
  const scopeOf = (driver, dimensions) => driver.scopeOf(context.map(([name, type]) => [kernel.symbol(name), type]), dimensions, encode);
  const scope = scopeOf(driver, 0n);
  const unnamed = kernel.term("Lam", 0, encode(A, scope), encode(y, scope));
  assert.ok(!kernel.binderNames.has(unnamed));
  driver.derive(unnamed, scope);
  assert.equal(encode(lam("x", A, y), scope), unnamed, "the source term is the same node");
  const warm = driver.graph.judgement(driver.derive(unnamed, scopeOf(driver, 1n)));
  const other = new InstructionDriver(kernel), cold = other.graph.judgement(other.derive(unnamed, scopeOf(other, 1n)));
  assert.equal(warm.term, cold.term);
  assert.deepEqual(warm.context, cold.context);
});

// A node's decoding depends on the names its entries and its loose indices
// take (CubicalSyntax.decodeNode), and is one object wherever they are
// named alike, found again by the node in the context it is decoded in: in
// A : U0, a : A, λ (z : A). a(z) shown with a named a or b, and its body
// under a binder named p, q or z.
test("a decoding is shared where its node is named alike, and its own where it is named otherwise", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax;
  const A = { tag: "Var", name: "A" }, a = { tag: "Var", name: "a" }, z = { tag: "Var", name: "z" };
  const context = [["A", { tag: "U", level: 0 }], ["a", A]].map(([name, type]) => [kernel.symbol(name), type]);
  const scope = checker.driver.scopeOf(context, 0n, (type, inner) => syntax.encode(type, new Map(), inner));
  const entry = scope.get(kernel.symbol("a"));
  const term = syntax.encode(lam("z", A, { tag: "App", fn: a, arg: z }), new Map(), scope), body = kernel.node(term).children[1];
  // Each naming a map of its own, as each scope's is.
  const as = name => new Map([[entry, name]]);
  const decode = (naming, handle = term, names = null) => syntax.decode(handle, new Map(), names, naming);
  const first = decode(as("a")), other = decode(as("b"));
  assert.deepEqual([first.body.fn.name, other.body.fn.name], ["a", "b"]);
  assert.equal(decode(as("a")), first, "named alike, one decoding");
  assert.equal(decode(as("b")), other);
  assert.equal(other.domain, first.domain, "the part that mentions no entry named otherwise is shared");
  const [p, q] = ["p", "q"].map(name => decode(as("a"), body, pushName(name, null)));
  assert.deepEqual([p.arg.name, q.arg.name], ["p", "q"]);
  assert.equal(decode(as("a"), body, pushName("z", null)), first.body, "the body under its binder's name, as the λ shows it");
});

// A binder the kernel built is shown unnamed until an encoding names it
// (web/cubical-kernel.mjs, BinderNames). Naming it as it was shown, or x,
// changes no decoding: one that shows it by its own name is kept, and one
// in which a binder showed a variant is made anew, as #354 made it, to the
// same text; naming a binder shown by two names by one of them drops the
// decodings that show a binder unnamed, and keeps those of named binders
// alone.
test("a binder named as it was shown keeps its decodings, and one named otherwise drops those that show a binder unnamed", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, names = kernel.binderNames;
  const decode = (handle, chain = null) => syntax.decode(handle, new Map(), chain, null);
  const unitType = syntax.encode(unit), outer = kernel.term("Bound", 1);
  // λ (x : Unit). λ (x1 : Unit). x, Π (x : Unit). Π (x1 : Unit). x and
  // Σ (x : Unit). Unit, all five binders unnamed.
  const lambda = kernel.term("Lam", 0, unitType, kernel.term("Lam", 0, unitType, outer));
  const pi = kernel.term("Pi", 0, unitType, kernel.term("Pi", 0, unitType, outer));
  const sigma = kernel.term("Sigma", 0, unitType, unitType);
  const [inner, piInner] = [lambda, pi].map(handle => kernel.node(handle).children[1]);
  for (const handle of [lambda, inner, pi, piInner, sigma]) assert.ok(!names.has(handle));
  const named = syntax.encode(lam("w", unit, { tag: "Var", name: "w" }));
  const shown = term => [term.name, term.body.name, term.body.body.name];
  const [l, p, s, w] = [decode(lambda), decode(pi), decode(sigma), decode(named)];
  assert.deepEqual([shown(l), shown(p), s.name], [["x", "x1", "x"], ["x", "x1", "x"], "x"]);
  // The inner λ alone, under a binder q, is shown by a second name.
  const q = decode(inner, pushName("q", null));
  assert.deepEqual([q.name, q.body.name], ["x", "q"]);
  names.set(piInner, "x1");
  names.set(pi, "x");
  names.set(sigma, "x");
  assert.equal(decode(sigma), s, "named x, as shown: the decoding is kept");
  assert.deepEqual([shown(decode(pi)), shown(decode(lambda))], [["x", "x1", "x"], ["x", "x1", "x"]]);
  names.set(inner, "x1");
  const again = decode(inner, pushName("q", null));
  assert.deepEqual([again.name, again.body.name], ["x1", "q"], "the decoding that showed it as x is dropped");
  assert.equal(decode(named), w, "a decoding of named binders alone is kept");
  assert.deepEqual(shown(decode(lambda)), ["x", "x1", "x"]);
});

// A binder's variant reads the stem of its own name as the stems stand,
// and records the variant's (web/cubical-variables.mjs, shownBinderName);
// a decoding that made one is made anew, reading and recording them again,
// wherever #354's codec decoded anew (CubicalSyntax.tierOf, VARIANT). From
// the first review of this change: a binder x1 shown under an outer x1 is
// x1_1; an unnamed binder shown under x as x1 makes x1 a variant of x; named
// z, it moves #354's epoch, and the first shows as x2, kept or decoded by a
// codec of its own, as on #354.
test("a binder's variant reads the stems again where #354 decoded anew", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, names = kernel.binderNames;
  const unitType = syntax.encode(unit), outer = kernel.term("Bound", 1);
  const named = kernel.term("Lam", 0, unitType, outer), unnamed = kernel.term("Pi", 0, unitType, outer);
  for (const handle of [named, unnamed]) assert.ok(!names.has(handle));
  names.set(named, "x1");
  const under = (codec, handle, name) => codec.decode(handle, new Map(), pushName(name, null), null).name;
  assert.deepEqual([under(syntax, named, "x1"), under(syntax, unnamed, "x")], ["x1_1", "x1"]);
  names.set(unnamed, "z");
  assert.deepEqual([under(syntax, named, "x1"), under(new CubicalSyntax(kernel), named, "x1")], ["x2", "x2"]);
});

// Between #354's moves a decoding is kept as #354 kept it, though the stems
// it read have changed since: a binder y1 shown under y1 is y1_1; a named y
// shown under y as y1 then makes y1 a variant of y; with nothing named
// since, the first is still y1_1 as kept, where a codec of its own, as a
// session that had not shown it, reads y2.
test("a binder's variant is kept between #354's moves, as #354 kept it", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, names = kernel.binderNames;
  const unitType = syntax.encode(unit), outer = kernel.term("Bound", 1);
  const first = kernel.term("Lam", 0, unitType, outer), second = kernel.term("Sigma", 0, unitType, outer);
  names.set(first, "y1");
  names.set(second, "y");
  const under = (codec, handle, name) => codec.decode(handle, new Map(), pushName(name, null), null).name;
  assert.deepEqual([under(syntax, first, "y1"), under(syntax, second, "y")], ["y1_1", "y1"]);
  assert.deepEqual([under(syntax, first, "y1"), under(new CubicalSyntax(kernel), first, "y1")], ["y1_1", "y2"]);
});

// The names a node's entries take are one key, whatever characters they
// hold (CubicalSyntax.shownEntries). From the first review of this change:
// a(c), its entries named a\0b and c, then a and b\0c.
test("entries named apart are decoded apart, whatever characters their names hold", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax;
  const A = { tag: "Var", name: "A" };
  const context = [["A", { tag: "U", level: 0 }], ["a", A], ["c", A]].map(([name, type]) => [kernel.symbol(name), type]);
  const scope = checker.driver.scopeOf(context, 0n, (type, inner) => syntax.encode(type, new Map(), inner));
  const [a, c] = ["a", "c"].map(name => scope.get(kernel.symbol(name)));
  const term = syntax.encode({ tag: "App", fn: { tag: "Var", name: "a" }, arg: { tag: "Var", name: "c" } }, new Map(), scope);
  const shown = (first, second) => {
    const decoded = syntax.decode(term, new Map(), null, new Map([[a, first], [c, second]]));
    return [decoded.fn.name, decoded.arg.name];
  };
  assert.deepEqual(shown("a\u0000b", "c"), ["a\u0000b", "c"]);
  assert.deepEqual(shown("a", "b\u0000c"), ["a", "b\u0000c"]);
});

// The display renames a variant spelling to its stem, as the stems stand.
// From the second review of this change: a binder x'1 decoded under an
// outer x'1 is x'1_1; a fresh x entry is then spelled x'1, a variant of x;
// and the first check of λ (x'1 : Unit). x'1 shows it by x, as on #354.
test("the display renames a variant spelling to its stem, whatever a binder read before", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, driver = checker.driver;
  const unitType = syntax.encode(unit), binder = kernel.term("Lam", 0, unitType, kernel.term("Bound", 1));
  kernel.binderNames.set(binder, "x'1");
  assert.equal(syntax.decode(binder, new Map(), pushName("x'1", null), null).name, "x'1_1");
  const entry = driver.freshEntry(driver.asType(driver.infer(unitType)), "x");
  assert.equal(kernel.entryNames.spelled(entry), "x'1");
  const view = checker.checkSyntax(lam("x'1", unit, { tag: "Var", name: "x'1" }), null, new Map(), new Map());
  assert.equal(checker.displayText(view.term, new Map()), "fun (x : Unit) => x");
});

// A fresh entry's spelling records its stem over a binder variant's, as on
// #354. From the second review of this change: a binder x' shown under x'
// as x'1 makes x'1 a variant of x'; a binder x'1 shown under x'1 is then
// x'2; a fresh x spelled x'1 makes x'1 a variant of x; with nothing named
// since, the second is x'2 as kept, where a codec of its own reads x1.
test("a fresh entry's spelling records its stem over a binder variant's", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, driver = checker.driver;
  const unitType = syntax.encode(unit), outer = kernel.term("Bound", 1);
  const first = kernel.term("Sigma", 0, unitType, outer), second = kernel.term("Lam", 0, unitType, outer);
  kernel.binderNames.set(first, "x'");
  kernel.binderNames.set(second, "x'1");
  const under = (codec, handle, name) => codec.decode(handle, new Map(), pushName(name, null), null).name;
  assert.deepEqual([under(syntax, first, "x'"), under(syntax, second, "x'1")], ["x'1", "x'2"]);
  const entry = driver.freshEntry(driver.asType(driver.infer(unitType)), "x");
  assert.equal(kernel.entryNames.spelled(entry), "x'1");
  assert.deepEqual([under(syntax, second, "x'1"), under(new CubicalSyntax(kernel), second, "x'1")], ["x'2", "x1"]);
});

// The display's renaming of made-up names reads the stems as they stand,
// and keeps what it made of a decoding until #354's codec would have made
// the decoding anew (BinderNames.renamings), as the codec keeps decodings
// longer. From the third review of this change: λ (x'1 : Unit). x'1,
// settled, shown while x'1 is no variant, its entry rolled back; then a
// fresh x spelled x'1, a variant of x; and a binder shown unnamed before,
// named. Shown again, the λ reads as a session that met the variant first
// shows it, as on #354: fun (x : Unit) => x.
function renamedAfter(t, name) {
  const lambda = lam("x'1", unit, { tag: "Var", name: "x'1" });
  const session = warm => {
    const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax;
    const unitType = syntax.encode(unit), type = () => checker.driver.asType(checker.driver.infer(unitType));
    const shown = () => checker.displayText(checker.checkSyntax(lambda, null, new Map(), new Map()).term, new Map());
    checker.driver.freshEntry(type(), "y");
    let unnamed = 0, before = null;
    if (warm) {
      syntax.encode(lambda);
      unnamed = kernel.term("Sigma", 0, unitType, unitType);
      assert.ok(!kernel.binderNames.has(unnamed));
      syntax.decode(unnamed, new Map(), null, null);
      new CubicalDeclarationTransaction(kernel, checker).finish(false);
      const transaction = new CubicalDeclarationTransaction(kernel, checker);
      before = shown();
      transaction.finish(false);
    }
    checker.driver.freshEntry(type(), "x");
    assert.equal(kernel.entryNames.stems.get("x'1"), "x");
    if (warm) kernel.binderNames.set(unnamed, name);
    return [before, shown()];
  };
  return { cold: session(false), warm: session(true) };
}
test("a view after a binder shown unnamed is named reads the stems again", async t => {
  const { cold, warm } = renamedAfter(t, "z");
  assert.deepEqual([cold[1], warm], ["fun (x : Unit) => x", ["fun (x' : Unit) => x'", "fun (x : Unit) => x"]]);
});
// The same where the binder is named x, its name unnamed: the codec keeps
// the decodings that show it, and #354's made them anew.
test("a view after a binder shown unnamed is named as it was shown reads the stems again", async t => {
  const { cold, warm } = renamedAfter(t, "x");
  assert.deepEqual([cold[1], warm], ["fun (x : Unit) => x", ["fun (x' : Unit) => x'", "fun (x : Unit) => x"]]);
});

// A decoding made anew records its variants again before the display reads
// the stems, as on #354. From the fourth review of this change: λ (x' :
// Unit). λ (x' : Unit). x', the outer x', shows as fun (x', x'1 : Unit) =>
// x', its inner binder's x'1 a variant of x'; a fresh x spelled x'1 makes
// x'1 a variant of x; an unnamed Σ shown before is named z; and the λ shown
// again records x'1 as a variant of x' and shows as before.
test("a view decoded anew records its variants again before the display reads them", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, driver = checker.driver;
  const unitType = syntax.encode(unit), type = () => driver.asType(driver.infer(unitType));
  const shown = term => checker.displayText(checker.checkSyntax(term, null, new Map(), new Map()).term, new Map());
  driver.freshEntry(type(), "y");
  const inner = kernel.term("Lam", 0, unitType, kernel.term("Bound", 1));
  kernel.binderNames.set(inner, "x'");
  const nested = lam("x'", unit, lam("w", unit, { tag: "Var", name: "x'" }));
  syntax.encode(nested);
  const sigma = kernel.term("Sigma", 0, unitType, unitType);
  syntax.decode(sigma, new Map(), null, null);
  new CubicalDeclarationTransaction(kernel, checker).finish(false);
  const transaction = new CubicalDeclarationTransaction(kernel, checker);
  assert.deepEqual([shown(nested), kernel.entryNames.stems.get("x'1")], ["fun (x', x'1 : Unit) => x'", "x'"]);
  transaction.finish(false);
  const entry = checker.driver.freshEntry(type(), "x");
  assert.deepEqual([kernel.entryNames.spelled(entry), kernel.entryNames.stems.get("x'1")], ["x'1", "x"]);
  kernel.binderNames.set(sigma, "z");
  assert.deepEqual([shown(nested), kernel.entryNames.stems.get("x'1")], ["fun (x', x'1 : Unit) => x'", "x'"]);
});

// The first review's sequence as a display shows it: λ (x1 : Unit). λ (x1 :
// Unit). x1, the outer, shows as fun (x, x1_ : Unit) => x; an unnamed Π
// shown under x as x1, named z, and it shows as fun (x, x1 : Unit) => x, as
// on #354.
test("a display decoded anew after a variant's stem changed shows the new stem's variant", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, names = kernel.binderNames;
  const unitType = syntax.encode(unit), outer = kernel.term("Bound", 1);
  const named = kernel.term("Lam", 0, unitType, outer), unnamed = kernel.term("Pi", 0, unitType, outer);
  names.set(named, "x1");
  const wrapped = kernel.term("Lam", 0, unitType, named);
  names.set(wrapped, "x1");
  const text = () => checker.displayText(syntax.decode(wrapped, new Map(), null, null), new Map());
  assert.equal(text(), "fun (x, x1_ : Unit) => x");
  assert.equal(syntax.decode(unnamed, new Map(), pushName("x", null), null).name, "x1");
  names.set(unnamed, "z");
  assert.equal(text(), "fun (x, x1 : Unit) => x");
});

// A commit that relocates a binder's name onto the handle of a binder shown
// unnamed moved #354's epoch (BinderNames.placed). From the fourth review of
// this change: λ (x'1 : Unit). x'1 shown while x'1 is no variant; a fresh x
// spelled x'1; then, in a declaration, a transient unnamed Σ shown and
// f := λ (w : Unit). tt defined and committed, its λ relocated onto the Σ's
// handle. The λ (x'1 : Unit). x'1 shows as #354 shows it.
test("a name a commit relocates onto a binder shown unnamed reads the stems again", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax;
  const unitType = syntax.encode(unit), type = () => checker.driver.asType(checker.driver.infer(unitType));
  const identity = lam("x'1", unit, { tag: "Var", name: "x'1" });
  const shown = () => checker.displayText(checker.checkSyntax(identity, null, new Map(), new Map()).term, new Map());
  checker.driver.freshEntry(type(), "y");
  syntax.encode(identity);
  syntax.encode(point);
  new CubicalDeclarationTransaction(kernel, checker).finish(false);
  let transaction = new CubicalDeclarationTransaction(kernel, checker);
  assert.equal(shown(), "fun (x' : Unit) => x'");
  transaction.finish(false);
  assert.equal(kernel.entryNames.spelled(checker.driver.freshEntry(type(), "x")), "x'1");
  transaction = new CubicalDeclarationTransaction(kernel, checker);
  const sigma = kernel.term("Sigma", 0, unitType, unitType);
  syntax.decode(sigma, new Map(), null, null);
  checker.define("main__f", lam("w", unit, point), { tag: "Pi", name: "w", domain: unit, body: unit });
  transaction.finish(true);
  const value = kernel.definition(kernel.definitions.get("main__f")).value;
  assert.deepEqual([value, kernel.binderNames.get(value)], [sigma, "w"], "f's λ relocated onto the Σ's handle");
  assert.equal(shown(), "fun (x : Unit) => x");
});

// The same with the Π named x1, as it was shown: the codec's epoch skips
// the naming, and #354's moved, so the λ, whose part showed a variant, is
// decoded anew to fun (x, x1 : Unit) => x, as on #354.
test("a display decoded anew after a binder is named as shown shows the new stem's variant", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, names = kernel.binderNames;
  const unitType = syntax.encode(unit), outer = kernel.term("Bound", 1);
  const named = kernel.term("Lam", 0, unitType, outer), unnamed = kernel.term("Pi", 0, unitType, outer);
  names.set(named, "x1");
  const wrapped = kernel.term("Lam", 0, unitType, named);
  names.set(wrapped, "x1");
  const text = () => checker.displayText(syntax.decode(wrapped, new Map(), null, null), new Map());
  assert.equal(text(), "fun (x, x1_ : Unit) => x");
  assert.equal(syntax.decode(unnamed, new Map(), pushName("x", null), null).name, "x1");
  const epoch = names.epoch;
  names.set(unnamed, "x1");
  assert.equal(names.epoch, epoch, "the codec's epoch skips a naming as shown");
  assert.equal(text(), "fun (x, x1 : Unit) => x");
});

// A variant decoding that still holds after #354's epoch moved is kept,
// the same object (CubicalSyntax.holds): #354 decoded it anew to the same
// text and recorded no stem it had not. λ (x1 : Unit). λ (x1 : Unit). x1,
// the outer, shows as fun (x, x1_ : Unit) => x, its inner binder's x1_1 a
// variant of x1; an unnamed Σ shown, then named z; and the λ is the decoding
// it was, as #354 shows it.
test("a variant decoding that still holds after #354's epoch moved is kept", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, names = kernel.binderNames;
  const unitType = syntax.encode(unit);
  const named = kernel.term("Lam", 0, unitType, kernel.term("Bound", 1));
  names.set(named, "x1");
  const wrapped = kernel.term("Lam", 0, unitType, named);
  names.set(wrapped, "x1");
  const sigma = kernel.term("Sigma", 0, unitType, unitType);
  const decode = handle => syntax.decode(handle, new Map(), null, null);
  const first = decode(wrapped);
  assert.deepEqual([checker.displayText(first, new Map()), first.body.name], ["fun (x, x1_ : Unit) => x", "x1_1"]);
  decode(sigma);
  const renamings = names.renamings;
  names.set(sigma, "z");
  assert.equal(names.renamings, renamings + 1, "#354's epoch moved");
  const again = decode(wrapped);
  assert.equal(again, first, "the decoding holds, and is kept");
  assert.equal(checker.displayText(again, new Map()), "fun (x, x1_ : Unit) => x");
});

// A decoding that shows a variant and a binder with no name yet holds only
// while the binders' names have not moved on, as a provisional one: λ (x1 :
// Unit). (λ (x1 : Unit). x1, the outer)(λ (_ : Unit). _), its inner binder
// x1_1 and the last unnamed, x; named w, the last shows as w, as on #354.
test("a variant decoding that shows a binder with no name yet goes when that binder is named otherwise", async t => {
  const program = fresh(t), { kernel, checker } = program, syntax = checker.syntax, names = kernel.binderNames;
  const unitType = syntax.encode(unit);
  const named = kernel.term("Lam", 0, unitType, kernel.term("Bound", 1));
  names.set(named, "x1");
  const unnamed = kernel.term("Lam", 0, unitType, kernel.term("Bound", 0));
  assert.ok(!names.has(unnamed));
  const outer = kernel.term("Lam", 0, unitType, kernel.term("App", 0, named, unnamed));
  names.set(outer, "x1");
  const shown = () => { const term = syntax.decode(outer, new Map(), null, null); return [term.body.fn.name, term.body.arg.name]; };
  assert.deepEqual(shown(), ["x1_1", "x"]);
  names.set(unnamed, "w");
  assert.deepEqual(shown(), ["x1_1", "w"]);
});
