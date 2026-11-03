// The names the driver keeps for the kernel's handles
// (docs/roadmaps/kernel/locally-nameless-kernel.md, section 5.3): entries
// named by name and type, across driver resets and checkpoints; definitions
// and signatures named by their indices; constructors through their
// instances' signatures; and a declaration's levels compared as written.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { CubicalDeclarationTransaction } from "../web/cubical-transaction.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { hiddenIn } from "../web/cubical-variables.mjs";
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
    const context = [["A", u0], ["B", { tag: "Pi", name: "_", domain: A, body: u0 }]].map(([name, type]) => [kernel.symbol(name), syntax.encode(type)]);
    const pi = (name, domain, body) => ({ tag: "Pi", name, domain, body });
    for (const inner of [["x"], ["x", "x"]]) {
      const term = lam("x", A, lam("y", Bx, inner.reduceRight((body, name) => lam(name, A, body), { tag: "Var", name: "y" })));
      const type = pi("x", A, pi("y", Bx, inner.reduceRight(body => pi("z", A, body), Bx)));
      const entries = discharged(driver.graph, driver.check(syntax.encode(term), syntax.encode(type), context));
      assert.equal(new Set(entries).size, entries.length, `${entries.length} binders`);
      assert.deepEqual(entries.map(entry => kernel.entryNames.name(entry)), ["x", "y", ...inner]);
    }
    // So in a context whose second x shadows the first, on which y depends:
    // λ (x : A). y takes neither x's entry.
    const shadowed = [...context, ...[["x", A], ["y", Bx], ["x", A]].map(([name, type]) => [kernel.symbol(name), syntax.encode(type)])];
    const id = driver.infer(syntax.encode(lam("x", A, { tag: "Var", name: "y" })), shadowed);
    const held = driver.contextScope(shadowed, 0n), [entry] = discharged(driver.graph, id);
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
  const [left, right] = [0, 1].map(dimension => g.refl(driver.infer(checker.syntax.encode(x), [[kernel.symbol("x"), at(dimension)]])));
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
  const variable = syntax.encode(x), context = dimension => [[kernel.symbol("x"), at(dimension)]];
  const contextOf = id => checker.driver.graph.judgement(id).context;
  const first = checker.driver.infer(variable, context(0)), kept = checker.driver.infer(variable, context(1));
  assert.deepEqual(contextOf(kept), contextOf(first));
  const shadowing = checker.driver.infer(kernel.term("Lam", kernel.symbol("x"), at(1), variable), context(1));
  assert.ok(!contextOf(kept).includes(discharged(checker.driver.graph, shadowing)[0]));
  kernel.instructionDriver = null;
  const g = checker.driver.graph, again = checker.driver.infer(variable, context(1));
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
  const contextOf = type => checker.driver.graph.judgement(checker.driver.infer(syntax.encode(x), [[symbol, type]])).context;
  const [entry] = contextOf(at(0));
  const transaction = new CubicalDeclarationTransaction(kernel, checker), transient = at(1);
  assert.deepEqual(contextOf(transient), [entry]);
  transaction.finish(false);
  const function_ = kernel.term("Pi", kernel.symbol("_"), syntax.encode(unit), syntax.encode(unit));
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
    for (const handle of [reference, copy]) assert.deepEqual(checker.syntax.decode(handle), { tag: "DefRef", name: "main__one" });
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
    assert.deepEqual(checker.syntax.decode(real), { tag: "DefRef", name: "main__real" });
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
  const value = name => checker.syntax.decode(kernel.definition(kernel.definitions.get(name)).value);
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
