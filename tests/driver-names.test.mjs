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
  // reuse one by its symbol: two fresh entries at one type are two.
  assert.notEqual(driver.freshEntry(type, "x"), driver.freshEntry(type, "x"));
});

test("λ (x : A). λ (x : A). x is the inner binder's variable", async t => {
  const program = fresh(t), { kernel, checker } = program, driver = checker.driver;
  const term = lam("x", unit, lam("x", unit, x));
  const judgement = driver.graph.judgement(driver.infer(checker.syntax.encode(term)));
  const second = checker.syntax.encode(lam("a", unit, lam("b", unit, { tag: "Var", name: "b" })));
  const first = checker.syntax.encode(lam("a", unit, lam("b", unit, { tag: "Var", name: "a" })));
  assert.ok(kernel.alphaEqual(judgement.term, second));
  assert.ok(!kernel.alphaEqual(judgement.term, first));
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
