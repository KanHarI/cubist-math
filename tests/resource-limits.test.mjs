import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel, KernelError, cubicalKinds } from "../web/cubical-kernel.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { HLevelSearch } from "../web/translator/hlevel.mjs";
import { T } from "../web/translator/core.mjs";
import { NativeCubicalElaborator } from "../web/cubical-elaborator.mjs";
import { Scope } from "../web/translator/elaboration.mjs";
import { bindDimensions } from "../web/translator/dimension-slots.mjs";
import { admitSignature, modifierCode } from "../web/cubical-signatures.mjs";
import { observeTestCases } from "../web/cubist/test-pragmas.mjs";

const module = await createCubical();
function setup(t) {
  const kernel = new CubicalKernel(module);
  t.after(() => kernel.dispose());
  return { kernel, driver: new InstructionDriver(kernel) };
}

test("native depth exhaustion keeps its kind, is not retried with more steps, and recovers", t => {
  const { kernel } = setup(t), unit = kernel.term("Unit");
  module._cb_checkpoint(kernel.handle);
  let deep = unit;
  for (let i = 1; i < 512; i++) deep = kernel.term("Sum", 0, deep, unit);
  assert.throws(() => kernel.term("Sum", 0, deep, unit), error => error.kind === "resource");
  let calls = 0;
  assert.equal(kernel.withGrowingBudget(() => {
    calls++;
    return module._cb_term(kernel.handle, cubicalKinds.indexOf("Sum"), 0, deep, unit, 0, 0);
  }), 0);
  assert.equal(calls, 1);
  assert.equal(kernel.errorKind(), "resource");
  module._cb_rollback(kernel.handle);
  assert.equal(kernel.errorKind(), "none");
  assert.equal(kernel.head(unit), unit);
});

test("argument inference reports a resource failure instead of an undetermined implicit argument", async t => {
  const program = new CubicalProgram(module, async () => null, { testMode: true });
  t.after(() => program.dispose());
  const infer = program.checker.infer.bind(program.checker);
  let interrupted = false;
  program.checker.infer = (term, ...rest) => {
    if (!interrupted && term.tag === "Point") {
      interrupted = true;
      throw new KernelError("Native prototype syntax depth exceeds 512.", "resource");
    }
    return infer(term, ...rest);
  };
  const result = await program.check(`
def identity{{A : U0}}(x : A) : A := x;
# test(depth) # expect_error(E388)
def limited := identity(tt);
def recovered : Unit := tt;
`, "main");
  assert.ok(interrupted, "the inference probe was reached");
  assert.equal(result.outputs.find(output => output.name === "limited").failure, "resource");
  assert.ok(result.outputs.find(output => output.name === "recovered").verified);
  const report = observeTestCases(program, result);
  assert.equal(report.prerequisites.length, 1, "an implicit-argument refusal cannot conceal a resource limit");
  assert.deepEqual(report.expectedErrors, []);
});

test("h-level cycle comparisons cannot turn a resource failure into a failed candidate", () => {
  const failure = new KernelError("Native prototype syntax depth exceeds 512.", "resource");
  const scope = { context: new Map(), evidence: [], spend() {}, equal() { throw failure; } };
  const search = new HLevelSearch(scope, [], String);
  search.active.push({ level: 1, type: T.unit });
  assert.throws(() => search.prove(1, { tag: "Const", value: 0 }, T.unit), error => error === failure);
});

test("bounded normalization may fall back, but final conversion preserves resource failure", t => {
  const { driver } = setup(t), graph = driver.graph;
  const unit = graph.unit(), focus = () => driver.focus(graph.refl(unit), "other");
  const failure = new KernelError("Native normal-form depth exceeded.", "resource");
  const reduce = driver.reduce.bind(driver);
  driver.reduce = () => { throw failure; };
  assert.equal(driver.normalizeBoth(focus(), focus()), false);
  // If the remaining conversion also cannot answer, it must not report
  // inequality. The ordinary mismatch control below still does.
  driver.agree = () => false;
  assert.throws(() => driver.convertTo(graph.point(), graph.void()), error => error === failure);
  driver.reduce = reduce;
  assert.throws(() => driver.convertTo(graph.point(), graph.void()), error => error.kind === "mismatch");
});

test("eta propagates resource and time limits from deriving the focused term", t => {
  const { driver } = setup(t), graph = driver.graph;
  const unit = graph.unit(), x = graph.extend(unit, "x");
  const lambda = graph.lambda(x, graph.variable(x));
  const fn = graph.variable(graph.extend(graph.pi(x, unit), "f"));
  const focus = judgement => driver.focus(graph.refl(judgement), "other");
  for (const kind of ["budget", "deadline", "resource"]) {
    const failure = new KernelError("probe", kind);
    driver.scopeAt = () => { throw failure; };
    assert.throws(() => driver.eta(focus(lambda), focus(fn)), error => error === failure);
  }
});

test("bridge formula work exhaustion is a resource failure and permits recovery", t => {
  const { kernel } = setup(t), clauses = [];
  // Equal-sized distinct clauses form an antichain. The bridge reaches its
  // work bound while copying this growing formula, before its size bound.
  for (let a = 0n; a < 32n && clauses.length < 4097; a++)
    for (let b = a + 1n; b < 32n && clauses.length < 4097; b++)
      for (let c = b + 1n; c < 32n && clauses.length < 4097; c++)
        clauses.push([(1n << a) | (1n << b) | (1n << c), 0n]);
  assert.throws(() => kernel.formula("interval", clauses), error => error.kind === "resource");
  assert.ok(kernel.formula("interval", [[1n, 0n]]));
  assert.equal(kernel.errorKind(), "none");
});

for (const kind of ["fuel", "budget", "resource", "deadline"]) {
  test(`definition admission may clean empty faces after ${kind}, but preserves an unresolved limit`, t => {
    const { kernel } = setup(t), checker = new NativeCubicalElaborator(kernel);
    const admit = checker.admit.bind(checker), original = new KernelError("probe", kind);
    const signature = T.glueType(T.unit, [{ face: [], type: T.unit, equiv: T.point }]);
    let calls = 0;
    checker.admit = (...args) => {
      if (++calls === 1) throw original;
      return admit(...args);
    };
    if (kind === "deadline") {
      assert.throws(() => checker.define("clean", T.glue(T.glueType(T.unit, []), T.point, []), signature), error => error.kind === kind);
      assert.equal(calls, 1);
    } else {
      assert.ok(checker.define("clean", T.glue(T.glueType(T.unit, []), T.point, []), signature));
      assert.equal(calls, 2);
      calls = 0;
      checker.admit = () => { throw ++calls === 1 ? original : new KernelError("ordinary refusal", "other"); };
      assert.throws(() => checker.define("limited", T.point, signature), error => error.kind === kind);
      assert.equal(calls, 2);
    }
    calls = 0;
    checker.admit = () => { calls++; throw original; };
    assert.throws(() => checker.define("unchanged", T.point, T.unit), error => error.kind === kind);
    assert.equal(calls, 1, "an unchanged signature is not retried");
  });
}

test("a resource failure in cleaned admission is retained after an ordinary first refusal", t => {
  const { kernel } = setup(t), checker = new NativeCubicalElaborator(kernel);
  const signature = T.glueType(T.unit, [{ face: [], type: T.unit, equiv: T.point }]);
  let calls = 0;
  checker.admit = () => { throw new KernelError("probe", ++calls === 1 ? "other" : "resource"); };
  assert.throws(() => checker.define("limited", T.point, signature), error => error.kind === "resource");
  assert.equal(calls, 2);
});

test("face restriction cannot retry a resource failure as an ordinary refusal", t => {
  const { driver } = setup(t), failure = new KernelError("probe", "resource");
  driver.typesMention = () => true;
  let calls = 0;
  assert.throws(() => driver.onFace(new Map(), [1n, 0n], () => { calls++; throw failure; }), error => error === failure);
  assert.equal(calls, 1);
});

test("constructor instance inference retains the limit from an argument", async t => {
  const program = new CubicalProgram(module, async () => null);
  t.after(() => program.dispose());
  const infer = program.checker.infer.bind(program.checker);
  let interrupted = false;
  program.checker.infer = (term, ...rest) => {
    if (!interrupted && term.tag === "DefRef" && term.name.endsWith("__seed")) {
      interrupted = true;
      throw new KernelError("probe", "resource");
    }
    return infer(term, ...rest);
  };
  const result = await program.check(`
inductive List(A : U0) { nil; cons(x : A, xs : List(A)); }
def seed : List(Unit) := nil;
def limited := cons(tt, seed);
def recovered : Unit := tt;
`, "main");
  assert.ok(result.outputs.find(output => output.name === "seed").verified);
  assert.ok(interrupted, "constructor inference examined its recursive argument");
  assert.equal(result.outputs.find(output => output.name === "limited").failure, "resource");
  assert.ok(result.outputs.find(output => output.name === "recovered").verified);
});

test("implicit argument unification retains a limit while unfolding a type alias", async t => {
  let active = false;
  const program = new CubicalProgram(module, async () => null, {
    onDeclarationStart: (_name, declaration) => { active = declaration.name.text === "limited"; },
  });
  t.after(() => program.dispose());
  const nf = program.checker.nf.bind(program.checker);
  let interrupted = false;
  program.checker.nf = (term, ...rest) => {
    if (active && !interrupted && term.tag === "App" && term.fn.tag === "DefRef" && term.fn.name.endsWith("__Tagged")) {
      interrupted = true;
      throw new KernelError("probe", "resource");
    }
    return nf(term, ...rest);
  };
  const result = await program.check(`
def Tagged(A : U0) : U0 := Unit;
def untag{{A : U0}}(t : Tagged(A)) : Unit := t;
def limited(t : Tagged(Unit)) : Unit := untag(t);
def recovered : Unit := tt;
`, "main");
  assert.ok(result.outputs.find(output => output.name === "untag").verified);
  assert.ok(interrupted, "the alias was unfolded");
  assert.equal(result.outputs.find(output => output.name === "limited").failure, "resource");
  assert.ok(result.outputs.find(output => output.name === "recovered").verified);
});

test("overlap and motive comparisons preserve a final normalization limit", t => {
  const { driver } = setup(t), g = driver.graph;
  const unit = g.unit(), point = g.point(), x = g.extend(unit, "x"), family = g.lambda(x, unit);
  const failure = new KernelError("probe", "resource");
  driver.agree = () => false;
  driver.reduce = () => { throw failure; };
  assert.throws(() => driver.overlapAgreement(point, point, [0n, 0n]), error => error === failure);
  assert.throws(() => driver.motive(family, unit), error => error === failure);
});

test("frontend dimension and signature bounds carry resource kinds", t => {
  const { kernel } = setup(t);
  const dimensions = new Map(Array.from({ length: 64 }, (_, i) => [`d${i}`, i]));
  const line = T.line("new", T.unit, T.at(T.variable("p"), [[...dimensions.keys()].map(name => `${name}:1`)]));
  assert.throws(() => bindDimensions(line, dimensions), error => error.kind === "resource");
  assert.throws(() => new Scope({}, new Map(), new Map(), dimensions).bindDimension("new"), error => error.kind === "resource");
  assert.throws(() => modifierCode({ trunc: 15 }), error => error.kind === "resource");
  assert.throws(() => admitSignature(kernel, { name: "large", parameters: Array(65).fill({}) }), error => error.kind === "resource");
});
