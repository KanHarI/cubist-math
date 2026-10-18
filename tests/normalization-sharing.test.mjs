import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel, KernelError } from "../web/cubical-kernel.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { readFile } from "node:fs/promises";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

async function setup(t) {
  const kernel = new CubicalKernel(await createCubical());
  t.after(() => kernel.dispose());
  const driver = new InstructionDriver(kernel);
  return { kernel, driver, term: (...args) => kernel.term(...args) };
}

test("normal forms shared beneath different unused binders compare by graph size", async t => {
  const { driver } = await setup(t), graph = driver.graph;
  const unit = graph.unit();
  let a = unit, b = unit;
  // Two paths to the preceding type per level, under different binders:
  // 2^40 expanded leaves, only 120 new nodes on each side. Full normalization
  // now finishes these DAGs; comparison must preserve that sharing too.
  for (let i = 0; i < 40; i++) {
    a = graph.sum(graph.pi(graph.extend(unit, `a${i}`), a), graph.pi(graph.extend(unit, `b${i}`), a));
    b = graph.sum(graph.pi(graph.extend(unit, `c${i}`), b), graph.pi(graph.extend(unit, `d${i}`), b));
  }
  const normal = type => graph.judgement(graph.step(graph.refl(type), "other", [], "normalize")).other;
  a = normal(a); b = normal(b);
  let reads = 0;
  const node = driver.node.bind(driver);
  driver.node = handle => {
    assert.ok(++reads < 5000, "comparison revisited shared syntax under irrelevant binders");
    return node(handle);
  };
  assert.ok(driver.alpha(a, b));
  assert.ok(reads < 2000, `comparison used ${reads} node reads`);
});

test("pruned term scopes preserve free names, shadowing and binder domains", async t => {
  const { driver, term } = await setup(t);
  const unit = term("Unit"), v = name => term("Var", name);
  const pi = (name, body, domain = unit) => term("Pi", name, domain, body);
  const sum = name => term("Sum", 0, v(name), unit);
  assert.ok(driver.alpha(pi(10, v(10)), pi(20, v(20))));
  assert.ok(!driver.alpha(pi(10, v(10)), pi(20, v(10))), "bound versus free on the right");
  assert.ok(!driver.alpha(pi(10, v(11)), pi(11, v(11))), "free versus bound on the right");
  // Non-leaf bodies reach scope pruning before the variable comparison.
  assert.ok(!driver.alpha(pi(10, sum(11)), pi(11, sum(11))), "retain a binding used only on the right");
  assert.ok(!driver.alpha(pi(11, sum(11)), pi(10, sum(11))), "retain a binding used only on the left");
  assert.ok(driver.alpha(pi(10, pi(10, v(10))), pi(20, pi(21, v(21)))), "nearest binder wins");
  assert.ok(!driver.alpha(pi(10, pi(10, v(10))), pi(20, pi(21, v(20)))), "outer and inner binders differ");
  assert.ok(!driver.alpha(pi(10, v(10), v(10)), pi(20, v(20), v(20))), "a binder does not scope its own domain");
  assert.ok(driver.alpha(pi(10, pi(11, v(11), v(10))), pi(20, pi(21, v(21), v(20)))), "outer binders scope inner domains");
  assert.ok(!driver.alpha(pi(10, pi(11, v(11), v(10))), pi(20, pi(21, v(21), v(10)))), "a free name in a domain stays free");
  // The inner binder shadows the outer one in its body, but its own domain
  // still uses the outer binding, even when their symbols are identical.
  assert.ok(driver.alpha(pi(10, pi(10, unit, v(10))), pi(20, pi(20, unit, v(20)))), "shadowing leaves the domain under the outer binder");
  assert.ok(!driver.alpha(pi(10, pi(10, unit, v(10))), pi(20, pi(20, unit, v(10)))), "a shadowing binder cannot capture its domain");
  // Populate and reuse comparison caches under distinct, explicit scopes.
  assert.ok(driver.alpha(sum(10), sum(20), { left: 10, right: 20, next: null }));
  assert.ok(!driver.alpha(sum(10), sum(20), { left: 10, right: 21, next: null }));
  assert.ok(!driver.alpha(sum(10), sum(20)));
});

test("term-scope pruning retains level variables and annotation dependencies", async t => {
  const { driver, term } = await setup(t);
  const v = name => term("Var", name), unit = term("Unit"), bound = term("LBound", 1);
  const family = name => term("Sum", 0, term("U", 0, v(name)), unit);
  const level = (name, used) => term("LLam", name, bound, family(used));
  assert.ok(driver.alpha(level(10, 10), level(20, 20)));
  assert.ok(!driver.alpha(level(10, 10), level(20, 10)));
  const annotated = name => term("Inl", 0, term("Sum", 0, v(name), unit), term("Point"));
  const lam = (name, used) => term("Lam", name, term("U", 0, term("LConst", 0)), annotated(used));
  assert.ok(driver.alpha(lam(10, 10), lam(20, 20)));
  assert.ok(!driver.alpha(lam(10, 10), lam(20, 10)));
});

test("normalization compares closed graphs natively and reuses that answer", async t => {
  const { driver } = await setup(t), graph = driver.graph, unit = graph.unit();
  let a = unit, b = unit;
  for (let i = 0; i < 40; i++) {
    a = graph.sum(graph.pi(graph.extend(unit, `a${i}`), a), graph.pi(graph.extend(unit, `b${i}`), a));
    b = graph.sum(graph.pi(graph.extend(unit, `c${i}`), b), graph.pi(graph.extend(unit, `d${i}`), b));
  }
  const left = driver.focus(graph.refl(a), "other"), right = driver.focus(graph.refl(b), "other");
  driver.freeTermSymbols = () => { throw new Error("closed normal-form comparison rescanned the graph in JavaScript"); };
  assert.ok(driver.normalizeBoth(left, right, null, null));
  // A later conversion must reuse the answer instead of rebuilding free-name
  // sets. Querying natively but forgetting this memo merely moves the cost.
  assert.ok(driver.alpha(driver.subterm(left), driver.subterm(right)));
});

test("normal-form comparison preserves outer renamings and recovers from query exhaustion", async t => {
  const { driver, kernel } = await setup(t), graph = driver.graph, unit = graph.unit();
  const a = graph.extend(unit, "a"), b = graph.extend(unit, "b");
  const focus = judgement => driver.focus(graph.refl(judgement), "other");
  const left = focus(graph.variable(a)), right = focus(graph.variable(b));
  assert.ok(driver.normalizeBoth(left, right, { left: graph.entry(a).symbol, right: graph.entry(b).symbol, next: null }, null));
  assert.ok(!driver.normalizeBoth(left, right, null, null), "free names differ without the outer renaming");

  const i = graph.dimension(0), j = graph.dimension(1), point = graph.point();
  const p = graph.variable(graph.extend(graph.path(i, unit, point, point), "p"));
  const atI = focus(graph.pathApply(p, i)), atJ = focus(graph.pathApply(p, j));
  assert.ok(driver.normalizeBoth(atI, atJ, null, { left: 0, right: 1, next: null }));
  assert.ok(!driver.normalizeBoth(atI, atJ, null, null), "free dimensions differ without the outer renaming");

  const x = focus(graph.pi(a, unit)), y = focus(graph.pi(b, unit));
  const query = kernel.alphaEqual.bind(kernel);
  kernel.alphaEqual = (left, right) => { kernel.setStepBudget(1n); return query(left, right); };
  assert.ok(driver.normalizeBoth(x, y, null, null), "exhaustion falls back to the existing comparison");
  assert.ok(driver.alpha(driver.subterm(x), driver.subterm(y)), "no false answer was cached");
  kernel.alphaEqual = query;
  assert.ok(driver.normalizeBoth(x, y, null, null));
});

test("normalization and comparison propagate deadlines and programming errors", async t => {
  const { driver, kernel } = await setup(t), graph = driver.graph, unit = graph.unit();
  const left = driver.focus(graph.refl(unit), "other"), right = driver.focus(graph.refl(unit), "other");
  const reduce = driver.reduce.bind(driver), query = kernel.alphaEqual.bind(kernel);
  for (const error of [new KernelError("Declaration time limit exceeded.", "deadline"), new TypeError("probe")]) {
    driver.reduce = () => { throw error; };
    assert.throws(() => driver.normalizeBoth(left, right, null, null), caught => caught === error);
    assert.equal(driver.unnormalizable.size, 0, "interrupted work is not a deterministic normalization failure");
    driver.reduce = reduce;
    kernel.alphaEqual = () => { throw error; };
    assert.throws(() => driver.normalizeBoth(left, right, null, null), caught => caught === error);
    kernel.alphaEqual = query;
  }
});

test("open quotient operations fully normalize within a bounded amount of kernel work", async () => {
  const module = await createCubical();
  for (const [name, source] of [
    ["small_quotient", await readFile(new URL("fixtures/quotient-normalization.cubist", import.meta.url), "utf8")],
    ["integer_multiplication", "import binary_integers; evaluate bint_mul expecting _;"],
  ]) {
    const program = new CubicalProgram(module, sourceReader(), {collectReferences: false});
    // Bound regressions by deterministic work, including query retries. The
    // previous implementation exhausted the arena on these small functions.
    program.kernel.maxQuerySteps = 40000000n;
    try {
      const result = await program.check(source, name);
      assert.deepEqual(result.gaps, [], name);
      assert.equal(result.evaluations.length, 1, name);
      assert.ok(result.evaluations[0].value.length > 0, name);
    } finally { program.dispose(); }
  }
});
