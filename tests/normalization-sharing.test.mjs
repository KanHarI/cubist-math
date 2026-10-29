import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel, KernelError } from "../web/cubical-kernel.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { readFile } from "node:fs/promises";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { InstructionGraph } from "../web/cubical-instructions.mjs";
import { ReplSession } from "../web/repl-session.mjs";

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

// The derivation's twin of the test above (docs/reports/driver-derivation-sharing.md):
// a graph met under many binders, as a folded normal form's closed parts
// are, is derived once per node and scope it reads, not once per path to
// it. Two paths to the preceding type per level, under different binders,
// and its domain a third: 3^40 paths, a few nodes a level. Each case counts
// the instructions it issues, and stops at a bound a path-by-path
// derivation passes within the first levels.
test("a graph shared beneath different binders is derived once per node", async t => {
  const { kernel, driver, term } = await setup(t), graph = driver.graph;
  const levels = 40, unit = term("Unit"), symbol = name => kernel.symbol(name), v = name => term("Var", symbol(name));
  const issue = graph.issue.bind(graph);
  let issued = 0;
  graph.issue = (...operands) => {
    assert.ok(++issued < 50 * levels, "a shared graph was derived once per path to it");
    return issue(...operands);
  };
  const doubled = (type, tag) => {
    for (let i = 0; i < levels; i++)
      type = term("Sum", 0, term("Pi", symbol(`${tag}a${i}`), type, type), term("Pi", symbol(`${tag}b${i}`), type, type));
    return type;
  };
  // Closed: each level is derived once, in the scope with nothing in it.
  const closed = graph.judgement(driver.infer(doubled(unit, "c")));
  assert.equal(closed.kind, "typing");
  assert.deepEqual(closed.context, []);
  const closedIssued = issued;
  // Open: each level mentions x, in a path type, so its scope keeps x's
  // entry, and nothing of the binders it does not mention.
  issued = 0;
  const open = doubled(term("Path", 0, unit, v("x"), v("x")), "o");
  const judgement = graph.judgement(driver.infer(open, [[symbol("x"), unit]]));
  assert.equal(graph.entry(judgement.context[0]).name, "x");
  assert.ok(driver.alpha(judgement.term, open));
  assert.ok(closedIssued < 10 * levels && issued < 10 * levels, `issued ${closedIssued} and ${issued} instructions`);
});

// The case that found it: an exact expected value compares two folded
// normal forms by conversion, which derives each. A rational's, binary
// backed, is under a thousand nodes as a graph and millions as a tree;
// before the fix the comparison below issued 25.5M instructions, and with
// it about 120,000. The bound stops a derivation by paths early.
test("an exact expected value on a rational derives its folded normal form by its graph", async t => {
  const program = new CubicalProgram(await createCubical(), sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  const session = new ReplSession(program), { kernel, checker } = program;
  const prepared = await session.run("import rationals; use rationals; def half := typed(Q, 1/2);");
  assert.deepEqual(prepared.filter(answer => answer.kind === "error"), []);
  const name = [...checker.definitionViews.keys()].find(name => name.endsWith("half"));
  const normal = kernel.normalizeFolded(checker.evaluated(checker.definitionViews.get(name).term).expression);
  const nodes = new Set(), trees = new Map(), stack = [normal];
  while (stack.length) {
    const handle = stack.pop();
    if (handle && !nodes.has(handle)) { nodes.add(handle); stack.push(...kernel.node(handle).children); }
  }
  const tree = handle => {
    if (!handle) return 0;
    if (!trees.has(handle)) trees.set(handle, 1 + kernel.node(handle).children.reduce((sum, child) => sum + tree(child), 0));
    return trees.get(handle);
  };
  assert.ok(nodes.size < 2000 && tree(normal) > 1000000, `${nodes.size} nodes, ${tree(normal)} as a tree`);
  const bound = 1000000, issue = InstructionGraph.prototype.issue;
  let issued = 0;
  InstructionGraph.prototype.issue = function (...operands) {
    if (++issued > bound) throw new Error("the folded normal form was derived by its paths");
    return issue.apply(this, operands);
  };
  let answers;
  try { answers = await session.run("evaluate 1/2 expecting 1/2;"); }
  finally { InstructionGraph.prototype.issue = issue; }
  assert.ok(issued <= bound, `issued ${issued} instructions`);
  assert.deepEqual(answers.map(answer => answer.kind), ["value"]);
  assert.match(answers[0].text, /^class\(\(class\(\(bnat\.\(1\), bnat\.\(0\)\)\), class\(\(bnat\.\(2\), bnat\.\(0\)\)\), /);
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

// A composition's faces lie outside its binder, under the binders around
// it. Comparing its tubes one link at a time, the renaming of a binder
// around it is kept for a link whose face names that dimension: <i>
// comp^k Unit [i = 0 ↦ tt] tt and <j> comp^k Unit [j = 0 ↦ tt] tt are
// alpha-equal, as the kernel finds them, and a face on a free dimension
// is no bound one.
test("dimension pruning keeps the renamings a system's faces read", async t => {
  const { kernel, driver, term } = await setup(t);
  const unit = term("Unit"), point = term("Point");
  const at0 = dim => kernel.formula("face", [[0n, 1n << BigInt(dim)]]);
  const line = (bound, faced) => term("PLam", bound, unit, term("Comp", 5, unit, term("Tube", at0(faced), point, 0), point));
  const glued = (bound, faced) => term("PLam", bound, term("U", 0, term("LConst", 0)),
    term("Glue", 0, unit, term("GlueSystem", at0(faced), unit, term("Var", kernel.symbol("e")), 0)));
  for (const shape of [line, glued]) {
    assert.ok(driver.alpha(shape(2, 2), shape(1, 1)), shape.name);
    assert.equal(kernel.alphaEqual(shape(2, 2), shape(1, 1)), true, shape.name);
    assert.ok(!driver.alpha(shape(2, 2), shape(1, 0)), `${shape.name}: a bound face against a free one`);
    assert.equal(kernel.alphaEqual(shape(2, 2), shape(1, 0)), false, shape.name);
  }
});

// The two reproductions of #331's second review, with the faces counted:
// a composition whose binder reuses the index of the path binder its face
// names, <i> comp^i X [i = 0 ↦ a] a, is its own derivation's term both ways;
// and <d0><d0> comp^d3 Unit [d0 = 0 ↦ tt] tt, whose face names the inner
// binder, is not <d1><d2> comp^d3 Unit [d1 = 0 ↦ tt] tt, whose face names
// the outer one. The driver answers as the kernel does.
test("a composition's faces are read under the binders around it, each by its own identity", async t => {
  const { kernel, driver, term } = await setup(t);
  const at0 = dim => kernel.formula("face", [[0n, 1n << BigInt(dim)]]);
  const symbol = name => kernel.symbol(name), v = name => term("Var", symbol(name));
  const source = term("PLam", 0, v("X"), term("Comp", 0, v("X"), term("Tube", at0(0), v("a"), 0), v("a")));
  const derived = driver.graph.judgement(driver.infer(source, [[symbol("X"), term("U", 0, term("LConst", 0))], [symbol("a"), v("X")]])).term;
  assert.ok(kernel.alphaEqual(derived, source) && kernel.alphaEqual(source, derived));
  assert.ok(driver.alpha(derived, source), "the derived term against its source");
  assert.ok(driver.alpha(source, derived), "the source against its derived term");
  const unit = term("Unit"), point = term("Point");
  const square = (outer, inner, faced) => term("PLam", outer, unit,
    term("PLam", inner, unit, term("Comp", 3, unit, term("Tube", at0(faced), point, 0), point)));
  const inner = square(0, 0, 0), outer = square(1, 2, 1);
  assert.equal(kernel.alphaEqual(inner, outer), false);
  assert.equal(driver.alpha(inner, outer), false, "a face on the inner binder against one on the outer");
  assert.equal(new InstructionDriver(kernel).alpha(outer, inner), false, "and the other way, with no answer kept");
});

// A derivation reads only part of its scope (InstructionDriver.narrow), and
// summarizes the dimensions the types of the variables it leaves out
// mention. A variable the term binds again leaves the scope under that
// binder, its type's dimensions with it, as in the whole scope: here x's
// type, p @ i, mentions i, and under λ(x : Unit) nothing does, so each of
// 64 path binders on i keeps its index rather than taking a fresh one, of
// which there are fewer.
test("a variable the term binds again no longer mentions its type's dimensions under that binder", async t => {
  const { kernel, driver, term } = await setup(t);
  const unit = term("Unit"), point = term("Point"), symbol = name => kernel.symbol(name);
  const universe = term("U", 0, term("LConst", 0)), i = kernel.formula("interval", [[1n, 0n]]);
  const context = [[symbol("p"), term("Path", 1, universe, unit, unit)], [symbol("x"), term("PApp", i, term("Var", symbol("p")))]];
  let body = point, type = unit;
  for (let level = 0; level < 64; level++) [body, type] = [term("PLam", 0, type, body), term("Path", 0, type, body, body)];
  const lambda = term("Lam", symbol("x"), unit, body);
  const judgement = driver.graph.judgement(driver.infer(lambda, context, 1n));
  assert.ok(driver.alpha(judgement.term, lambda), "each path binder kept its index");
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
  const smallQuotient = await readFile(new URL("fixtures/quotient-normalization.cubist", import.meta.url), "utf8");
  for (const [name, source, optimizations = {}] of [
    ["small_quotient", smallQuotient],
    // A unary descent covers the stuck eliminator with interning off. The
    // binary fixture exceeds this test's budget in that mode.
    ["unary_quotient_unshared", `import quotients;
      def Related(a, b : Unit) : U0 := Unit;
      def Q : U0 := Quotient(U0, Unit, Related);
      computable def copy(x : Q) : Q := descend(
        U0, U0, Unit, Related, Q, quotient_is_set(U0, Unit, Related),
        fun (a : Unit) => typed(Q, class(a)),
        fun (a, b : Unit, r : Related(a, b)) => class_path(U0, Unit, Related, a, b, r), x
      );
      evaluate copy expecting !!!_;`, {shareSyntax: false}],
    ["integer_multiplication", "import binary_integers; evaluate bint_mul expecting !!!_;"],
    ["binary_fraction_one", `import fractions; import binary_integers;
      evaluate fraction_field(binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one).one expecting !!!_;`],
  ]) {
    const program = new CubicalProgram(module, sourceReader(), {collectReferences: false, optimizations});
    // Bound regressions by deterministic work, including query retries. The
    // previous implementation exhausted the arena on these small functions;
    // !!! keeps them asking for the full normal form.
    program.kernel.maxQuerySteps = 40000000n;
    try {
      const result = await program.check(source, name);
      assert.deepEqual(result.gaps, [], name);
      assert.equal(result.evaluations.length, 1, name);
      assert.ok(result.evaluations[0].value.length > 0, name);
    } finally { program.dispose(); }
  }
});
