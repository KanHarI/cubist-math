// Iota on the locally nameless kernel (docs/roadmaps/kernel/
// locally-nameless-kernel.md, sections 3.3 and 7.1): the eliminator on a
// constructor computes as it did on main's ABI 3, where its display reads
// the constructor's type with fresh variables. Each expectation below was
// checked on main's build too, and its printed forms agree with main's up to
// the names of the clauses' binders, which the kernel no longer keeps.
// kernel/tests/test_iota.c checks the single Iota step of the same shapes.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkProgram } from "./check-program.mjs";

const module = await createCubical();

const two = `inductive Two {
  one;
  two;
}
`;

// A higher type whose constructors take paths: wrap's position is a path
// (a cube and no arity binder), spin's a path under an arity binder;
// around's cube has an earlier position as its endpoints, and through's
// applies an earlier position to a data argument. f is the eliminator
// with clauses that keep each argument in its place.
const higher = `${two}
inductive S {
  base;
  loop : base = base;
  wrap(p : base = base);
  twin(p, q : base = base);
  spin(q : Two -> base = base);
  around(x : S, p : x = x);
  through(a : Two, q : Two -> S, p : q(a) = q(a));
}

def f(x : S) : S := induction x return S {
    base => base;
    loop @ i => loop @ i;
    wrap(p) with h => twin(p, h);
    twin(p, q) with h, k => twin(k, h);
    spin(q) with h => spin(h);
    around(x, p) with h, k => around(h, k);
    through(a, q, p) with h, k => through(a, h, k);
  };
`;

// What an evaluation of the full normal form printed, from its start.
const printed = result => result.prints.map(print => print.text);

test("iota lifts a path-valued position to the path of its eliminations", async t => {
  // wrap(p) ⟶ m_wrap(p, ⟨i⟩ f(p @ i)), as on main: the clause gets p and
  // the path, never f applied to p itself; with an arity binder, spin(q) ⟶
  // m_spin(λ y. ⟨i⟩ f(q(y) @ i)). The last two expectations are wrong on
  // purpose: the check tells the arguments apart, and the lifted position
  // from the position.
  const { result } = await checkProgram(t, `${higher}
evaluate fun (p : base = base) => f(wrap(p)) expecting fun (p : base = base) => twin(p, path i => f(p @ i));
evaluate fun (q : Two -> base = base) => f(spin(q))
  expecting fun (q : Two -> base = base) => spin(fun (y : Two) => path i => f(q(y) @ i));
evaluate fun (p : base = base) => f(wrap(p)) expecting fun (p : base = base) => twin(path i => f(p @ i), p);
evaluate fun (q : Two -> base = base) => f(spin(q)) expecting fun (q : Two -> base = base) => spin(q);
print(evaluate(!!!fun (p : base = base) => f(wrap(p))));
print(evaluate(!!!fun (q : Two -> base = base) => f(spin(q))));
`, { module });
  assert.equal(result.gaps.length, 2, result.gaps.map(gap => gap.reason).join("\n"));
  for (const gap of result.gaps) assert.match(gap.reason, /^The term evaluates to /);
  assert.match(result.gaps[0].reason, /, not fun \(p : base = base\) => twin\(path i => f\(p @ i\), p\)\.$/);
  const [wrapped, spun] = printed(result);
  assert.match(wrapped, /^fun \(p : base = base\) => twin\(p, path i => induction p @ i return S \{ base => base; /);
  assert.match(spun, /^fun \(q : Two -> base = base\) => spin\(fun \(x : Two\) => path i => induction q\(x\) @ i return S \{ /);
});

test("iota's display shows a boundary through the positions' shown values", async t => {
  // around's cube has x as both endpoints: at x := (λ (z : S). z)(base), a
  // λ-headed application, the lifted path's endpoints are f(x), and the
  // reduct is m_around(f(x), ⟨i⟩ f(p @ i)), as on main. through's cube
  // applies the position q to the data argument a.
  const { result } = await checkProgram(t, `${higher}
evaluate fun (p : base = base) => f(around((fun (z : S) => z)(base), p))
  expecting fun (p : base = base) => around(base, path i => f(p @ i));
evaluate fun (q : Two -> S, p : q(one) = q(one)) => f(through(one, q, p))
  expecting fun (q : Two -> S, p : q(one) = q(one)) => through(one, fun (a : Two) => f(q(a)), path i => f(p @ i));
print(evaluate(!!!fun (p : base = base) => f(around((fun (z : S) => z)(base), p))));
print(evaluate(!!!fun (q : Two -> S, p : q(one) = q(one)) => f(through(one, q, p))));
`, { module });
  assert.deepEqual(result.gaps, []);
  const [around, through] = printed(result);
  assert.match(around, /^fun \(p : base = base\) => around\(base, path i => induction p @ i return S \{ /);
  assert.match(through, /^fun \(q : Two -> S, p : q\(one\) = q\(one\)\) => through\(one, fun \(x : Two\) => induction q\(x\) return S \{ .*\}, path i => induction p @ i return S \{ /);
});

test("iota instantiates a position's arity and cube at the data arguments before it", async t => {
  // Tree : U1 { node(A : U0, q : A → Tree) }: node(Unit, q) ⟶
  // m_node(Unit, λ (a : Unit). grow(q(a))), as on main; link's path-valued
  // position has an arity over the data argument A and a cube whose
  // endpoint applies q to the data argument a.
  const { result } = await checkProgram(t, `${two}
inductive Tree : U1 {
  leaf;
  node(A : U0, q : A -> Tree);
  link(A : U0, a : A, q : A -> Tree, p : forall y : A. q(y) = q(a));
}

def grow(t : Tree) : Tree := induction t return Tree {
    leaf => leaf;
    node(A, q) with h => node(A, h);
    link(A, a, q, p) with h, k => link(A, a, h, k);
  };

evaluate fun (q : Unit -> Tree) => grow(node(Unit, q)) expecting fun (q : Unit -> Tree) => node(Unit, fun (a : Unit) => grow(q(a)));
evaluate fun (q : Two -> Tree, p : forall y : Two. q(y) = q(one)) => grow(link(Two, one, q, p))
  expecting fun (q : Two -> Tree, p : forall y : Two. q(y) = q(one)) =>
    link(Two, one, fun (a : Two) => grow(q(a)), fun (y : Two) => path i => grow(p(y) @ i));
evaluate fun (q : Unit -> Tree) => grow(node(Unit, q)) expecting fun (q : Unit -> Tree) => node(Unit, q);
print(evaluate(!!!fun (q : Unit -> Tree) => grow(node(Unit, q))));
print(evaluate(!!!fun (q : Two -> Tree, p : forall y : Two. q(y) = q(one)) => grow(link(Two, one, q, p))));
`, { module });
  assert.equal(result.gaps.length, 1, result.gaps.map(gap => gap.reason).join("\n"));
  assert.match(result.gaps[0].reason, /^The term evaluates to fun \(q : Unit -> Tree\) => node\(Unit, fun \(x : Unit\) => induction q\(x\) return Tree /);
  const [node, link] = printed(result);
  assert.match(node, /^fun \(q : Unit -> Tree\) => node\(Unit, fun \(x : Unit\) => induction q\(x\) return Tree \{ leaf => leaf; /);
  assert.match(link, /^fun \(q : Two -> Tree, p : forall y : Two\. q\(y\) = q\(one\)\) => link\(Two, one, fun \(x : Two\) => induction q\(x\) return Tree \{ .*\}, fun \(x : Two\) => path i => induction p\(x\) @ i return Tree \{ /);
});
