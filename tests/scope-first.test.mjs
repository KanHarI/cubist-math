// Scope first, then syntax (docs/roadmaps/kernel/locally-nameless-kernel.md,
// section 5.3): every term is encoded against the scope of the context it is
// asked in, made first, and a variable neither bound in the term nor an entry
// of that scope is refused. The encoding cache keys an open term by its scope
// and the binders around it; the translator's own variables, a rule's, a
// call's placeholders and the binders it walks into, are entries of
// temporary scopes.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";

const module = await createCubical();
const unit = { tag: "Unit" }, point = { tag: "Point" }, u0 = { tag: "U", level: 0 };
const variable = name => ({ tag: "Var", name });
const lam = (name, domain, body) => ({ tag: "Lam", name, domain, body });
const unbound = /Unbound variable/;
function fresh(t) {
  const program = new CubicalProgram(module, sourceReader(), { collectReferences: false });
  t.after(() => program.dispose());
  return program;
}

test("a variable neither bound in the term nor in its scope is refused", async t => {
  const { checker } = fresh(t), syntax = checker.syntax;
  assert.throws(() => syntax.encode(variable("x")), unbound);
  assert.throws(() => syntax.encode({ tag: "U", level: variable("u") }), unbound);
  // Bound by the term's own binder, or an entry of the scope, it is encoded.
  assert.ok(syntax.encode(lam("x", unit, variable("x"))));
  const scope = checker.scopeOf(new Map([["x", unit]]), new Map());
  assert.ok(syntax.encode(variable("x"), new Map(), scope));
});

test("the encoding cache keys an open term by its scope and binders, a closed one by neither", async t => {
  const { kernel, checker } = fresh(t), syntax = checker.syntax, driver = checker.driver;
  // One Var object, bound by the inner binder of one term and by the outer
  // binder of another: each derivation checks its own term.
  const x = variable("x");
  const inner = lam("x", unit, x), outer = lam("x", unit, lam("y", { tag: "Sum", left: unit, right: unit }, x));
  for (const [term, type] of [[inner, { tag: "Pi", name: "a", domain: unit, body: unit }],
    [outer, { tag: "Pi", name: "a", domain: unit, body: { tag: "Pi", name: "b", domain: { tag: "Sum", left: unit, right: unit }, body: unit } }]]) {
    const judgement = driver.graph.judgement(driver.check(syntax.encode(term), syntax.encode(type)));
    assert.ok(kernel.alphaEqual(judgement.term, syntax.encode(term)));
    assert.ok(kernel.alphaEqual(judgement.type, syntax.encode(type)));
  }
  // Encoded under a binder, the same object is not taken for one encoded
  // bare: that is refused.
  assert.throws(() => syntax.encode(x), unbound);
  // A term that mentions an entry is not reused in a scope without it.
  const scope = checker.scopeOf(new Map([["x", unit]]), new Map());
  const open = { tag: "App", fn: lam("z", unit, variable("z")), arg: x };
  assert.ok(syntax.encode(open, new Map(), scope));
  assert.throws(() => syntax.encode(open, new Map(), checker.scopeOf(new Map([["w", unit]]), new Map())), unbound);
  // A closed term is encoded once, whatever scope and binders it is met in.
  const closed = { tag: "Pair", as: { tag: "Sigma", name: "s", domain: unit, body: unit }, first: point, second: point };
  const made = kernel.term, terms = () => { let count = 0; kernel.term = (...args) => { count++; return made.apply(kernel, args); }; return () => count; };
  const handle = syntax.encode(closed, new Map(), scope), count = terms();
  assert.equal(syntax.encode(lam("q", unit, closed)) !== 0, true);
  assert.equal(syntax.encode(closed, new Map(), checker.scopeOf(new Map([["w", unit]]), new Map())), handle);
  assert.equal(count(), 1, "only the new binder is made");
  kernel.term = made;
});

test("a head query asks in its context's scope, and fails where the context is ill-formed", async t => {
  const { checker } = fresh(t);
  const context = new Map([["A", u0], ["a", variable("A")]]);
  assert.deepEqual(checker.nf(lam("y", unit, variable("a")), context, new Map()).tag, "Lam");
  assert.deepEqual(checker.nf({ tag: "App", fn: lam("y", variable("A"), variable("y")), arg: variable("a") }, context, new Map()), variable("a"));
  // An assumption whose type is no type: no entry, and no answer.
  assert.throws(() => checker.nf(variable("a"), new Map([["a", point]]), new Map()));
  // A variable outside the context is refused rather than asked about.
  assert.throws(() => checker.nf(variable("b"), context, new Map()), unbound);
});

test("a call's placeholders are entries of the solver's scope when a type mentioning one is asked about", async t => {
  // unwrap's hole A, with no type expected of the call, is solved by
  // unfolding Wrap(A?) against Unit: a head query on a type that mentions
  // the placeholder.
  const asked = [];
  const { verdicts } = await checkProgram(t, `
def Wrap(A : U0) : U0 := A;
def unwrap{{A : U0}}(w : Wrap(A)) : A := w;
def used := unwrap(tt);
`, { module, options: { onDeclarationStart: (name, declaration, checker) => {
    if (declaration.name.text !== "used") return;
    const nf = checker.nf.bind(checker);
    checker.nf = (term, context, ...rest) => {
      if (term.tag === "App" && term.fn.tag === "DefRef" && term.fn.name === "main__Wrap") asked.push([term.arg, context]);
      return nf(term, context, ...rest);
    };
  } } });
  assert.equal(verdicts.used, true);
  assert.ok(asked.length, "Wrap(A?) was asked about");
  for (const [argument, context] of asked) {
    assert.equal(argument.tag, "Var");
    assert.deepEqual(context.get(argument.name), u0, "the placeholder is in the query's context, at its parameter's domain");
  }
});

test("a simplification rule's level and parameters are entries of its own scope", async t => {
  const asked = [];
  const { verdicts } = await checkProgram(t, `import unat;
use unat;
def explicit(n : UNat) : n + 0 = n {
  simp only [unat_add_zero];
}
`, { module, options: { onDeclarationStart: (name, declaration, checker) => {
    if (declaration.name.text !== "explicit") return;
    const nf = checker.nf.bind(checker);
    checker.nf = (term, context, ...rest) => {
      asked.push(context);
      return nf(term, context, ...rest);
    };
  } } });
  assert.equal(verdicts.explicit, true);
  assert.ok(asked.some(context => [...context.keys()].some(name => name.startsWith("simp_parameter"))));
});

test("binders a call's candidate walks into are bound as it asks about them", async t => {
  const { verdicts } = await checkProgram(t, `
def Ignore2(v, u : Unit) : U0 := Unit;
def take_value{{B : U0}}(f : Unit -> B) : B := f(tt);
def function_(u : Unit) : forall v : Unit. Ignore2(v, u) := fun (v : Unit) => tt;
def taken := take_value(function_);
`, { module });
  assert.equal(verdicts.taken, true);
});

test("the binders a constructor's expected type peels are bound as it asks about their bodies", async t => {
  const { verdicts } = await checkProgram(t, `
inductive I(A : U0) {
  c(x : Unit);
}

def Ix(x : Unit) : U0 := I(Unit);
def f : forall x : Unit. Ix(x) := c;
`, { module });
  assert.deepEqual(verdicts, { I: true, Ix: true, f: true });
});

// The scopes that could not be made while a source was checked, each by its
// error's message: a query asked in one fails, and the constraint that asked
// it waits.
async function failedScopes(t, source) {
  const failed = [], wrapped = new WeakSet();
  const { verdicts } = await checkProgram(t, source, { module, options: { onDeclarationStart: (name, declaration, checker) => {
    if (wrapped.has(checker)) return;
    wrapped.add(checker);
    const scopeOf = checker.scopeOf.bind(checker);
    checker.scopeOf = (...rest) => {
      try { return scopeOf(...rest); }
      catch (error) { failed.push(error.message); throw error; }
    };
  } } });
  return { verdicts, failed };
}

test("the solver asks about a binder's body with the binder at its domain as solved", async t => {
  // Semigroup.Hom.magma, made for the extension, calls Magma.Hom.make with
  // its universes and models as holes. Magma.Hom(U?, V?, A?) unfolds to
  // fun (B : Magma(V?)) => …, and the expected Magma.Hom(U, V, …) to
  // fun (B : Magma(V)) => …: the domains solve V? as V, and the bodies are
  // asked about with B at Magma(V). Bound at Magma(V?), as the domain stood
  // before, B made Magma.M(V, B) in the next binder's type ill-typed.
  const { verdicts, failed } = await failedScopes(t, `import hlevels;

theory Magma(U < UU0) {
  M : set U;
  mul(x, y : M) : M notation x * y;
}

theory Semigroup(U < UU0) extends Magma {
  law mul_assoc(x, y, z : M) : (x * y) * z = x * (y * z);
}
`);
  assert.equal(verdicts.Semigroup, true);
  assert.deepEqual(failed, []);
});

test("a hole solved by a type bounds its universe before the types it enters are asked about", async t => {
  // transpose(naturality(f, g, h, p)): naturality's type solves transpose's
  // A? : U(U?) as B, of the universe U, and its corners and edges, while
  // only that solution bounds U?. The solver's scope binds transpose's s at
  // Square(U?, B, …) with U? at least U, as solving it would make it, and
  // not with U? free, where B is no type in U(U?).
  const { verdicts, failed } = await failedScopes(t, `
def Square{{U < UU0, A : U, a00, a01, a10, a11 : A}}(
  a0_ : a00 = a01, a1_ : a10 = a11, a_0 : a00 = a10, a_1 : a01 = a11
) :
  U := PathP(fun (i : Interval) => a_0 @ i = a_1 @ i, a0_, a1_);

def naturality{{U < UU0, A, B : U, x, y : A}}(
  f, g : A -> B, h : forall a : A. f(a) = g(a), p : x = y
) :
  Square(h(x), h(y), cong(f, p), cong(g, p)) := path i => h(p @ i);

def transpose{{
  U < UU0, A : U, a00, a01, a10, a11 : A, a0_ : a00 = a01, a1_ : a10 = a11, a_0 : a00 = a10,
  a_1 : a01 = a11
}}(s : Square(a0_, a1_, a_0, a_1)) :
  Square(a_0, a_1, a0_, a1_) := path j => path i => s @ i @ j;

def transposed{{U < UU0, A, B : U, x, y : A}}(
  f, g : A -> B, h : forall a : A. f(a) = g(a), p : x = y
) :
  Square(cong(f, p), cong(g, p), h(x), h(y)) := transpose(naturality(f, g, h, p));
`);
  assert.deepEqual(verdicts, { Square: true, naturality: true, transpose: true, transposed: true });
  assert.deepEqual(failed, []);
});

test("a call's candidate keeps the dimensions its scope's variables' types mention", async t => {
  // take(f)(tt) under x : p @ i: take's B would mention f's u, inside
  // PathP(j => Ignore(u), tt, tt), until the candidate is walked into and
  // Ignore(u) asked about. The walk enters j, which the candidate does not
  // place where i is, and keeps i, which x's type mentions.
  const { verdicts } = await checkProgram(t, `
def Ignore(u : Unit) : U0 := Unit;

def take{{B : U0}}(g : Unit -> B) : B := g(tt);

def f(u : Unit) : Unit -> PathP(fun (j : Interval) => Ignore(u), tt, tt) := fun (v : Unit) => refl(tt);

def taken(p : Unit = Unit) :
  PathP(fun (i : Interval) => (p @ i) -> PathP(fun (j : Interval) => Unit, tt, tt),
    fun (x : Unit) => refl(tt), fun (x : Unit) => refl(tt)) :=
  path i => fun (x : p @ i) => take(f)(tt);
`, { module });
  assert.deepEqual(verdicts, { Ignore: true, take: true, f: true, taken: true });
});

test("a decoded term encodes back to its node only where all the node mentions is in scope", async t => {
  // p @ 0 checked where p : Path(j; Unit, x, x) carries that type, which
  // mentions x, as its annotation; its syntax does not. Where p is a path
  // between tt and tt and x is not in scope, it is encoded from its syntax,
  // and a head query does not answer x. So for a dimension only the
  // annotation mentions: q @ i, in i, where the query has none.
  const { checker } = fresh(t), syntax = checker.syntax;
  const path = (left, right) => ({ tag: "Path", dim: "j", family: unit, left, right });
  const at = { tag: "PApp", path: variable("p"), arg: [] }, qi = { tag: "PApp", path: variable("q"), arg: [["i:1"]] };
  const answer = (term, context) => { try { return checker.nf(term, context, new Map()); } catch { return null; } };
  for (const [first, dimensions, second] of [
    [new Map([["x", unit], ["p", path(variable("x"), variable("x"))]]), new Map(), new Map([["p", path(point, point)]])],
    [new Map([["q", path(point, point)], ["p", path(qi, qi)]]), new Map([["i", 0]]), new Map([["q", path(point, point)], ["p", path(point, point)]])]
  ]) {
    const checked = checker.checkSyntax(at, null, first, dimensions);
    assert.equal(syntax.encode(checked.term, dimensions, checker.scopeOf(first, dimensions)), checked.expression);
    assert.notEqual(syntax.encode(checked.term, new Map(), checker.scopeOf(second, new Map())), checked.expression);
    const asked = answer(checked.term, second);
    assert.ok(!asked || asked.tag === "Point", "no answer from what only the annotation mentions");
  }
});
