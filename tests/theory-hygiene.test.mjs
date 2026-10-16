import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

const module = await createCubical();
const check = async (t, source, fixtures = {}) => {
  const library = sourceReader();
  return checkProgram(t, source, {module, reader: (name, importer) => fixtures[name] ?? library(name, importer)});
};
const verified = async (t, source, fixtures) => {
  const result = await check(t, source, fixtures);
  assert.deepEqual(result.result.gaps, []);
  return result;
};

test("theory capture uses opened fields before globals and retains them across imports and selections", async t => {
  const parent = `import hlevels; import nat; import algebra;
def A : U0 := Unit;
def one : Nat := zero;
theory P(U < UU0) { A : set U; a : A; }
def p : P(U0) := P.make(Nat, nat_is_set, zero);
def multiplicative : Monoid(U0) := nat_multiplicative.monoid;
use p; use multiplicative;
theory T(U < UU0) { M : set U; point(n : A) : M; law l : point(one) = point(nat.(1)); }
def original(S : T(U0)) : Nat -> S.M := S.point;
def boundary(S : T(U0)) : S.point(nat.(1)) = S.point(nat.(1)) := S.l;
theory Parameterized(U < UU0, a : A) { M : set U; c : M; }
theory Same(U < UU0, a : A) extends Parameterized {}
`;
  const child = `def A : U0 := Unit;
def additive_ : Monoid(U0) := nat_additive.monoid;
use additive_;
theory Child(U < UU0) extends T {}
initial N : Child(U0);
free W(B : U0) : T(U0) on B;
def point : N := N.point(zero);
def boundary_path : N.point(nat.(1)) = N.point(nat.(1)) := N.l;
def free_path(B : U0) : typed(W(B), W.point(nat.(1))) = W.point(nat.(1)) := W.l;
`;
  await verified(t, `import fixture;\n${child}`, {fixture: parent});
  await verified(t, parent + child.replace("def A : U0 := Unit;", ""));
});

test("theory capture respects ring zero opened over Nat's zero", async t => {
  await verified(t, `import nat; import hlevels; import algebra; import integers;
use integers;
theory Scaled(U < UU0) { M : set U; scale(r : Z, x : M) : M;
  law scale_zero(x, y : M) : scale(zero, x) = scale(zero, y); }
`);
});

test("resolved qualified syntax preserves diagnostic categories and receiver spelling", async t => {
  const prefix = `import hlevels; import nat; import algebra;
inductive Box(A : U0) : U0 { box(a : A); }
def m : Nat := zero;
theory Arrow(U < UU0) { M : set U; op : M -> M; }
`;
  for (const [field, code, message] of [
    ["point(n : Nat) : M; law bad(n : Nat) : point(Box.box(n)) = point(n);", "E343", /Box\.box/],
    ["point(n : Nat) : M; law bad : point(Nat.zero) = point(zero);", "E343", /Nat\.zero/],
    ["point(n : Nat) : M; law bad : point(m.x) = point(zero);", "E343", /m\.x/],
    ["point(a, b : Arrow(U), f : Arrow.Hom(a, b)) : M;", "E817", /Arrow's models/],
    ["point(x : Monoid.Model(U)) : M;", "E396", /Monoid.Model is now Monoid/],
    ["point(Monoid : Nat) : M; law bad(Monoid : Nat) : point(Monoid.one) = point(Monoid);", "E862", /Monoid is bound here/],
    ["point(R : Monoid(U), x : R.nope) : M;", "E815", /R is a model/],
  ]) {
    const {result} = await check(t, `${prefix} theory T(U < UU0) { M : set U; ${field} }`);
    const gap = result.gaps[0];
    assert.equal(gap?.code, code, JSON.stringify(result.gaps));
    assert.match(gap.reason, message);
    assert.ok(result.gaps.every(g => !g.reason.includes("\u0000")));
  }
});

test("diagnostics for captured names never expose private binding keys", async t => {
  const prefix = `import hlevels; import nat; def m : Nat := zero;
inductive Box(A : U0) : U0 { box(a : A); }
notation weird { x + y := succ(x); }
`;
  for (const [fields, code, spelling] of [
    ["point(b : Box(_)) : M;", "E379", /Box is a declared type/],
    ["f(n : Nat) : M; law l : f(m m.(+) m) = f(m);", "E835", /m\.\(\+\) takes/],
    ["g(h : Nat -> Nat -> Nat) : M; law l : g(weird.(+)) = g(weird.(+));", "E398", /weird\.\(\+\) is an operation/],
  ]) {
    const {result} = await check(t, `${prefix} theory T(U < UU0) { M : set U; ${fields} }`);
    assert.equal(result.gaps[0]?.code, code, JSON.stringify(result.gaps));
    assert.match(result.gaps[0].reason, spelling);
    assert.ok(result.gaps.every(g => !g.reason.includes("\u0000")));
  }
});

test("generated evidence links nowhere and written compound headers link once", async t => {
  for (const header of ["initial N : Monoid(U0);", "free W(A : U0) : Monoid(U0) on A -> A;", "free W(A : U0) : Monoid(U0) on exists a : A. A;"]) {
    const source = `import hlevels; import algebra; ${header}`;
    const {result} = await verified(t, source);
    assert.ok(result.links.every(link => link.start >= 0 && link.end <= source.length), JSON.stringify(result.links));
    for (const spelling of ["->", "exists"]) if (header.includes(spelling)) {
      const start = source.indexOf(spelling);
      assert.equal(result.links.filter(link => link.start === start && link.end === start + spelling.length).length, 1);
    }
  }
});

test("freshened parameters and operation arguments keep their public names in diagnostics and inspection", async t => {
  const {result, program, get} = await check(t, `import hlevels; import algebra;
free W(M : U0) : Monoid(U0) on M;
def x : W := W.one;
def y : W(Unit, Unit) := W.one;
theory Iterated(U < UU0, g : U) { M : set U; iterate(g : M -> M, x : M) : M; }
def h(S : Iterated(U0, Unit)) := Iterated.Hom.id(S);
theory T(U < UU0) { M : set U; op(a : Unit) : forall a : U0. M; }
initial N : T(U0);
`);
  for (const gap of result.gaps) assert.doesNotMatch(gap.reason, /′|argument g1|argument a1/);
  assert.match(result.gaps.find(g => g.name === "y").reason, /W\(M\)/);
  assert.match(result.gaps.find(g => g.name === "h").reason, /argument g /);
  assert.match(result.gaps.find(g => g.name === "N").reason, /argument a /);
  const signature = program.signatureView(get("W").binding);
  assert.equal(signature.constructors.find(c => c.name === "W.gen").type, "M -> W");
  assert.doesNotMatch(JSON.stringify(signature), /′/);
  await verified(t, `import hlevels; import algebra;
free S(IsSet : U0) : Monoid(U0) on IsSet;
free P(IsProp : U0) : Monoid(U0) on IsProp;
def s : S(Unit) := S.gen(tt);
def p : P(Unit) := P.gen(tt);
`);
});

test("inherited greater-than comparisons retain their complete lexical selection", async t => {
  for (const operator of [">", ">="]) {
    await verified(t, `import hlevels; import nat; use nat;
theory P(U < UU0) { M : set U; point(n : Nat, p : n ${operator} 0) : M; }
notation shifted { numeral(n : Nat) := succ(n); }
use shifted;
theory Q(U < UU0) extends P {}
initial N : Q(U0);
free W(A : U0) : P(U0) on A;
`);
  }
});

test("substitution considers enclosing binders before refusing a fixed pattern capture", async t => {
  await verified(t, `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M;
  def pick(x : M, n : Nat) : M := (fun (x : M) => match n return M { zero => x; succ(k) => x; })(c);
  law l(k : M) : pick(k, zero) = c;
}
`);
});

test("inlining preserves a helper's free fields under a caller's binders", async t => {
  for (const binder of ["c", "x"]) await verified(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  law l(${binder} : M) : k(${binder}) = op(${binder}, ${binder});
}
def boundary(S : T(U0), x : S.M) : S.op(x, S.c) = S.op(x, x) := S.l(x);
initial N : T(U0);
def initial_boundary(x : N) : N.op(x, N.c) = N.op(x, x) := N.l(x);
`);
});

test("inlining refuses capture by an enclosing fixed pattern with a focused diagnostic", async t => {
  const {result} = await check(t, `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M;
  def k(n : Nat) : M := c;
  law l(n : Nat) : (match n return M { zero => k(zero); succ(c) => k(c); }) = c;
}
`);
  assert.deepEqual(result.gaps.map(g => g.code), ["E871"]);
  assert.match(result.gaps[0].reason, /Inlining k here would capture its field c/);
});

test("generated recursive calls retain their declaration under same-named parameters and patterns", async t => {
  for (const [parameter, pattern] of [["T", "n"], ["n", "T"]]) await verified(t, `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; op(x : M) : M;
  def iter(${parameter} : Nat) : M := match ${parameter} { zero => c; succ(${pattern}) => op(iter(${pattern})); };
}
def computes(S : T(U0)) : S.iter(succ(zero)) = S.op(S.c) { rfl; }
`);
});

test("ordinary declared types elaborate their constructors in the file's selected notation", async t => {
  await verified(t, `import nat; use nat;
inductive V : U0 { v(p : 1 + 1 = 2); }
def point : V := v(refl(2));
`);
});

test("catch-all path clauses respect recursive boundaries and require coherence", async t => {
  await verified(t, `import hlevels; import algebra;
inductive H : set U0 { first; second; p(y : H) : y = y; }
def k(x : H) : Unit := match x { first => tt; _ => tt; };
def computes : k(second) = tt { rfl; }
initial N : Monoid(U0);
def forget(x : N) : Unit := match x { N.one => tt; _ => tt; };
`);
  const {result} = await check(t, `import hlevels; import nat;
inductive H : set U0 { first; second; p : first = second; }
def bad(x : H) : Nat := match x { first => zero; _ => succ(zero); };
`);
  assert.ok(result.gaps.some(g => g.name === "bad"));
});

test("initial and free reject untruncated carriers and non-carrier-valued operations", async t => {
  const {result} = await check(t, `import hlevels; import nat;
theory Raw(U < UU0) { M : U; }
theory Sized(U < UU0) { M : set U; size(x : M) : Nat; }
initial R : Raw(U0);
free F(A : U0) : Raw(U0) on A;
initial S : Sized(U0);
free G(A : U0) : Sized(U0) on A;
`);
  assert.deepEqual(result.gaps.map(g => [g.name, g.code]), [["R", "E853"], ["F", "E853"], ["S", "E855"], ["G", "E855"]]);
});
