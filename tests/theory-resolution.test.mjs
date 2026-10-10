import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

const module = await createCubical();
const checked = async (t, source, fixtures = {}) => {
  const library = sourceReader();
  const reader = (name, importer) => fixtures[name] ?? library(name, importer);
  const result = await checkProgram(t, source, {module, reader});
  assert.deepEqual(result.result.gaps, []);
  return result;
};

test("family indices carry captured syntax through generated homomorphisms and isomorphisms", async t => {
  await checked(t, `import fixture;
def k : Nat := succ(zero);
theory Child(U < UU0) extends G {}
def inherited(S : Child(U0)) : S.V(zero) := S.unit;
def identity(S : Child(U0)) : Child.Hom(S, S) := Child.Hom.id(S);
def composite(S : Child(U0)) : Child.Hom(S, S) := Child.Hom.compose(Child.Hom.id(S), Child.Hom.id(S));
def iso(S : Child(U0)) : Child.Iso(S, S) := Child.Iso.compose(Child.Iso.id(S), Child.Iso.id(S));
`, {fixture: `import hlevels;
import nat;
def k : Nat := zero;
theory G(U < UU0) { V(n : Nat) : set U; unit : V(k); base : V(zero); }
`});
});

test("a child may reuse its imported parent's name without redirecting parent references", async t => {
  await checked(t, `import fixture;
theory T(U < UU0) extends T { extra : M; }
def inherited(S : T(U0)) : S.M := original(S.t);
def parent_map(S : T(U0)) := T.Hom.t(T.Hom.id(S));
`, {fixture: `import hlevels;
theory T(U < UU0) { M : set U; point : M; }
def original(S : T(U0)) : S.M := S.point;
`});
});

test("a local model projection stays distinct from the generated declaration of the same spelling", async t => {
  for (const local of ["T", "other"]) {
    await checked(t, `import hlevels;
theory P(U < UU0) { M : set U; x : M; }
theory T(U < UU0) { M : set U; op(${local} : P(U), y : ${local}.M) : M; }
def apply(S : T(U0), p : P(U0)) : S.M := S.op(p, p.x);
`);
  }
});

test("template holes cannot capture a user's parameter or family-index names", async t => {
  for (const binder of ["__theory_type_0", "__theory_parameter_0", "__theory_reference"]) {
    await checked(t, `import hlevels;
import nat;
theory T(U < UU0, ${binder} : Nat) { V(n : Nat) : set U; point : V(${binder}); }
def identity(S : T(U0, zero)) : T.Hom(S, S) := T.Hom.id(S);
`);
  }
});

test("a captured field global can be shadowed by the generated model's name", async t => {
  await checked(t, `import hlevels;
def A : U0 := Unit;
theory T(U < UU0) { M : set U; point(a : A) : M; }
initial A : T(U0);
def use_it : A := A.point(tt);
free W(A : U0) : T(U0) on A;
def free_argument : W(Nat) := W.point(tt);
`);
});

test("initial and free models retain imported global types and law constants", async t => {
  await checked(t, `import fixture;
def A : U0 := Nat;
def k : Nat := succ(zero);
initial N : T(U0);
free W(B : U0) : T(U0) on B;
def argument : N := N.point(tt);
def boundary : N.number(zero) = N.number(zero) := N.at_k;
def free_argument(B : U0) : W(B) := W.point(tt);
def folded(B : U0, S : T(U0), g : B -> S.M) :
  W.fold(B, S, g).map(W.point(tt)) = S.point(tt) { rfl; }
`, {fixture: `import hlevels;
import nat;
def A : U0 := Unit;
def k : Nat := zero;
theory T(U < UU0) {
  M : set U;
  point(a : A) : M;
  number(n : Nat) : M;
  law at_k : number(k) = number(k);
}`});
});

test("inherited fields and derived operations keep globals when the child shadows them", async t => {
  await checked(t, `import fixture;
def A : U0 := Nat;
def k : Nat := succ(zero);
theory Child(U < UU0) extends Parent {}
initial N : Child(U0);
def argument : N := N.point(tt);
def boundary : N.number(zero) = N.number(zero) := N.at_k;
def derived(S : Child(U0)) : S.number(zero) = S.named(tt) { rfl; }
def parent(S : Child(U0)) : Unit -> S.M := S.parent.point;
`, {fixture: `import hlevels;
import nat;
def A : U0 := Unit;
def k : Nat := zero;
theory Parent(U < UU0) {
  M : set U;
  point(a : A) : M;
  number(n : Nat) : M;
  def named(u : Unit) : M := number(k);
  law at_k : named(tt) = number(k);
}`});
});

test("inheritance retains each parent's notation and leaves the child's notation local", async t => {
  await checked(t, `import fixture;
notation shifted { numeral(n : Nat) := succ(n); }
use shifted;
theory Child(U < UU0) extends Parent { law own : number(0) = number(0); }
initial N : Child(U0);
def inherited : N.number(zero) = N.number(zero) := N.base;
def own : N.number(succ(zero)) = N.number(succ(zero)) := N.own;
`, {fixture: `import hlevels;
import nat;
use nat;
theory Parent(U < UU0) {
  M : set U;
  number(n : Nat) : M;
  law base : number(0) = number(0);
}`});
});

test("explicit notation selections keep their declaration when that notation name is rebound", async t => {
  await checked(t, `import fixture;
notation fixed { numeral(n : Nat) := succ(n); }
initial N : T(U0);
theory Child(U < UU0) extends T {}
initial C : Child(U0);
def original : N.number(zero) = N.number(zero) := N.base;
def inherited : C.number(zero) = C.number(zero) := C.base;
`, {fixture: `import hlevels;
import nat;
notation fixed { numeral(n : Nat) := n; }
theory T(U < UU0) { M : set U; number(n : Nat) : M; law base : number(fixed.(0)) = number(zero); }`});
});

test("a fold's h-level helper keeps the theory's definition when the caller rebinds IsSet", async t => {
  await checked(t, `import fixture;
def IsSet : U0 := Unit;
initial N : T(U0);
free W(A : U0) : T(U0) on A;
def folded(S : T(U0)) : N.fold(S).map(N.c) = S.c { rfl; }
`, {fixture: `import hlevels; theory T(U < UU0) { M : set U; c : M; }`});
});

test("a model's projections and selected fields use its original theory after that name is rebound", async t => {
  await checked(t, `import fixture;
theory T(U < UU0) { M : set U; extra : Nat; c : M; }
def direct : Unit := source.c;
def expression : Unit := (fun (x : Unit) => source)(tt).c;
def opened : Unit { use source; exact c; }
`, {fixture: `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
def source : T(U0) := T.make(Unit, prop_is_set(U0, Unit, unit_is_prop), tt);`});
});

test("a captured global cannot become a later field or an inlined operation's binder", async t => {
  await checked(t, `import hlevels;
import nat;
def A : U0 := Unit;
def k : Nat := zero;
theory T(U < UU0) {
  M : set U;
  point(a : A) : M;
  number(n : Nat) : M;
  def original(u : Unit) : M := number(k);
  A : M;
  law local(k : Nat) : original(tt) = number(zero);
}
initial N : T(U0);
def argument : N := N.point(tt);
def bound(k : Nat) : N.number(zero) = N.number(zero) := N.local(k);
`);
});

test("generated projections and homomorphisms cannot be captured by an operation binder", async t => {
  await checked(t, `import hlevels;
theory T(U < UU0) { M : set U; op(T : M) : M; }
initial N : T(U0);
def preserved(S : T(U0), x : N) :
  N.fold(S).map(N.op(x)) = S.op(N.fold(S).map(x)) { rfl; }
`);
});

test("grouped header domains resolve before their binders and later domains see those binders", async t => {
  await checked(t, `import hlevels;
def A : U0 := Unit;
theory T(U < UU0, A, x : A, p : x = A) { M : set U; c : M; }
initial N : T(U0, tt, tt, refl(tt));
`);
});

test("grouped operation and derived parameters preserve their shared outer domain", async t => {
  await checked(t, `import hlevels;
def A : U0 := Unit;
theory T(U < UU0) {
  M : set U;
  op(A, x : A) : M;
  def derived(A, x : A) : M := op(A, x);
  def from_carrier(M, x : M) : Unit := tt;
}
initial N : T(U0);
def argument : N := N.op(tt, tt);
def derived(S : T(U0)) : S.derived(tt, tt) = S.op(tt, tt) { rfl; }
def local(S : T(U0), x : S.M) : Unit := S.from_carrier(x, x);
theory P(U < UU0, A : U0) { M : set U; op(A, x : A) : M; }
initial W : P(U0, Unit);
def parameter : W := W.op(tt, tt);
`);
});

test("recursive derived operations retain their recursive binder with captured globals", async t => {
  await checked(t, `import fixture;
def k : Nat := succ(zero);
theory Child(U < UU0) extends T {}
def recursive(S : Child(U0)) : S.iterate(succ(zero)) = S.op(S.number(zero)) { rfl; }
`, {fixture: `import hlevels;
import nat;
def k : Nat := zero;
theory T(U < UU0) {
  M : set U;
  number(n : Nat) : M;
  op(T : M) : M;
  def iterate(n : Nat) : M := match n { zero => number(k); succ(m) => op(iterate(m)); };
}`});
});

test("equal header notation stays compatible across extends, and changed notation does not", async t => {
  const {program} = await checked(t, `import hlevels;
import nat;
use nat;
theory P(U < UU0, p : 0 = 0) { M : set U; c : M; }
theory C(U < UU0, p : 0 = 0) extends P {}
`);
  const result = await program.check(`import hlevels;
import nat;
use nat;
theory P(U < UU0, p : 0 = 0) { M : set U; c : M; }
notation shifted { numeral(n : Nat) := succ(n); }
use shifted;
theory C(U < UU0, p : 0 = 0) extends P {}
`, "different");
  assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), [["C", "E821"]]);
});

test("independent parents retain different bindings with the same source spelling", async t => {
  await checked(t, `import first;
import second;
theory Child(U < UU0) extends P, Q {}
initial N : Child(U0);
def first_argument : N := N.first(tt);
def second_argument : N := N.second(zero);
`, {
    first: `import hlevels; def A : U0 := Unit; theory P(U < UU0) { M : set U; first(a : A) : M; }`,
    second: `import hlevels; import nat; def A : U0 := Nat; theory Q(U < UU0) { M : set U; second(a : A) : M; }`,
  });
});

test("copied model projections preserve both the receiver and the theory's projection binding", async t => {
  await checked(t, `import fixture;
theory Item(U < UU0) { M : set U; extra : Nat; c : M; }
def source : Item(U0) := Item.make(Nat, nat_is_set, zero, zero);
initial N : P(U0);
def original : N := N.point(tt);
def boundary : N.point(tt) = N.point(tt) := N.at_source;
`, {fixture: `import hlevels;
theory Item(U < UU0) { M : set U; c : M; }
def source : Item(U0) := Item.make(Unit, prop_is_set(U0, Unit, unit_is_prop), tt);
theory P(U < UU0) { M : set U; point(a : source.M) : M; law at_source : point(source.c) = point(source.c); }`});
});

test("inlined proposition helpers retain declared proposition identities", async t => {
  await checked(t, `import hlevels;
import h1_truncation;
inductive P : prop U0 { proof_point; }
theory T(U < UU0) {
  M : set U;
  def Q(a : Unit) : U0 := P;
  def merely(A : U) : U := Trunc(U, A);
  law ok : Q(tt);
  law inhabited : merely(M);
}
`);
  await checked(t, `import fixture;
inductive P : set U0 { replacement; }
theory Child(U < UU0) extends Parent { law ok : Q(tt); }
`, {fixture: `import hlevels;
inductive P : prop U0 { proof_point; }
theory Parent(U < UU0) { M : set U; def Q(a : Unit) : U0 := P; }
`});
});

test("a captured data type cannot become a proposition through a rebound spelling", async t => {
  const library = sourceReader();
  const fixture = `import hlevels;
inductive P : set U0 { data_point; }
theory Parent(U < UU0) { M : set U; def Q(a : Unit) : U0 := P; }
`;
  const {result} = await checkProgram(t, `import fixture;
inductive P : prop U0 { replacement; }
theory Child(U < UU0) extends Parent { law invalid : Q(tt); }
`, {module, reader: (name, importer) => name === "fixture" ? fixture : library(name, importer)});
  assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), [["Child", "E818"]]);
});

test("inherited notation keeps the complete operand tree in its original selection", async t => {
  for (const [crossModule, selected] of [[false, true], [true, true], [true, false]]) for (const operand of ["0 + 0", "0"]) {
    const parent = `import hlevels;
import nat;
use nat;
theory P(U < UU0) { M : set U; point(n : Nat) : M; law base : point(${operand}) = point(0); }
`;
    const child = `${selected ? "notation shifted { numeral(n : Nat) := succ(n); }\nuse shifted;" : ""}
theory Q(U < UU0) extends P { law own : point(${selected ? "0" : "succ(zero)"}) = point(${selected ? "0" : "succ(zero)"}); }
initial N : Q(U0);
free W(A : U0) : Q(U0) on A;
def original : N.point(zero) = N.point(zero) := N.base;
def free_original(A : U0) : typed(W(A), W.point(zero)) = W.point(zero) := W.base;
def local : N.point(succ(zero)) = N.point(succ(zero)) := N.own;
def parent(S : Q(U0)) : P(U0) := S.p;
def parent_hom(S : Q(U0)) : P.Hom(S.p, S.p) := Q.Hom.p(Q.Hom.id(S));
`;
    await checked(t, crossModule ? `import fixture;\n${child}` : parent + child, {fixture: parent});
  }
});
