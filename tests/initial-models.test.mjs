import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkProgram } from "./check-program.mjs";

const module = await createCubical();
const verified = async (t, source) => {
  const checked = await checkProgram(t, source, { module });
  assert.equal(checked.result.complete, true, JSON.stringify(checked.result.gaps));
  return checked;
};

test("initial and free models substitute a theory parameter in projections without capturing law binders", async t => {
  await verified(t, `import hlevels;
import algebra;
import nat;
theory Action(U < UU0, R : Monoid(U)) {
  M : set U;
  act(r : R.M, x : M) : M;
  law unit(S : M) : act(R.one, S) = S;
}
initial N : Action(U0, nat_additive.monoid);
free W(S : Monoid(U0), A : U0) : Action(U0, S) on A;
def unit_path(S : Monoid(U0), A : U0, x : W(S, A)) : W.act(S.one, x) = x := W.unit(x);
def folded(S : Monoid(U0), A : U0, T : Action(U0, S), g : A -> T.M, r : S.M, a : A) :
  W.fold(S, A, T, g).map(W.act(r, W.gen(a))) = T.act(r, g(a)) { rfl; }
`);
});

test("free folds preserve function and dependent pair generator types", async t => {
  await verified(t, `import hlevels;
import algebra;
free Functions(A, B : U0) : Monoid(U0) on A -> B;
free Pairs(A : U0, B : A -> U0) : Monoid(U0) on exists a : A. B(a);
def function_fold(A, B : U0, S : Monoid(U0), g : (A -> B) -> S.M, a : A -> B) :
  Functions.fold(A, B, S, g).map(Functions.gen(a)) = g(a) { rfl; }
def pair_fold(A : U0, B : A -> U0, S : Monoid(U0), g : (exists a : A. B(a)) -> S.M, a : exists a : A. B(a)) :
  Pairs.fold(A, B, S, g).map(Pairs.gen(a)) = g(a) { rfl; }
`);
});

test("grouped equational law binders keep their shared domain and avoid capturing free-model parameters", async t => {
  await verified(t, `import hlevels;
theory Equal(U < UU0) {
  M : set U;
  c : M;
  law all : forall x, y : M. x = y;
  law shared : forall M, y : M. M = y;
  law capture : forall A, y : M. A = y;
}
initial N : Equal(U0);
free W(A : U0) : Equal(U0) on A;
def all_path(x, y : N) : x = y := N.all(x, y);
def shared_path(x, y : N) : x = y := N.shared(x, y);
def capture_path(A : U0, x, y : W(A)) : x = y := W.capture(x, y);
`);
});

test("initial and free models resolve named and mixed theory arguments by parameter name", async t => {
  await verified(t, `import hlevels;
import algebra;
initial N : Monoid(U := U0);
theory Pointed(U < UU0, A : U) { M : set U; point(a : A) : M; }
initial P : Pointed(A := Unit, U := U0);
initial Mixed : Pointed(A := Unit, U0);
free W(B : U0) : Pointed(A := B, U := U0) on B;
def point_fold(B : U0, S : Pointed(U0, B), g : B -> S.M, b : B) :
  W.fold(B, S, g).map(W.point(b)) = S.point(b) { rfl; }
def unit_fold(S : Monoid(U0)) : N.fold(S).map(N.one) = S.one { rfl; }
`);
});

test("invalid named theory arguments refuse the expansion before publishing constructors", async t => {
  const { result } = await checkProgram(t, `import hlevels;
theory Pointed(U < UU0, A : U) { M : set U; point(a : A) : M; }
initial Unknown : Pointed(V := U0, A := Unit);
initial Twice : Pointed(U := U0, U := U0);
initial Missing : Pointed(U := U0);
`, { module });
  const failures = result.outputs.filter(output => !output.verified);
  assert.deepEqual(failures.map(output => [output.name, output.code]), [["Unknown", "E375"], ["Twice", "E377"], ["Missing", "E851"]]);
  assert.ok(result.outputs.every(output => !/^(Unknown|Twice|Missing)\./.test(output.name)));
});
