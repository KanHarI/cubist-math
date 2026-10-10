import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkProgram } from "./check-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { lawRefusal } from "../web/translator/initial-models.mjs";

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

test("inferred theory universes survive initial and parameterized free expansion", async t => {
  await verified(t, `import hlevels;
theory T(U < UU0, A : U) { M : set U; point(a : A) : M; }
initial N : T(_, Unit);
initial Named : T(A := Unit, U := _);
free W(V < UU0, A : V) : T(_, A) on A;
free Capturing(T : U0) : T(_, T) on T;
def initial_fold(S : T(U0, Unit)) : N.fold(S).map(N.point(tt)) = S.point(tt) { rfl; }
def named_fold(S : T(U0, Unit)) : Named.fold(S).map(Named.point(tt)) = S.point(tt) { rfl; }
def generic_fold(V < UU0, A : V, S : T(V, A), g : A -> S.M, a : A) :
  W.fold(V, A, S, g).map(W.point(a)) = S.point(a) { rfl; }
def generic_generator(V < UU0, A : V, S : T(V, A), g : A -> S.M, a : A) :
  W.fold(V, A, S, g).map(W.gen(a)) = g(a) { rfl; }
def renamed_parameter(A : U0, S : T(U0, A), g : A -> S.M, a : A) :
  Capturing.fold(T := A, S, g).map(Capturing.point(a)) = S.point(a) { rfl; }
`);
});

test("inferred theory types survive constructor domains and law boundaries", async t => {
  await verified(t, `import hlevels;
theory T(U < UU0, A : U, a : A) {
  M : set U;
  point(x : A) : M;
  law at_parameter : point(a) = point(a);
}
initial N : T(U0, _, tt);
free W(V < UU0, A : V, a : A) : T(V, _, a) on A;
def initial_path : N.point(tt) = N.point(tt) := N.at_parameter;
def free_path(V < UU0, A : V, a : A) :
  typed(W(V, A, a), W.point(a)) = W.point(a) := W.at_parameter;
def initial_fold(S : T(U0, Unit, tt)) : N.fold(S).map(N.point(tt)) = S.point(tt) { rfl; }
def free_fold(V < UU0, A : V, a : A, S : T(V, A, a), g : A -> S.M, x : A) :
  W.fold(V, A, a, S, g).map(W.point(x)) = S.point(x) { rfl; }
`);
});

test("inherited theories without universe headers have initial and free models at their generated universe", async t => {
  await verified(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
theory Child extends T {}
theory Parameterized(n : Unit) extends Child {}
initial N : Child(U0);
initial Named : Child(U := U0);
initial P : Parameterized(n := tt, U := U0);
free W(V < UU0, A : V) : Child(V) on A;
free Q(A : U0) : Parameterized(U0, tt) on A;
theory Numbered extends T { op(U : M) : M; }
initial K : Numbered(U := U0);
def folded(S : Child(U0)) : N.fold(S).map(N.c) = S.c { rfl; }
def parameter_fold(S : Parameterized(U0, tt)) : P.fold(S).map(P.c) = S.c { rfl; }
def generator_fold(V < UU0, A : V, S : Child(V), g : A -> S.M, a : A) :
  W.fold(V, A, S, g).map(W.gen(a)) = g(a) { rfl; }
def parameter_generator_fold(A : U0, S : Parameterized(U0, tt), g : A -> S.M, a : A) :
  Q.fold(A, S, g).map(Q.gen(a)) = g(a) { rfl; }
`);
});

test("an inherited theory still requires its generated universe argument", async t => {
  const {result} = await checkProgram(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
theory Child extends T {}
initial N : Child;
free W(A : U0) : Child on A;`, {module});
  const failures = result.outputs.filter(o => !o.verified);
  assert.deepEqual(failures.map(o => [o.name, o.code]), [["N", "E851"], ["W", "E851"]]);
  assert.ok(failures.every(o => /Child takes 1 argument/.test(o.reason)));
});

test("shadowed operation and law quantifiers keep their scopes in constructors and folds", async t => {
  await verified(t, `import hlevels;
theory T(U < UU0) {
  M : set U;
  c : M;
  op : forall x : M. forall x : M. M;
  law l : forall x : M. forall x : M. x = x;
  law grouped : forall x : M. forall x, y : M. op(x, y) = y;
  law dependent : forall x : Unit. forall x : Unit. forall p : x = x. c = c;
}
initial N : T(U0);
free W(A : U0) : T(U0) on A;
def inner_scope(x, y : N) : y = y := N.l(x, y);
def grouped_scope(x, y, z : N) : N.op(y, z) = z := N.grouped(x, y, z);
def dependent_scope(x, y : Unit, p : y = y) : N.c = N.c := N.dependent(x, y, p);
def free_scope(A : U0, x, y : W(A)) : y = y := W.l(x, y);
def initial_fold(S : T(U0), x, y : N) :
  N.fold(S).map(N.op(x, y)) = S.op(N.fold(S).map(x), N.fold(S).map(y)) { rfl; }
def free_fold(A : U0, S : T(U0), g : A -> S.M, a, b : A) :
  W.fold(A, S, g).map(W.op(W.gen(a), W.gen(b))) = S.op(g(a), g(b)) { rfl; }
`);
});

test("the equational strategy refuses carrier-dependent domains before declaring a model", async t => {
  for (const field of ["op(x : M, p : x = x) : M;", "law l(x : M, p : x = c) : x = c;", "op(p : c = c) : M;"]) {
    const {result} = await checkProgram(t, `import hlevels;
theory D(U < UU0) { M : set U; c : M; ${field} }
initial N : D(U0);
def after := tt;`, {module});
    assert.deepEqual(result.outputs.filter(o => o.name === "N" || o.name.startsWith("N.")).map(o => [o.name, o.code]), [["N", "E854"]]);
    assert.ok(result.outputs.at(-1).verified);
  }
  // Dependence on an independent argument stays supported.
  await verified(t, `import hlevels;
theory P(U < UU0) { M : set U; op(x : Unit, p : x = x) : M; }
initial N : P(U0);`);
});

test("free generators are independent of the new type and its generated namespace", async t => {
  for (const on of ["W", "W.model.M", "W.fold", "W.gen", "W.squash", "W -> Unit"]) {
    const source = `import hlevels; import algebra; free W : Monoid(U0) on ${on};`;
    const {result} = await checkProgram(t, source, {module});
    assert.deepEqual(result.outputs.map(o => [o.name, o.code]), [["W", "E863"]]);
    assert.equal(result.outputs[0].errorStart, source.indexOf(on, source.indexOf(" on ")));
  }
  // A bound name in the generator type does not refer to the new type.
  await verified(t, `import hlevels; import algebra;
free W : Monoid(U0) on forall W : Unit. Unit;
free V(V : U0) : Monoid(U0) on V;`);
});

test("free parameters cannot capture globals used by theory fields or generated definitions", async t => {
  await verified(t, `import hlevels; import algebra; import nat; use nat;
theory P(U < UU0) { M : set U; point(n : Nat) : M; }
free W(Nat : U0) : P(U0) on Nat;
free H(IsSet, IsProp, P : U0) : P(U0) on IsSet;
def global_argument(A : U0, S : P(U0), g : A -> S.M, n : Nat) :
  W.fold(Nat := A, S, g).map(W.point(n)) = S.point(n) { rfl; }
def generator_argument(A : U0, S : P(U0), g : A -> S.M, a : A) :
  W.fold(A, S, g).map(W.gen(a)) = g(a) { rfl; }
free Dep(Nat : U0, A : Nat -> U0) : P(U0) on exists n : Nat. A(n);
`);
});

test("initial and free constructors and folds share file-level notation", async t => {
  await verified(t, `import hlevels; import nat; use nat;
theory P(U < UU0, n : Nat) { M : set U; point(p : n = n) : M; }
initial N : P(U0, 3);
free W(A : U0) : P(U0, 3) on A;
def folded(S : P(U0, 3), p : 3 = 3) : N.fold(S).map(N.point(p)) = S.point(p) { rfl; }
`);
});

const notationTheory = `import hlevels;
import nat;
use nat;
theory T(U < UU0, k : Nat) {
  M : set U;
  op(n : Nat, p : n = 0) : M;
  point(n : Nat) : M;
  law base : point(0 + 0) = point(0);
  law index : point(k) = point(k);
}`;
const notationReader = (source = notationTheory) => {
  const library = sourceReader();
  return (name, importer) => name === "notation_theory" ? source : library(name, importer);
};

test("imported initial and free fields keep the theory's notation without a caller selection", async t => {
  const source = `import notation_theory;
initial N : T(U0, zero);
free W(A : U0) : T(U0, zero) on A;
def operation : N := N.op(zero, refl(zero));
def boundary : N.point(zero) = N.point(zero) := N.base;
def free_boundary(A : U0) : typed(W(A), W.point(zero)) = W.point(zero) := W.base;
def folded(S : T(U0, zero)) : N.fold(S).map(N.op(zero, refl(zero))) = S.op(zero, refl(zero)) { rfl; }
`;
  const {result} = await checkProgram(t, source, {module, reader: notationReader()});
  assert.deepEqual(result.gaps, []);
  // A copied rule's source offsets belong to the imported module, never here.
  assert.ok(result.links.every(link => link.start >= 0 && link.end <= source.length));
});

test("copied fields keep theory notation while free parameters, theory arguments and generators keep caller notation", async t => {
  const {result} = await checkProgram(t, `import notation_theory;
notation shifted { numeral(n : Nat) := succ(n); }
use shifted;
initial N : T(U0, 0);
free W(p : 0 = 0) : T(U0, 0) on 0 = 0;
def operation : N := N.op(zero, refl(zero));
def boundary : N.point(zero) = N.point(zero) := N.base;
def argument : N.point(succ(zero)) = N.point(succ(zero)) := N.index;
def generator(p : succ(zero) = succ(zero), a : succ(zero) = succ(zero)) : W(p) := W.gen(a);
def model_type(p : succ(zero) = succ(zero)) : T(U0, succ(zero)) := W.model(p);
def folded(p : succ(zero) = succ(zero), S : T(U0, succ(zero)), g : (succ(zero) = succ(zero)) -> S.M) :
  W.fold(p, S, g).map(W.gen(p)) = g(p) { rfl; }
`, {module, reader: notationReader()});
  assert.deepEqual(result.gaps, []);
});

test("a caller rebinding a notation name cannot change an imported theory's captured rules", async t => {
  const {result} = await checkProgram(t, `import notation_theory;
notation nat { numeral(n : Nat) := succ(n); }
use nat;
initial N : T(U0, 0);
free W(nat : U0) : T(U0, 0) on nat;
def operation : N := N.op(zero, refl(zero));
def boundary : N.point(zero) = N.point(zero) := N.base;
def argument : N.point(succ(zero)) = N.point(succ(zero)) := N.index;
def free_boundary(A : U0) : typed(W(A), W.point(zero)) = W.point(zero) := W.base;
`, {module, reader: notationReader()});
  assert.deepEqual(result.gaps, []);
});

test("captured model notation survives a model or free parameter taking its name", async t => {
  const reader = notationReader(`import hlevels;
import nat;
theory Arithmetic(U < UU0) { K : set U; plus(x, y : K) : K notation x + y; }
def arithmetic : Arithmetic(U0) := Arithmetic.make(Nat, nat_is_set, add);
use arithmetic;
theory T(U < UU0) {
  M : set U;
  point(n : Nat) : M;
  law base : point(zero + zero) = point(zero);
}`);
  const {result} = await checkProgram(t, `import notation_theory;
initial arithmetic : T(U0);
free W(arithmetic : U0) : T(U0) on arithmetic;
def boundary : arithmetic.point(zero) = arithmetic.point(zero) := arithmetic.base;
def free_boundary(A : U0) : typed(W(A), W.point(zero)) = W.point(zero) := W.base;
`, {module, reader});
  assert.deepEqual(result.gaps, []);
});

test("ill-typed theory arguments fail once at the argument before expansion", async t => {
  for (const application of ["Action(U0, Nat)", "Action(R := Nat, U := U0)", "Action(U0, tt)"]) {
    const source = `import hlevels; import algebra; import nat;
theory Action(U < UU0, R : Monoid(U)) { M : set U; act(r : R.M, x : M) : M; }
initial N : ${application};`;
    const {result} = await checkProgram(t, source, {module});
    const outputs = result.outputs.filter(o => o.name === "N" || o.name.startsWith("N."));
    assert.equal(outputs.length, 1);
    assert.equal(outputs[0].verified, false);
    assert.ok(outputs[0].code, outputs[0].reason);
    const arg = application.includes("Nat") ? "Nat" : "tt";
    assert.equal(outputs[0].errorStart, source.lastIndexOf(arg), outputs[0].reason);
  }
});

test("free expansion preserves syntax across comments and supports universe parameters", async t => {
  await verified(t, `import hlevels; import algebra;
free W(V < UU0, A : // parameter type
  V) // after header
  : Monoid( // theory argument
  V) on // generator type
  A;
def folded(V < UU0, A : V, S : Monoid(V), g : A -> S.M, a : A) :
  W.fold(V, A, S, g).map(W.gen(a)) = g(a) { rfl; }
`);
});

test("a theory's pattern names leave free parameters and the model's name usable, refusing only a capture", async t => {
  await verified(t, `import nat;
import hlevels;
theory T(U < UU0, A : U) {
  M : set U;
  op(n : Nat, b : (match n return U { zero => A; succ(k) => A; })) : M;
}
free W(k : U0) : T(U0, Unit) on k;
initial k : T(U0, Unit);
def generator_fold(A : U0, S : T(U0, Unit), g : A -> S.M, a : A) :
  W.fold(k := A, S, g).map(W.gen(a)) = g(a) { rfl; }`);
  // The expansion writes the model, as k.c, under the pattern's k.
  const source = `import nat;
import hlevels;
theory P(U < UU0) {
  M : set U;
  c : M;
  law l(n : Nat) : c = (match n return M { zero => c; succ(k) => c; });
}
initial k : P(U0);`;
  const {result} = await checkProgram(t, source, {module});
  const failure = result.outputs.find(o => o.name === "k");
  assert.deepEqual(result.outputs.filter(o => !o.verified).map(o => [o.name, o.code]), [["k", "E869"]]);
  assert.match(failure.reason, /^P's l binds k in a pattern, under which the expansion names the model k: rename the initial or free model\./);
  assert.equal(failure.errorStart, source.indexOf("P(U0)", source.indexOf("initial")));
});

test("generated syntax has local positions, and only names written in the header link from its source", async t => {
  const header = "initial N : Monoid(U0);\nfree W(A : U0) : Monoid(U0) on A;";
  const source = `import hlevels; import algebra;\n${"// padding\n".repeat(100)}${header}`;
  const {result} = await verified(t, source);
  const start = source.lastIndexOf("initial");
  const linked = result.links.filter(link => link.start >= start)
    .map(link => `${source.slice(link.start, link.end)}@${link.start - start}`);
  // The declared names, and in the headers each name a definition's header
  // would link, once: later declarations read the header again unlinked.
  assert.deepEqual(linked.sort(), ["N@8", "Monoid@12", "U0@19", "W@29", "A@31", "U0@35", "Monoid@41", "U0@48", "A@55"].sort());
  // Nothing the expansion or its elaboration marks stands at a declared
  // name, so the name opens its declared type.
  for (const [declared, offset] of [["N", 8], ["W", 29]]) {
    const at = start + offset;
    assert.deepEqual(result.links.filter(link => link.start >= at && link.start <= at + declared.length).map(link => [link.role, link.name]),
      [["inductive", declared]]);
  }
  assert.ok(result.links.every(link => source.slice(link.start, link.end) !== "// padding"));
  for (const suffix of ["model", "fold_map", "fold"]) {
    assert.ok(result.symbols.some(symbol => symbol.name === `N.${suffix}` && symbol.verified));
  }
  // A constructor's bad argument reports inside this declaration, never at
  // the imported theory's source offset; dependent declarations are skipped.
  const invalid = `import hlevels; import algebra;\n${"// padding\n".repeat(100)}free TooLarge : Monoid(U0) on U0;`;
  const {result: failed} = await checkProgram(t, invalid, {module});
  const failure = failed.outputs.find(o => !o.verified);
  assert.ok(failure);
  assert.ok(failure.errorStart >= invalid.indexOf("free TooLarge"), JSON.stringify(failure));
  assert.ok(failure.errorEnd <= invalid.length, JSON.stringify(failure));
  assert.deepEqual(failed.outputs.map(o => o.name), ["TooLarge"]);
});

test("fold clauses bind names no constructor in scope can take", async t => {
  // Constructors without arguments named as a source would name the fold's
  // clause variables, a, x0, x1 and i, and as its parameters are named,
  // target, g and x, which shadow a constructor as any binder does.
  await verified(t, `import hlevels;
import algebra;
import nat;
use nat;
inductive Letter : set U0 { a; b; }
inductive Two : set U0 { x0; x1; i; target; g; x; }
free Words : Monoid(U0) on Letter;
free W(A : U0) : Monoid(U0) on A;
theory P(U < UU0) { M : set U; op(t : Two, m : M) : M; law swap(t : Two, m : M) : op(t, m) = op(t, m); }
initial N : P(U0);
free F(A : U0) : P(U0) on A;
def count(w : Words) : Nat := Words.fold(nat_additive.monoid, fun (l : Letter) => 1).map(w);
def three : count(Words.mul(Words.gen(a), Words.mul(Words.gen(b), Words.gen(a)))) = 3 { rfl; }
def kept(A : U0, T : P(U0), h : A -> T.M, y : A) :
  F.fold(A, T, h).map(F.op(x1, F.op(i, F.gen(y)))) = T.op(x1, T.op(i, h(y))) { rfl; }
`);
});

test("a free parameter keeps its name when a field's global is already resolved", async t => {
  const source = `import hlevels;
import nat;
theory P(U < UU0) { M : set U; point(n : Nat) : M; }
free W(Nat : U0) : P(U0) on Nat;
print(typeof(W.fold));
def folded(A : U0, S : P(U0), h : A -> S.M, a : A) : W.fold(Nat := A, target := S, g := h).map(W.gen(a)) = h(a) { rfl; }`;
  const {result} = await verified(t, source);
  assert.deepEqual(result.prints.map(p => p.text), ["forall Nat : U0. forall target : P(U0). (Nat -> target.M) -> P.Hom{{U0, U0}}(W.model(Nat), target)"]);
  const written = source.indexOf("Nat : U0");
  assert.deepEqual([...new Set(result.links.filter(link => link.start === written).map(link => link.name))], ["Nat"]);
});

test("only the kernel's boundary refusals of a law are the strategy's E856", () => {
  const d = {generated: {laws: {"N.l": "l"}}}, kernel = text => ({constructor: "N.l", message: `Instruction kernel: Constructor N.l: ${text}`});
  for (const boundary of ["A boundary must be a constructor expression: a position or an earlier constructor, applied, or a path application or abstraction of one (section 1.4).",
    "A binder's type in a boundary mentions the sort, a constructor or a position (section 1.4).",
    "A path abstraction or application in a boundary carries a type that is not a cube over the sort (section 1.4).",
    "A constructor's boundary names the constructor itself (section 1.5)."])
    assert.match(lawRefusal(d, kernel(boundary)).message, /^The law l is not an equation between operation terms/);
  // Any other refusal keeps the kernel's message, even one naming a boundary.
  for (const other of ["A constructor type is derived in the signature's universe U(ℓ); lift it there first.", "found boundary_ok, expected M"])
    assert.equal(lawRefusal(d, kernel(other)), null);
  assert.equal(lawRefusal({generated: {laws: {}}}, kernel("A boundary is nested too deeply.")), null);
});

test("a theory that failed its own check is an untranslated dependency of its initial and free models", async t => {
  const source = `import hlevels;
theory T(U < UU0) { M : set U; c : M; law bad(x : M) : M; }
initial N : T(U0);
free W(A : U0) : T(U0) on A;
def use_it(m : T(U0)) : T(U0) := m;`;
  const {result} = await checkProgram(t, source, {module});
  assert.deepEqual(result.outputs.map(o => [o.name, o.code]), [["T", "E818"], ["N", "E340"], ["W", "E340"], ["use_it", "E340"]]);
  for (const [name, keyword] of [["N", "initial"], ["W", "free"]]) {
    const failure = result.outputs.find(o => o.name === name);
    assert.match(failure.reason, /^Untranslated dependency: T /);
    assert.equal(failure.errorStart, source.indexOf("T(U0)", source.indexOf(keyword)));
  }
});

test("refusals of a theory name the declaration's own spelling and the carriers given", async t => {
  const {result} = await checkProgram(t, `import hlevels;
theory Two(U < UU0) { M : set U; P : set U; c : M; }
initial N : Two(U0);
free X : Nat on Unit;`, {module});
  assert.deepEqual(result.outputs.filter(o => !o.verified).map(o => [o.name, o.code]), [["N", "E852"], ["X", "E850"]]);
  assert.match(result.outputs.find(o => o.name === "N").reason, /one carrier that is not a family; Two has M, P\./);
  assert.match(result.outputs.find(o => o.name === "X").reason, /as free W\(A : U0\) : Monoid\(U0\) on A; Nat is none\./);
});

test("a failed generated declaration skips its dependents and keeps progress totals accurate", async t => {
  const {program} = await checkProgram(t, "", {module});
  const progress = [];
  const result = await program.check(`import hlevels; import algebra;
free W : Monoid(U0) on U0;
def after := tt;`, "root", p => progress.push(p));
  assert.deepEqual(result.outputs.map(o => [o.name, o.verified]), [["W", false], ["after", true]]);
  assert.ok(progress.filter(p => p.phase !== "loading").every(p => p.completed <= p.total));
  assert.deepEqual([progress.at(-1).completed, progress.at(-1).total], [result.declarationCount, result.declarationCount]);
  // A failure that skips nothing changes no total and reports nothing more.
  const events = [];
  await program.check(`def a : U0 := tt;\ndef b : U0 := tt;\ndef c : U0 := tt;`, "plain", p => events.push(p));
  const checked = events.filter(p => p.phase === "checked").map(p => JSON.stringify(p));
  assert.equal(new Set(checked).size, checked.length, checked.join("\n"));
});

test("arrow operations receive a supported-spelling diagnostic and derived law terms expand", async t => {
  const {result} = await checkProgram(t, `import hlevels;
theory S(U < UU0) { M : set U; zero : M; succ : M -> M; }
initial N : S(U0);`, {module});
  const failure = result.outputs.find(o => o.name === "N");
  assert.equal(failure.code, "E864");
  assert.match(failure.reason, /named operation arguments/);
  await verified(t, `import hlevels;
theory S(U < UU0) {
  M : set U;
  mul(x, y : M) : M;
  def sq(x : M) : M := mul(x, x);
  law idem(x : M) : sq(x) = x;
}
initial N : S(U0);
def square(x : N) : N.mul(x, x) = x := N.idem(x);`);
});

test("grouped operation arguments generate homomorphisms and computing initial and free folds", async t => {
  await verified(t, `import hlevels;
theory T(U < UU0) {
  M : set U;
  c : M;
  op : forall x, y : M. M;
}
initial N : T(U0);
free W(A : U0) : T(U0) on A;
def initial_fold(S : T(U0), x, y : N) :
  N.fold(S).map(N.op(x, y)) = S.op(N.fold(S).map(x), N.fold(S).map(y)) { rfl; }
def free_fold(A : U0, S : T(U0), g : A -> S.M, a, b : A) :
  W.fold(A, S, g).map(W.op(W.gen(a), W.gen(b))) = S.op(g(a), g(b)) { rfl; }
theory P(U < UU0, A : U) { M : set U; point : forall A, y : A. M; }
initial Q : P(U0, Unit);
def shared_domain(S : P(U0, Unit)) : Q.fold(S).map(Q.point(tt, tt)) = S.point(tt, tt) { rfl; }
`);
});

test("laws using other laws are refused before publishing a model", async t => {
  const {result} = await checkProgram(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; law l : c = c; law m : l @ 0 = c; }
initial N : T(U0);
free W(A : U0) : T(U0) on A;`, {module});
  assert.deepEqual(result.outputs.filter(o => !o.verified).map(o => [o.name, o.code]), [["N", "E856"], ["W", "E856"]]);
  assert.ok(result.outputs.every(o => !/^(N|W)\./.test(o.name)));
});

test("a law the kernel refuses as a boundary gets the strategy's refusal, and a law's redexes reduce", async t => {
  const source = `import nat;
import hlevels;
use nat;
theory P(U < UU0) {
  M : set U;
  c : M;
  op(n : Nat) : M;
  law l(n : Nat) : c = (match n return M { zero => c; succ(k) => op(k); });
}
initial N : P(U0);
free W(j : U0) : P(U0) on j;`;
  const {result} = await checkProgram(t, source, {module});
  assert.deepEqual(result.outputs.filter(o => !o.verified).map(o => [o.name, o.code]), [["N", "E856"], ["W", "E856"]]);
  assert.ok(result.outputs.every(o => !/^(N|W)\./.test(o.name)));
  for (const keyword of ["initial", "free"])
    assert.equal(result.outputs.find(o => o.name === (keyword === "free" ? "W" : "N")).errorStart, source.indexOf("P(U0)", source.indexOf(keyword)));
  // The kernel reads a boundary beta-reduced, and a data argument as data.
  await verified(t, `import nat;
import hlevels;
use nat;
theory R(U < UU0) {
  M : set U;
  c : M;
  op(n : Nat, x : M) : M;
  law redex : op(0, c) = (fun (y : M) => y)(c);
  law data(n : Nat, x : M) : op(match n return Nat { zero => 0; succ(k) => k; }, x) = x;
}
initial N : R(U0);
free W(A : U0) : R(U0) on A;`);
});

test("domains depending on laws or carrier evidence are refused, naming the proof, before publishing a model", async t => {
  for (const [dependency, kind] of [["l", "law"], ["M_is_set", "evidence"]]) {
    const {result} = await checkProgram(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; law l : c = c; law m(p : ${dependency} = ${dependency}) : c = c; }
initial N : T(U0);`, {module});
    const failures = result.outputs.filter(o => !o.verified);
    assert.deepEqual(failures.map(o => [o.name, o.code]), [["N", "E867"]]);
    assert.match(failures[0].reason, new RegExp(`^m takes p with a type depending on the ${kind} ${dependency}: `));
    assert.ok(result.outputs.every(o => !o.name.startsWith("N.")));
  }
  // A carrier-typed binder of a law's name is the binder: the carrier's refusal.
  const {result} = await checkProgram(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; law l : c = c; law m(l : M, p : l = l) : c = c; }
initial N : T(U0);`, {module});
  const failure = result.outputs.find(o => o.name === "N");
  assert.equal(failure.code, "E854");
  assert.match(failure.reason, /^m takes p with a type depending on the carrier M: /);
});

test("universe-quantified laws receive a coded strategy refusal", async t => {
  const {result} = await checkProgram(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; law l : forall V < UU0. c = c; }
initial N : T(U0);
free W(A : U0) : T(U0) on A;`, {module});
  assert.deepEqual(result.outputs.filter(o => !o.verified).map(o => [o.name, o.code]), [["N", "E865"], ["W", "E865"]]);
  assert.ok(result.outputs.every(o => !/^(N|W)\./.test(o.name)));
});

test("a model name cannot hide a global required by its expansion", async t => {
  for (const source of [
    "theory T(U < UU0) { M : set U; c : M; } initial T : T(U0);",
    "def N : U0 := Unit; theory T(U < UU0, A : U) { M : set U; c(x : A) : M; } initial N : T(U0, N);",
    "def W : U0 := Unit; theory T(U < UU0) { M : set U; } free W(A : W) : T(U0) on Unit;",
  ]) {
    const {result} = await checkProgram(t, `import hlevels; ${source}`, {module});
    const failures = result.outputs.filter(o => !o.verified);
    assert.deepEqual(failures.map(o => o.code), ["E866"]);
    assert.match(failures[0].reason, /hides a declaration used by its expansion: rename the initial or free model\./);
  }
  // A field with the declared type's name is substituted, not a global.
  await verified(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
initial M : T(U0);
free W(W : U0) : T(U0) on W;`);
  // A field's global has a declaration identity before N is published.
  await verified(t, `import hlevels;
def N : U0 := Unit;
theory T(U < UU0) { M : set U; c(x : N) : M; }
initial N : T(U0);
def use_it : N := N.c(tt);`);
});

test("an initial or free model's declared type is an inductive to the workbench and the migration verifier", async t => {
  const source = `import hlevels;
import algebra;
initial N : Monoid(U0);
free W(A : U0) : Monoid(U0) on A;
`;
  const {program, get} = await verified(t, source);
  // The workbench shows a declared type's signature, never a checked term.
  for (const name of ["N", "W"]) {
    assert.deepEqual([get(name).kind, get(name).role], ["inductive", "inductive"]);
    assert.ok(program.signatureView(get(name).binding).constructors.length);
  }
  // The verifier matches the declared types' signatures, through which the
  // generated definitions compare as identical.
  const library = sourceReader();
  const [report] = await verifyMigration({ modules: ["initial_fixture"], level: "identical",
    readOriginal: (name, importer) => name === "initial_fixture" ? source : library(name, importer),
    readEdited: async () => source.replace("initial N : Monoid(U0);", "initial N : Monoid(U := U0);") });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 8);
});

test("initial and free reject a theory name shadowed by an ordinary definition", async t => {
  for (const named of [false, true]) {
    const source = `import hlevels;
import algebra;
def Monoid : U0 := Unit;
initial N : Monoid(${named ? "U := " : ""}U0);
free W(A : U0) : Monoid(${named ? "U := " : ""}U0) on A;
`;
    const {result} = await checkProgram(t, source, {module});
    assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), [["N", "E850"], ["W", "E850"]]);
    for (const gap of result.gaps) assert.equal(source.slice(gap.start, gap.end), `Monoid(${named ? "U := " : ""}U0)`);
    assert.ok(result.outputs.every(output => !/^(N|W)\./.test(output.name)));
  }
});

test("an oversized generator is diagnosed at the written generator type", async t => {
  const source = `import hlevels;
theory T(U < UU0) { M : set U; }
free W(A : U1) : T(U0) on A;
`;
  const {result} = await checkProgram(t, source, {module});
  assert.deepEqual(result.gaps.map(gap => gap.name), ["W"]);
  const gap = result.gaps[0];
  assert.equal(gap.code, "E870");
  assert.match(gap.reason, /generator type of W.*universe above/);
  assert.equal(source.slice(gap.start, gap.end), "A");
  assert.ok(!gap.reason.includes("argument a"));
  const ordinary = await checkProgram(t, `inductive Plain(A : U1) : set U0 { point(a : A); }`, {module});
  assert.deepEqual(ordinary.result.gaps.map(gap => [gap.name, gap.code]), [["Plain", "E514"]]);
});

test("headerless theories keep public universe labels independent of operation binders", async t => {
  for (const binder of ["x", "U", "U_1"]) {
    await verified(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
theory Child extends T { op(${binder} : M) : M; }
def example : Child(U := U0) := Child.make{{U := U0}}(Unit, prop_is_set(U0, Unit, unit_is_prop), tt, fun x => x);
initial N : Child(U := U0);
free W(A : U0) : Child(U := U0) on A;
theory Wide(V, U < UU0) extends Child { N : set V; }
def carrier(S : Wide(U0, U1)) : U1 := S.M;
`);
  }
  await verified(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
theory Child(U : Unit) extends T { op(U_1 : M) : M; }
initial N : Child(U_1 := U0, U := tt);
free W(A : U0) : Child(U := tt, U_1 := U0) on A;
`);
});
