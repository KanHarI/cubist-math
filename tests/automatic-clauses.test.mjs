import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/mathscript/parser.mjs";
import { checkProgram } from "./check-program.mjs";

const module = await createCubical();
async function check(t, source) {
  const checked = await checkProgram(t, source, { module, name: "automatic" });
  const ok = name => assert.ok(checked.get(name).verified, `${name}: ${checked.get(name).reason}`);
  return { ...checked, ok };
}

const quotient = `import hlevels;
inductive Quotient(A : U0, R : A -> A -> U0) : set {
  class(a : A);
  glue(a, b : A, r : R(a, b)) : class(a) = class(b);
}
def link(A : U0, R : A -> A -> U0, a, b : A, r : R(a, b)) :
  typed(Quotient(A, R), class(a)) = typed(Quotient(A, R), class(b)) := glue(a, b, r);
`;

// E4: the motive is a family of sets, not just a constant set.
test("E4: a quotient's dependent eliminator generates its set squash", async t => {
  const {ok,result} = await check(t, `${quotient}
def descend(A : U0, R : A -> A -> U0, B : Quotient(A, R) -> U0,
    h : forall z : Quotient(A, R). IsSet(U0, B(z)),
    f : forall a : A. B(class(a)),
    respects : forall a, b : A. forall r : R(a, b).
      PathP(fun (i : Interval) => B(link(A, R, a, b, r) @ i), f(a), f(b)),
    q : Quotient(A, R)) : B(q) := match q as z return B(z) {
  class(a) => f(a);
} obligations {
  glue(a, b, r) @ i => respects(a, b, r) @ i;
};
def class_computes(A : U0, R : A -> A -> U0, B : Quotient(A, R) -> U0,
    h : forall z : Quotient(A, R). IsSet(U0, B(z)), f : forall a : A. B(class(a)),
    respects : forall a, b : A. forall r : R(a, b).
      PathP(fun (i : Interval) => B(link(A, R, a, b, r) @ i), f(a), f(b)), a : A) :
    descend(A, R, B, h, f, respects, class(a)) = f(a) { rfl; }
def glue_image(A : U0, R : A -> A -> U0, B : Quotient(A, R) -> U0,
    h : forall z : Quotient(A, R). IsSet(U0, B(z)), f : forall a : A. B(class(a)),
    respects : forall a, b : A. forall r : R(a, b).
      PathP(fun (i : Interval) => B(link(A, R, a, b, r) @ i), f(a), f(b)), a, b : A, r : R(a, b)) :
    PathP(fun (i : Interval) => B(link(A, R, a, b, r) @ i), f(a), f(b)) :=
    path i => descend(A, R, B, h, f, respects, link(A, R, a, b, r) @ i);
def glue_computes(A : U0, R : A -> A -> U0, B : Quotient(A, R) -> U0,
    h : forall z : Quotient(A, R). IsSet(U0, B(z)), f : forall a : A. B(class(a)),
    respects : forall a, b : A. forall r : R(a, b).
      PathP(fun (i : Interval) => B(link(A, R, a, b, r) @ i), f(a), f(b)), a, b : A, r : R(a, b)) :
    glue_image(A, R, B, h, f, respects, a, b, r) = respects(a, b, r) { rfl; }
`);
  for(const name of ["Quotient","descend","class_computes","glue_image","glue_computes"]) ok(name);
  assert.ok(result.links.some(link => link.name === "Quotient.squash" && link.role === "coherence obligation"));
});

// E11: all three generated dimensions, with a dependent groupoid motive.
test("E11: a groupoid's dependent eliminator generates its three-dimensional squash", async t => {
  const {ok,result} = await check(t, `import hlevels;
inductive Gpd(A : U0) : trunc(1) { point(a : A); }
def descend(A : U0, B : Gpd(A) -> U0,
    h : forall z : Gpd(A). HasLevel(U0, 2, B(z)), f : forall a : A. B(point(a)), q : Gpd(A)) : B(q) :=
  match q as z return B(z) { point(a) => f(a); };
computable def read(q : Gpd(Nat)) : Nat := match q { point(a) => a; };
computable def read_point : read(point(3)) = 3 { rfl; }
evaluate read(point(3)) expecting 3;
`);
  for (const name of ["Gpd","descend","read","read_point"]) ok(name);
  assert.deepEqual(result.evaluations.map(item => item.value), ["3"]);
});

test("explicit obligations retain kernel checking and require all computational clauses", async t => {
  const {ok,get} = await check(t, `import hlevels;
inductive Circle { base; loop : base = base; }
def flat(x : Circle) : Nat := match x { base => 0; } obligations by rfl;
def checked : flat(loop @ 1) = 0 { rfl; }
def wrong(x : Circle) : Nat := match x { base => 0; } obligations { loop @ i => 1; };
def missing(x : Circle) : Nat := match x {} obligations by hlevel;
def misplaced(x : Circle) : Nat := match x {} obligations { base => 0; loop @ i => 0; };
`);
  ok("flat"); ok("checked");
  assert.equal(get("wrong").verified,false);
  assert.match(get("wrong").reason,/mismatch|clause/i);
  assert.match(get("missing").reason,/needs a clause for base/);
  assert.match(get("misplaced").reason,/point constructor.*computational clause/);
});

test("missing h-level evidence fails rather than admitting an unsquashed eliminator", async t => {
  const {get} = await check(t, `${quotient}
def unsound(A : U0, R : A -> A -> U0, q : Quotient(A, R)) : U0 := match q {
  class(a) => A;
  glue(a, b, r) @ i => A;
};
`);
  assert.equal(get("unsound").verified,false);
  assert.match(get("unsound").reason,/Cannot generate Quotient\.squash.*h-level/);
});

test("automatic clauses work in the match statement, and use the declared target's squash", async t => {
  const {ok} = await check(t, `import hlevels;
inductive Tr(A : U0) : prop { point(a : A); }
def rebuilt(A : U0, x : Tr(A)) : Tr(A) { match x { point(a) => { exact point(a); } } }
def point_computes : rebuilt(Nat, point(2)) = point(2) { rfl; }
inductive Circle { base; loop : base = base; }
def flat(x : Circle) : Nat { match x { base => { exact 0; } } obligations { loop @ i => { exact 0; } } }
def by_level(x : Circle) : Unit { match x { base => { exact tt; } } obligations by hlevel; }
`);
  for (const name of ["rebuilt","point_computes","flat","by_level"]) ok(name);
});

test("trailing proofs fill declared paths without replacing a generated squash", async t => {
  const {ok} = await check(t, `${quotient}
def by_rfl(A : U0, R : A -> A -> U0, q : Quotient(A, R)) : Nat :=
  match q { class(a) => 0; glue(a, b, r) @ i => 0; } obligations by rfl;
def by_block(A : U0, R : A -> A -> U0, q : Quotient(A, R)) : Nat :=
  match q { class(a) => 0; } obligations by { intro a, b, r; rfl; };
def by_term(A : U0, R : A -> A -> U0, q : Quotient(A, R)) : Nat :=
  match q { class(a) => 0; } obligations by (fun (a, b : A, r : R(a, b)) => path i => 0);
def statement_block(A : U0, R : A -> A -> U0, q : Quotient(A, R)) : Nat {
  match q { class(a) => { exact 0; } } obligations by { intro a, b, r; rfl; }
}
def statement_term(A : U0, R : A -> A -> U0, q : Quotient(A, R)) : Nat {
  match q { class(a) => { exact 0; } } obligations by (fun (a, b : A, r : R(a, b)) => path i => 0);
}
def computes : by_term(Unit, fun (a, b : Unit) => Unit, class(tt)) = 0 { rfl; }
`);
  for (const name of ["by_rfl", "by_block", "by_term", "statement_block", "statement_term", "computes"]) ok(name);
});

test("a whole-clause proof is refused when several declared paths are missing", async t => {
  const {ok,get} = await check(t, `import hlevels;
inductive TwoLoops { base; first : base = base; second : base = base; }
def tactics(x : TwoLoops) : Nat := match x { base => 0; } obligations by rfl;
def ambiguous_block(x : TwoLoops) : Nat := match x { base => 0; } obligations by { rfl; };
def ambiguous_term(x : TwoLoops) : Nat := match x { base => 0; } obligations by (path i => 0);
`);
  ok("tactics");
  for (const name of ["ambiguous_block", "ambiguous_term"])
    assert.match(get(name).reason, /exactly one missing declared path clause; found 2/);
});

test("hlevel hints supply evidence unavailable to automatic squash without the hint", async t => {
  const {ok,get} = await check(t, `${quotient}
def hinted(A : U0, R : A -> A -> U0, B : U0, h : Unit -> IsSet(U0, B), b : B, q : Quotient(A, R)) : B :=
  match q { class(a) => b; glue(a, a2, r) @ i => b; } obligations by hlevel with [h(tt)];
def no_hint(A : U0, R : A -> A -> U0, B : U0, h : Unit -> IsSet(U0, B), b : B, q : Quotient(A, R)) : B :=
  match q { class(a) => b; glue(a, a2, r) @ i => b; };
`);
  ok("hinted");
  assert.match(get("no_hint").reason, /Cannot generate Quotient\.squash/);
});

test("obligations report missing imports and unsupported tactics directly", async t => {
  const {get} = await check(t, `inductive Tr(A : U0) : prop { point(a : A); }
def absent(A : U0, x : Tr(A)) : Unit := match x { point(a) => tt; };
`);
  assert.match(get("absent").reason, /Cannot generate Tr\.squash: import hlevels/);
  assert.throws(() => parse("def f(x : Circle) : Nat := match x { base => 0; } obligations by simp;"),
    /obligations by supports hlevel.*proof block/);
});
