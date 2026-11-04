// Small programs for the argument solver's differential suite
// (tools/solver-differential.mjs): each is elaborated on main and on a
// branch, and every declaration's verdict, checked term and type (hashed up
// to bound names), and the evaluations, are compared. They cover what the
// library's closures can leave out: universe-polymorphic calls whose bounds
// come from several arguments, in either order, with equations among them;
// implicit arguments determined through dependent types; the solver's
// guesses (approximate); results that are functions once solved; and the
// binders unification descends under. Every reproduction a review of the
// solver found is a member, named after it.
export const programs = {
  // #352, Codex round 1: a bound found after the first one still counts.
  codex_352_r1_wrap_level: `
def Wrap(U < UU0) : UU0 := U;
def take{{U < UU0}}(A : U, B : Wrap(U)) : Unit := tt;
def taken : Unit := take(Unit, U0);
`,
  // #352, Codex round 1: typing a solution guesses no other hole.
  codex_352_r1_family_tag: `import unat;
use unat;
def Family(n : UNat) : U0 := UNat;
def Tag(x, n : UNat) : U0 := Unit;
def pick{{n : UNat, x : Family(n)}}(t : Tag(x, n)) : UNat := n;
def picked(z : Family(0), t : Tag(z, 1)) : UNat := pick(t);
evaluate picked(0, tt) expecting 1;
`,
  // #352, Codex round 2: a function type's codomain bounds the universe.
  codex_352_r2_wrap_arrow: `
def Wrap(U < UU0, A : U) : UU0 := A -> U;
def take{{U < UU0, A : U}}(a : A, f : Wrap(U, A)) : Unit := tt;
def taken(B : U1, b : B) : Unit := take(b, fun (x : B) => U1);
`,
  // #352, Codex round 2: a result solved as a function takes the next
  // argument.
  codex_352_r2_identity_function: `
def identity{{U < UU0, A : U}}(x : A) : A := x;
def taken(B : U1, b : B) : B := identity(fun (x : B) => x, b);
`,
  // Lower bounds from several arguments, in both orders.
  bounds_two_arguments: `
def both{{U < UU0}}(A, B : U) : Unit := tt;
def small_first : Unit := both(Unit, U0);
def large_first : Unit := both(U0, Unit);
def three{{U < UU0}}(A, B, C : U) : Unit := tt;
def mixed : Unit := three(U1, Unit, U0);
`,
  // A bound through a value's type and one through a type.
  bounds_value_and_type: `
def keep{{U < UU0, A : U}}(a : A, B : U) : A := a;
def kept(X : U1, x : X) : X := keep(x, U0);
def kept_small : Unit := keep(tt, Unit);
`,
  // An equation from a function's domain, with a bound from another
  // argument.
  equation_and_bound: `
def apply{{U < UU0}}(f : U -> Unit, A : U) : Unit := f(A);
def to_unit(A : U0) : Unit := tt;
def applied : Unit := apply(to_unit, Unit);
def lifted(f : U1 -> Unit) : Unit := apply(f, U0);
def conflicted(f : U0 -> Unit) : Unit := apply(f, U0);
`,
  // An upper bound from the type expected of the call, and a lower bound
  // from its argument.
  bounds_upper_and_lower: `
def lift_type{{U < UU0}}(A : U) : U := A;
def small : U0 := lift_type(Unit);
def large : U1 := lift_type(Unit);
`,
  // A universe nothing bounds where the call's type does not mention it.
  unbounded_universe: `
def ignore{{U < UU0, A : U}}(u : Unit) : Unit := u;
def ignored : Unit := ignore{{A := Unit}}(tt);
`,
  // An implicit argument read off a path's endpoints.
  path_endpoints: `import unat;
use unat;
def start{{A : U0, x, y : A}}(p : x = y) : A := x;
def started : UNat := start(refl(3));
evaluate started expecting 3;
def middle{{A : U0, x, y, z : A}}(p : x = y, q : y = z) : A := y;
def joined(p : 1 = 1) : UNat := middle(p, refl(1));
evaluate joined(refl(1)) expecting 1;
`,
  // Implicit arguments through a dependent function's type.
  dependent_function: `import unat;
use unat;
def Fam(n : UNat) : U0 := UNat;
def at_point{{A : U0, B : A -> U0}}(f : forall x : A. B(x), a : A) : B(a) := f(a);
def doubled(n : UNat) : Fam(n) := n + n;
def used : Fam(2) := at_point(doubled, 2);
def used_given : Fam(2) := at_point{{B := Fam}}(doubled, 2);
evaluate used_given expecting 4;
`,
  // A guess: only matching the instance argument by argument determines
  // the holes.
  guess_two_arguments: `import unat;
use unat;
def Two(m, n : UNat) : U0 := Unit;
def second{{m, n : UNat}}(t : Two(m, n)) : UNat := n;
def got(t : Two(1, 2)) : UNat := second(t);
evaluate got(tt) expecting 2;
def first_of{{m, n : UNat}}(t : Two(m, n)) : UNat := m;
def got_first(t : Two(5, 6)) : UNat := first_of(t);
evaluate got_first(tt) expecting 5;
`,
  // A guess undone, then the definition unfolded: here the unfolding
  // determines the holes.
  guess_then_unfold: `import unat;
use unat;
def Sum3(n, m, k : UNat) : U0 := n + k = 6;
def take3{{a, b : UNat}}(x : Sum3(a, 0, b)) : Unit := tt;
def taken3(x : Sum3(1, 1, 5)) : Unit := take3(x);
`,
  // A result type that computes to a function once its argument is known.
  function_result: `import unat;
use unat;
def Fn(A : U0) : U0 := A -> A;
def as_function{{A : U0}}(a : A) : Fn(A) := fun (x : A) => x;
def made : UNat := as_function(1)(2);
evaluate made expecting 2;
def same{{U < UU0, A : U}}(x : A) : A := x;
def applied : UNat := same(fun (n : UNat) => n + 1, 3);
evaluate applied expecting 4;
`,
  // Functions compared under their binders.
  under_binders: `import unat;
use unat;
def after{{A, B, C : U0}}(g : B -> C, f : A -> B) : A -> C := fun (x : A) => g(f(x));
def plus_two : UNat -> UNat := after(fun (n : UNat) => n + 1, fun (n : UNat) => n + 1);
evaluate plus_two(3) expecting 5;
def dependent{{A : U0, B : A -> U0}}(f : forall x : A. B(x)) : forall x : A. B(x) := f;
def kept : forall n : UNat. UNat := dependent(fun (n : UNat) => n);
def kept_given : forall n : UNat. UNat := dependent{{B := fun (n : UNat) => UNat}}(fun (n : UNat) => n);
evaluate kept_given(7) expecting 7;
`,
  // A theory and its extension: the generated homomorphism makers' calls
  // descend under the binders of their models' types.
  theory_extension: `import hlevels;

theory Magma(U < UU0) {
  M : set U;
  mul(x, y : M) : M notation x * y;
}

theory Semigroup(U < UU0) extends Magma {
  law mul_assoc(x, y, z : M) : (x * y) * z = x * (y * z);
}
`,
  // A guess undone in a generated maker call, then asked again.
  theory_pointed: `import hlevels;

theory Pointed(U < UU0) {
  M : set U;
  point : M;
}

theory Twice(U < UU0) extends Pointed {
  law point_point : point = point;
}
`,
  // Squares: holes solved under dimension binders, in a universe only that
  // solution bounds.
  squares_transpose: `
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
`,
  // The library's squares, used as the library uses them.
  squares_library: `import squares;

def again{{U < UU0, A, B : U, x, y, z : A}}(f : A -> B, p : x = y, q : y = z) :
  cong(f, trans(p, q)) = trans(cong(f, p), cong(f, q)) := top_unique{{
    a00 := f(x), a01 := f(x), a10 := f(y), a11 := f(z)
  }}(cong_square(f, trans_filler(p, q)), trans_filler(cong(f, p), cong(f, q)));
`,
  // A path family over a dimension, solved through a dependent path.
  dependent_path: `import unat;
use unat;
def over{{A : U0, B : A -> U0, x, y : A}}(p : x = y, u : B(x), v : B(y),
  q : PathP(fun (i : Interval) => B(p @ i), u, v)) : B(y) := v;
def Const(n : UNat) : U0 := UNat;
def overed : UNat := over{{B := Const}}(refl(1), 2, 2, refl(2));
evaluate overed expecting 2;
`,
};
