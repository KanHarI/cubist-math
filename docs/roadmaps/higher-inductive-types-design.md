# Higher inductive-inductive types: kernel and language design

Status: adopted on 2026-09-25 as [kernel roadmap](cubical-kernel-roadmap.md)
item H, stages H1–H4. Nothing is implemented yet; the
[work plan](work-plan.md) schedules it. It supersedes kernel items G1–G3 and
the separate native-inductive and generic higher-inductive items. It depends
on G0 (universe-generic checking). The existing literature informed this
design without bounding it; the choices that depart from it are listed in the
section on departures. The language features built on it are proposed in
[inductive-language-features.md](inductive-language-features.md), which
ergonomics milestones 6 and 7 adopt.

## Goals

1. **One mechanism.** A single kernel mechanism declares every inductive type:
   - ordinary data (natural numbers, sums, lists, W types, ordinals);
   - indexed families (vectors, finite sets, well-typed syntax, and an
     identity type whose J computes on `refl`);
   - higher inductive types (pushouts, suspensions, spheres, truncations, set
     quotients);
   - inductive-inductive types, where a type is defined together with families
     over it: Cauchy reals with their closeness relation, the partiality
     monad, and the syntax of type theory.

   Every class is a special case of one signature format, so there is one set
   of generated rules to trust and test.
2. **Computability, expressible and preserved.** This is the governing
   requirement.
   - Eliminators compute definitionally on every constructor, including path
     constructors, and on formal compositions.
   - Closed assumption-free results of data types, including data families,
     normalize to canonical values (invariant 10).
   - A result that computes can be declared so, and the checker enforces the
     declaration. No rule, elaboration feature or tool may silently lose
     computability. See [Computability](#3-computability-expressible-and-preserved).
3. **A small trusted core.** The kernel checks a signature normal form and
   generates rules from it. Readable declarations, `match`, recursion and views
   are untrusted elaboration into that normal form and into eliminator
   applications.
4. **Staged trust.** The accepted class widens in stages. Each stage is gated
   on its own soundness note and differential tests.

## 1. Signatures

A signature is an ordered list of items. Each item is checked in the context
of all items before it.

- A **sort** has a name, the signature's shared parameters, an index telescope
  and an h-level (`type`, `set` or `prop`). All sorts are declared before any
  constructor. An index telescope may mention earlier sorts: the closeness
  relation is indexed by two reals.
- A **constructor** belongs to one sort. It is checked against all sorts and
  against the constructors listed before it, of any sort.

### Constructor normal form

The kernel accepts constructors only in this form:

```
c : (data : D) (positions : P1 … Pn) (dims : I^d) -> S_k(index terms) [boundary]
```

- **Data** `D` is a telescope of ordinary types. It may mention parameters and
  earlier data, but never a sort.
- Each **position** is `Pj = forall (a : Aj), Cube_dj(S_m(indices_j(a)), boundary_j(a))`:
  - A `dj`-dimensional cube in sort `S_m`. An element is a 0-cube and a path is
    a 1-cube with its two endpoints as boundary. So squash and path arguments
    are positions like any other.
  - The arity `Aj` may mention data but never a sort or a position, so strict
    positivity holds by construction.
  - Its index and boundary terms may mention data, earlier positions, the
    arity variable, earlier constructors and formal compositions.
- **Dimensions** `dims` are the constructor's own interval variables. A point
  constructor has `d = 0`.
- **Result indices and boundary** are terms of the sort built from the same
  ingredients. The boundary is a system on faces of `dims`, and its pieces
  must agree wherever faces overlap. The kernel's existing face and system
  machinery checks this.

**H-level modifiers.** `set` appends a two-dimensional squash constructor and
`prop` a one-dimensional one. They are ordinary constructors in this format:
the kernel generates them and the elaborator knows their meaning.

**Universe levels.** A sort's level is the maximum of the levels of its
indices, data, arities and parameters. With G0 these are level expressions.

## 2. Generated rules

### Formation and introduction

Each sort is a type former, applied to parameters and indices. Each
constructor is a term. A constructor evaluated on a face of its dimensions
reduces to its boundary, so the boundary holds by definition.

### Kan structure: one formal composition per sort

Each sort has one formal constructor, heterogeneous composition along a line
of parameters and indices with walls:

```
fcomp_S(line : I -> (params, indices), base : S(line(0)), faces : φ ↦ walls) : S(line(1))
```

It reduces to its wall when a face holds, and it has no other definitional
behavior of its own. Transport is `fcomp` with the walls `φ ↦ λ i. a` on the
constancy face `φ`. Homogeneous composition is `fcomp` along a constant line.
One formal constructor supplies both operations.

**Pushing through constructors.** When a sort has no path constructors and the
base and all walls are applications of the same point constructor, `fcomp`
pushes into the arguments, as the kernel already does for natural numbers,
sums and W types. Plain data therefore keeps strict canonical forms. Transport
of a path constructor along a line of parameters pushes into its arguments,
then corrects the boundary with `fcomp` walls. This is the one delicate
generated rule.

### Indexed families: matching the index line

Along a line on which indices vary, pushing a constructor through needs the
target's indices to have the constructor's shape. The kernel matches the
normal form of the index line, first-order on constructor heads, against the
constructor's result indices:

- **The match succeeds.** For example, the vector-length line normalizes to
  `succ(m(i))` and the constructor is `cons`. Then `fcomp` pushes into the
  arguments, transporting them along the matched lines (here `m(i)`).
- **The match fails.** For example, the index is a neutral path, as when
  transporting `refl` along an arbitrary `p : a = b`. Then `fcomp` is
  canonical: it is a normal form.

Closed index lines in data types normalize to constructor forms, so closed
elements of data families such as `Vec(A, 3)` normalize to constructor trees.
Formal compositions remain only where no constructor form exists, which is
exactly where the identity family needs them: `refl` transported along a
nontrivial path. That makes `inductive Id(A : U, a : A) : A -> type { refl :
Id(A, a, a); }` an identity type whose J computes definitionally on `refl`.
It is the separate identity type of kernel item G3, with no dedicated kernel
rules.

Matching must be stable under restriction to faces: a line that fails to
match may match after substituting interval endpoints. The rewrite system
handles this by re-reducing restricted formal compositions. The semantic
construction (section 4) must generate formal elements only for non-matching
lines, and let restriction map them to pushed elements.

### Elimination

A motive gives a type family for each sort. The motive for an indexed sort is
indexed over the displayed indices: for each index of sort type, the family
also receives the motive's element for that index. For the closeness relation,
the motive is `Q(ε, u, v, pu, pv, h)`, where `pu` and `pv` are the motive's
values at `u` and `v`.

A clause is given for each constructor. It takes the constructor's data and
positions, plus a displayed version of each position: the recursive result.
It returns a displayed cube over the constructor's result, whose indices and
boundary are the displayed index and boundary terms.

**Clause types from the partial eliminator.** Rather than implement a separate
translation into displayed types, the kernel computes the displayed index and
boundary terms by running the eliminator itself over them:
- clauses are variables;
- positions map to their displayed variables;
- constructors reduce to the clauses of earlier constructors;
- `fcomp` becomes composition in the motive.

Only earlier constructors occur in these terms, so this is well founded. One
reduction engine serves both computation and clause typing.

**Computation:**

```
elim(c(data, positions) @ dims)   ≡ clause_c(data, positions, elim ∘ positions) @ dims
elim(fcomp(line, base, faces))    ≡ comp(motive along line, elim(base), faces ↦ elim(walls))
```

A path clause must match its point clauses on its boundary. The kernel checks
this when it checks the clause.

### What computes

A closed element of a sort normalizes to one of:
- a constructor applied to closed arguments;
- a path constructor at an interval endpoint, which has already reduced to
  its boundary;
- a formal composition of such elements.

Eliminating into a data type turns `fcomp` into composition in that type,
which computes. So a closed natural number obtained through any higher
inductive-inductive type still normalizes to a numeral. A closed proof of a
truncated existential normalizes to `point(w)` under formal compositions. The
CLI can read `w` off the base, which is how real approximations are
evaluated (section 5).

## 3. Computability: expressible and preserved

This is the governing requirement. For any result that can compute, a user
must be able to say so and have it checked, and nothing in the system may
silently lose it.

### Expressible

- **Every construction here has a computing form.** Data, indexed,
  higher and inductive-inductive types all compute. Quotients, truncation,
  the identity family and the reals are declarations with computing
  eliminators. So no mathematics in scope has to go through an axiom merely
  because the language lacks a computing formulation.
- **Computability is a checked property.**
  - Every checked declaration carries its *non-computing dependencies*: the
    transitive set of user axioms, excluded middle, choice, resizing and any
    other postulate its term, type and context use. The inspector shows it.
  - `computable def …` asserts that this set is empty. The checker rejects the
    declaration otherwise, naming the dependency chain that reaches the
    offending assumption.
  - A provisional stage marker (section 4) is not a non-computing dependency,
    because such results still compute.
- **Computation can be stated in source.**
  - A definitional statement proved by `rfl` states it inside the language,
    as in `factorial(10) = 3628800`.
  - For results under truncation, `evaluate term expecting pattern;` is a
    checked test directive. It normalizes the closed term, reads the witness
    off its normal form, and compares it with the pattern. Canonicity
    regressions then live in the library, next to the results they protect.

### Preserved

- **Kernel.** Every generated rule is a computation rule, and none produces a
  stuck closed term of a data type:
  - formal compositions eliminate into data types by composition, which
    pushes through constructors;
  - index-line matching gives closed data families constructor normal forms;
  - path constructors reduce to their boundaries at interval endpoints.

  Each stage ships a canonicity statement and extends the fixture with the
  types it admits.
- **Elaboration.** `match`, recursion, views, automatic clauses, `simp` and
  `rw` produce ordinary kernel terms, so they cannot add dependencies.
  Automatic clauses use proved h-level evidence, never assumed evidence. A
  view built with a non-computing assumption carries that dependency into
  every use, and `computable` definitions then reject it.
- **Unfolding hints** change conversion strategy only. Evaluation always
  unfolds, so they never hide computational content.
- **Tools.** The migration verifier compares non-computing dependencies as
  well as types. A declaration that computed before a refactoring must still
  compute after it.
- **Continuous checking.** Every `computable` declaration and every
  `evaluate` directive in the library is rechecked in CI.

## 4. Soundness and trust

### Proposed semantic route

The route interprets the kernel in De Morgan cubical sets, which is the
existing kernel's interval algebra:

1. For a signature, define presheaves for its sorts over cubes and indices.
   Carriers, their restriction maps and the relation sorts are defined
   together by a metatheoretic induction-induction-recursion. The generators
   are the constructors and formal compositions. A path constructor restricted
   to a boundary face is its boundary term, so carriers contain only reduced
   forms. This generalizes Coquand–Huber–Mörtberg's construction of higher
   inductive types from one sort to many ordered sorts.
2. Formal compositions provide fillers by construction. Uniformity holds
   because restriction commutes with every generator.
3. The eliminator is defined by the metatheory's structural recursion on
   generators. It commutes with restriction, so it is a section, and the
   computation rules hold strictly.

**Obligations to write, per stage:**
- confluence of boundary reduction;
- fibrancy along index lines, where formal coercions are needed (as in
  Cavallo–Harper's treatment of indexed higher inductive types);
- that the metatheory has the induction-induction-recursion needed;
- normalization of the extended syntax, for decidable conversion.

### Stages

| Stage | Class accepted | Main new obligation |
| --- | --- | --- |
| H1 | One sort, no indices: data and higher inductive types | Transport along parameters with boundary correction |
| H2 | One indexed sort | Formal composition along varying indices |
| H3 | Several sorts where every sort is `set` or `prop` (quotient inductive-inductive types) | Induction-induction; clause typing through the partial eliminator |
| H4 | Several sorts with untruncated sorts | Higher dependent cubes in clauses; adopt only if a use appears |

The code is the same at every stage; the signature checker's gate widens.
Stage H3 covers every inductive-inductive use we know of: Cauchy reals, the
partiality monad, surreal numbers and the syntax of type theory.

### Trust controls

- **Reference checker first.** Every stage lands in the JavaScript reference
  checker before the C kernel. Both must agree on the canonicity fixture and on
  every generated-rule test.
- **Differential oracles.** The hand-coded natural-number, sum, W and pushout
  rules are the oracle for stage H1. Declare the same types generically and
  compare typing, reduction and composition results on the kernel tests and
  the archived library. Retire the hand-coded rules only after they agree.
- **Negative tests:**
  - positivity violations, such as a sort in an arity or in data;
  - boundaries that disagree on overlapping faces;
  - clauses whose boundary misses its point clauses;
  - eliminating a `prop` sort into a family that is not a proposition
    without a squash clause;
  - index-level mismatches;
  - a use of a later constructor.
- **Provisional marker.** Until a stage's soundness note is reviewed, a result
  that uses a type admitted only by that stage lists `kernel extension:
  stage Hn` among its dependencies. It still computes, because this is not an
  axiom, but the trust extension stays visible.

## 5. Language

### Declarations

```
inductive Nat { zero; succ(n : Nat); }

inductive List(A : U) { nil; cons(head : A, tail : List(A)); }

inductive Susp(A : U) { north; south; meridian(a : A) : north = south; }

inductive Trunc(A : U) : prop { point(a : A); }

inductive Quotient(A : U, R : A -> A -> U) : set {
  class(a : A);
  glue(a, b : A, r : R(a, b)) : class(a) = class(b);
}

// Indexed families: parameters in parentheses, indices after the colon.
inductive Vec(A : U) : Nat -> type {
  nil : Vec(A, 0);
  cons(x : A, n : Nat, xs : Vec(A, n)) : Vec(A, succ(n));
}

inductive Id(A : U, a : A) : A -> type { refl : Id(A, a, a); }

inductive Ty { base; arrow(a, b : Ty); }
inductive Ctx { empty; extend(g : Ctx, a : Ty); }
inductive Var : Ctx -> Ty -> type {
  here(g : Ctx, a : Ty) : Var(extend(g, a), a);
  there(g : Ctx, a, b : Ty, v : Var(g, a)) : Var(extend(g, b), a);
}
inductive Tm : Ctx -> Ty -> type {             // intrinsically typed terms
  var(g : Ctx, a : Ty, v : Var(g, a)) : Tm(g, a);
  lam(g : Ctx, a, b : Ty, body : Tm(extend(g, a), b)) : Tm(g, arrow(a, b));
  app(g : Ctx, a, b : Ty, f : Tm(g, arrow(a, b)), x : Tm(g, a)) : Tm(g, b);
}

inductive Real : set with Close : Pos -> Real -> Real -> prop {
  rat(q : Rat) : Real;
  lim(x : Pos -> Real, cauchy : forall δ, ε : Pos. Close(δ + ε, x(δ), x(ε))) : Real;
  eq(u, v : Real, near : forall ε : Pos. Close(ε, u, v)) : u = v;

  rat_rat(q, r : Rat, ε : Pos, bound : abs(q - r) < ε) : Close(ε, rat(q), rat(r));
  rat_lim(q : Rat, y : Pos -> Real, cy : forall δ, ε : Pos. Close(δ + ε, y(δ), y(ε)),
          δ η : Pos, h : Close(η, rat(q), y(δ))) : Close(δ + η, rat(q), lim(y, cy));
  lim_rat(x : Pos -> Real, cx : forall δ, ε : Pos. Close(δ + ε, x(δ), x(ε)), r : Rat,
          δ η : Pos, h : Close(η, x(δ), rat(r))) : Close(δ + η, lim(x, cx), rat(r));
  lim_lim(x : Pos -> Real, cx : forall δ, ε : Pos. Close(δ + ε, x(δ), x(ε)),
          y : Pos -> Real, cy : forall δ, ε : Pos. Close(δ + ε, y(δ), y(ε)),
          δ η θ : Pos, h : Close(θ, x(δ), y(η))) : Close(δ + η + θ, lim(x, cx), lim(y, cy));
}
```

- **Header.** It declares every sort, with `with` joining companion sorts.
  Parameters are in parentheses and fixed across all constructors. Indices
  come after the colon, as a function type ending in the h-level: `type`
  (the default), `set` or `prop`. Constructors choose their own result
  indices, as `nil` and `cons` do.
- **Ordering.** Constructors are checked in order. Each may use every sort,
  and the constructors listed before it. `lim` uses the sort `Close`;
  `rat_lim` uses the constructor `lim` in its result.
- **Which sort.** The result type decides it: `: Real`, `: u = v` (a path in
  `Real`), or `: Close(…)`. Higher constructors state a `PathP` or square type.
- **Clarity.** The elaborator brings constructors into normal form, deciding
  which arguments are data and which are positions. Errors name the offending
  argument: a sort in negative position, a use before declaration, or a
  boundary face that disagrees, shown with both sides.

### Definitions: `match` over every sort at once

A definition out of an inductive-inductive type gives a function for each sort
it eliminates from. The companion's statement mentions the main function's
values at the indices. The elaborator reads those occurrences as the displayed
indices.

```
def neg(u : Real) : Real
  with neg_close(ε : Pos, u, v : Real, h : Close(ε, u, v)) : Close(ε, neg(u), neg(v))
= match {
  rat(q) => rat(-q);
  lim(x, c) => lim(fun δ => neg(x(δ)), fun δ ε => neg_close(c(δ, ε)));
  eq(u, v, near) i => eq(neg(u), neg(v), fun ε => neg_close(near(ε))) @ i;
  rat_rat(q, r, ε, bound) => rat_rat(-q, -r, ε, abs_neg_difference(q, r, ε, bound));
  rat_lim(q, y, cy, δ, η, h) => rat_lim(-q, fun δ => neg(y(δ)), fun δ ε => neg_close(cy(δ, ε)),
                                        δ, η, neg_close(h));
  lim_rat(x, cx, r, δ, η, h) => lim_rat(fun δ => neg(x(δ)), fun δ ε => neg_close(cx(δ, ε)),
                                        -r, δ, η, neg_close(h));
  lim_lim(x, cx, y, cy, δ, η, θ, h) =>
    lim_lim(fun δ => neg(x(δ)), fun δ ε => neg_close(cx(δ, ε)),
            fun δ => neg(y(δ)), fun δ ε => neg_close(cy(δ, ε)), δ, η, θ, neg_close(h));
};
```

- **Structural recursion.** A call on a position (`x(δ)`, `c(δ, ε)`, `h`) is
  structural and compiles to the displayed variable. Index arguments of a
  companion call are determined by the position's type and may be omitted, as
  in `neg_close(c(δ, ε))`. Any other recursive call is rejected, with the call
  named.
- **Computation makes the types line up.** In the `rat_lim` clause the
  required type is `Close(δ + η, neg(rat(q)), neg(lim(y, cy)))`. It reduces
  to the constructor's type because `neg` computes on `rat` and `lim`.
- **Path clauses** bind the constructor's interval variables after its
  arguments (`eq(u, v, near) i`). The kernel checks their endpoints against
  the point clauses.
- **Automatic clauses:**
  - clauses for formal compositions are never written;
  - squash clauses are generated when the target is a proposition, or a set
    for two-dimensional squash, using the h-level evidence of the target;
  - with a proposition-valued goal, every path and relation clause is
    discharged, so a proof needs only the point clauses of the main sort:

```
def neg_neg(u : Real) : neg(neg(u)) = u = match u {
  rat(q) => cong(rat, rat_neg_neg(q));
  lim(x, c) => lim_congruence(fun δ => neg_neg(x(δ)));
};
```

### Views

A view is any checked eliminator used with `match … using view`. The
elaborator generates two for every declaration:
- `T.rec`, non-dependent recursion into an algebra;
- `T.ind_prop`, induction into propositions with only the point clauses of
  the main sort.

The library adds analytic ones, such as extension of a Lipschitz map from
the rationals. That is the form most definitions out of the reals use.

```
def abs(u : Real) : Real = match u using lipschitz_extension(1, fun q => rat(abs(q)), rat_abs_lipschitz);
```

### Indexed families in use

`match` on an element of an indexed family also generalizes the goal over the
indices. Each branch's goal therefore uses the constructor's own result
indices:

```
computable def append(A : U, m, n : Nat, xs : Vec(A, m), ys : Vec(A, n)) : Vec(A, m + n)
= match xs {
  nil => ys;                                                      // goal: Vec(A, 0 + n) ≡ Vec(A, n)
  cons(x, k, rest) => cons(x, k + n, append(A, k, n, rest, ys));  // goal: Vec(A, succ(k) + n)
};

computable def J(A : U, a : A, C : forall b : A. Id(A, a, b) -> U, base : C(a, refl),
                 b : A, p : Id(A, a, b)) : C(b, p)
= match p { refl => base; };

def J_on_refl(A : U, a : A, C : forall b : A. Id(A, a, b) -> U, base : C(a, refl)) :
  J(A, a, C, base, a, refl) = base { rfl; }                       // J computes on refl

def Sem(a : Ty) : U = match a { base => Nat; arrow(a, b) => Sem(a) -> Sem(b); };
def Env(g : Ctx) : U = match g { empty => Unit; extend(g, a) => Env(g) and Sem(a); };

computable def eval(g : Ctx, a : Ty, t : Tm(g, a), env : Env(g)) : Sem(a) = match t {
  var(g, a, v) => lookup(g, a, v, env);
  lam(g, a, b, body) => fun x => eval(extend(g, a), b, body, (env, x));
  app(g, a, b, f, x) => eval(g, arrow(a, b), f, env)(eval(g, a, x, env));
};

evaluate append(Nat, 1, 1, cons(1, 0, nil), cons(2, 0, nil)) expecting cons(1, _, cons(2, _, nil));
```

- `computable` declarations are checked to have no non-computing
  dependencies.
- `evaluate` is a checked test of the normal form.
- `J_on_refl` holds by `rfl` because `J` computes on `refl`.
- In `eval`, the environment changes between recursive calls. The recursion
  is still structural in the term, so the elaborator generalizes the motive
  over the environment.

### Inspection and evaluation

- The inspector shows each declaration's normal form: data, positions and
  boundaries. It also shows the generated eliminator with its clause types,
  and each clause's computed displayed indices.
- `cli evaluate` normalizes a closed term. For a truncated existential it
  reads the witness off the base of the normal form. For example, it reports
  a rational within 10⁻⁶ of √2 from a closed proof of
  `Trunc(exists q : Rat. Close(1/1000000, sqrt(2), rat(q)))`.

Higher-level features built on this design are proposed separately in
[inductive-language-features.md](inductive-language-features.md). They
include theories, cells, relations and bundles, canonical quotients,
presentations and derived declarations.

## 6. Departures from existing work

| Choice | Instead of | Reason |
| --- | --- | --- |
| One signature format from ordinary data to induction-induction | Separate data, higher inductive and inductive-inductive mechanisms | One set of generated rules to trust; hand-coded formers become test oracles |
| Positions are cubes, so paths and squash arguments are positions | Special higher recursive arguments | Positivity and displayed types come from one rule |
| One heterogeneous formal composition per sort | Separate formal homogeneous composition and coercion | Half the formal constructors and reduction rules |
| Clause types from running the partial eliminator | A separate translation into displayed types | One reduction engine for computing and for typing |
| Index-line matching before falling back to formal composition | Always-formal coercion across indices | Closed data families keep constructor normal forms; the identity family still gets J computing on `refl` |
| Non-computing dependencies tracked per declaration, a `computable` modifier and `evaluate` directives | Computation as an informal expectation | Computability becomes a stated, checked and regression-tested property |
| H-level modifiers with generated squash and automatic clauses | Handwritten truncation constructors and clauses | The common cases, propositions and sets, need no boilerplate |
| Companion functions whose statements mention the main function | Explicit displayed-motive arguments | Definitions read like mutual structural recursion |
| Staged gate with a provisional dependency marker | Admitting everything at once, or not at all | Each class ships when its argument exists, visibly |

Established results still carry weight: Coquand–Huber–Mörtberg for higher
inductive types with parameters; Cavallo–Harper for indexed ones; and
Kaposi–Kovács for signatures of higher inductive-inductive types, which show
the class is coherent. No existing system ships stage H3 with full computation;
it is ours to establish.

## 7. Where the roadmaps took this

- **Kernel roadmap.**
  - Item H, stages H1–H4, owns the signature format, generated rules and
    trust controls.
  - G1–G3 are superseded:
    - truncation and set quotients become declarations at H1;
    - the identity family `Id` is an H2 declaration;
    - G2's resizing policy remains.
  - G4 generalizes to every declared type without path constructors.
  - The governing requirement is now "computability is expressible and
    preserved".
- **Ergonomics roadmap.**
  - Milestone 6 (theories, structures and notation) and milestone 7
    (inductive declarations and pattern matching) implement section 5 and the
    companion proposal.
  - Milestone 8 owns non-computing dependencies, `computable` and `evaluate`.
- **HoTT automation roadmap.**
  - B0, B2, B5, F3 and A9 are superseded. B5's views move to milestone 7.
  - A2, A5, D0a, D1 and E2 gain requirements from this design.
- **Reals roadmap.**
  - Cauchy reals are the initial model of a theory at H3.
  - Rationals are a canonical quotient.
  - Dedekind reals are the fallback, needing only H1.

## Open questions

1. **Arities that depend on positions.** Rejected at first. No known use
   needs them.
2. **Induction-recursion** (a type defined together with a function out of
   it, as for universes à la Tarski). Out of scope; the same normal form might
   extend to it.
3. **Signatures as data.** Reflecting signatures as a type of descriptions
   would allow deriving decidable equality, `T.ind_prop` and similar in the
   language rather than in the elaborator.
4. **Performance.** Generic reduction may be slower than the hand-coded rules.
   Measure against the archive before retiring them, and consider
   specializing hot signatures.
5. **Accumulating formal compositions.** Measure proof-term growth from formal
   compositions on realistic transports, and add reductions only where they
   are sound.
