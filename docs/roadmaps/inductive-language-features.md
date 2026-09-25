# Language features for theories, inductive and higher inductive declarations

Status: adopted on 2026-09-25 by [ergonomics](proof-ergonomics-roadmap.md)
milestones 6 and 7; nothing is implemented yet. It builds on
[the higher inductive-inductive type design](higher-inductive-types-design.md)
(kernel roadmap item H, stages H1–H4) and on
[G0](cubical-kernel-roadmap.md) (universe-generic checking).

Every feature here is untrusted elaboration. Each one produces kernel
signatures, eliminator applications and ordinary checked terms, and needs no
kernel rule beyond the design it builds on. Each section states what the
feature elaborates to, the stage it needs, and how it keeps computability
expressible and preserved.

The problems these features answer come from the archived library and from
the proof migration:

| Problem | Where we saw it |
| --- | --- |
| Algebra lemmas repeat the whole structure as arguments | `F, zero, one, addF, mulF, negF, ring` repeated on every ring lemma; the migration's biggest token cost |
| The structure identity principle takes dozens of declarations per structure | `structured_sets` (40 declarations), `group_univalence`, `group_total_identity` |
| Operations on quotients need hand-built descent in two or three arguments | `quotient_operations`, `quotient_group_universal` |
| Constructor argument groups repeat | Four closeness constructors of the Cauchy reals each restate an approximation and its Cauchy proof |
| Quotients do not print or decide equality | Rationals as a quotient have no canonical closed forms |
| Setness of data types is proved by hand | `integers_are_a_set`, `fin_is_set`, `hedberg` instances |
| One structure, several presentations | Integers as an inductive type, as differences, as "a point and an equivalence" |

## 1. Theories: one declaration for structures, initial models and universal properties

A **theory** declares sorts, operations and laws once. From that one
declaration the language derives:

- **`T.Model`**, the record type of models. Fields are the carriers,
  operations, laws and h-level evidence. It elaborates to a Σ type with
  definitional eta, so it serves as the structure record of ergonomics
  milestone 6.
- **`T.Hom(M, N)`**, homomorphisms. For sorts that are sets, preserving the
  laws is automatic. For untruncated sorts, the fields include the required
  coherence cells.
- **`T.Iso(M, N)`** and **`T.equality : (M = N) ≃ T.Iso(M, N)`**. This is the
  structure identity principle, generated once per theory by the structure
  description machinery of HoTT F1.
- **`T.Displayed(M)`**, displayed models, for induction.
- **`initial T`**, when the theory is strictly positive: the initial model as
  a declared type. Its constructors are the operations and laws. It comes
  with:
  - `fold(M)`, the unique homomorphism into any model, computing on
    constructors;
  - `fold_unique`, its uniqueness;
  - `universal : (initial T → M) ≃ T.Hom(…)` in the form the theory's shape
    allows.
- **`free T on A`**: the initial model of `T` extended with generators
  `gen(a : A)`, whose `fold(M, f)` extends `f : A → M`.

```
theory Monoid {
  sort M : set;
  unit : M;
  mul(x y : M) : M                        notation x * y;
  law unit_left(x : M) : unit * x = x;
  law unit_right(x : M) : x * unit = x;
  law assoc(x y z : M) : (x * y) * z = x * (y * z);
}

theory Group extends Monoid {
  inv(x : M) : M;
  law inv_left(x : M) : inv(x) * x = unit;
}

def square(G : Group.Model, x : G.M) : G.M = x * x;      // notation from G's theory
def conjugate(G : Group.Model, g x : G.M) : G.M { open G; exact g * x * inv(g); }

inductive FreeGroup(A : U) = free Group on A;
computable def exponent_sum(A : U) : Group.Hom(FreeGroup(A).model, IntAdd) =
  FreeGroup(A).fold(IntAdd, fun a => 1);
```

- **One source for records and data types.** A structure declaration and an
  inductive declaration become one form. A plain structure is a theory used
  only for its models; a plain inductive type is a theory used only for its
  initial model. `inductive` remains shorthand for the second.
- **The repetition disappears.** A ring lemma takes `(R : CommRing.Model)` and
  writes `x * (y + z)` in `R`'s notation, instead of seven arguments per
  lemma.
- **Identity for free.** Structure identity is generated per theory, so
  `group_univalence` becomes an instance, not a development.
- **Recursion principles have an explanation.** For inductive-inductive types
  the recursion principle is folding into a model. The Cauchy reals' Lipschitz
  extension is exactly that: build a model on the target from `f`, then fold.
- **Extension.** `extends` reuses sorts, operations and laws. Every model of
  `Group` has an underlying `Monoid.Model`, with the forgetful map generated.

The surrounding constructions compose in the same way:

```
theory Loop { sort S : type; base : S; law loop : base = base; }
inductive Circle = initial Loop;          // Loop.Model on X is a point with a loop
// generated: Circle.universal : (Circle -> X) ≃ Loop.Model on X

theory CauchyStructure {
  sort R : set;
  relation Close(ε : Pos) on R : prop     notation u ≈[ε] v;
  bundle Approx = (x : Pos -> R, cauchy : forall δ ε : Pos, x(δ) ≈[δ + ε] x(ε));
  rat(q : Rat) : R;
  lim(a : Approx) : R;
  law eq(u v : R, near : forall ε : Pos, u ≈[ε] v) : u = v;
  rat_rat(q r : Rat, ε : Pos, bound : abs(q - r) < ε) : rat(q) ≈[ε] rat(r);
  rat_lim(q : Rat, a : Approx, δ η : Pos, h : rat(q) ≈[η] a.x(δ)) : rat(q) ≈[δ + η] lim(a);
  lim_rat(a : Approx, r : Rat, δ η : Pos, h : a.x(δ) ≈[η] rat(r)) : lim(a) ≈[δ + η] rat(r);
  lim_lim(a b : Approx, δ η θ : Pos, h : a.x(δ) ≈[θ] b.x(η)) : lim(a) ≈[δ + η + θ] lim(b);
}
inductive Real = initial CauchyStructure;                  // stage H3

theory CwF {                                               // the syntax of type theory
  sort Con : set;  sort Ty(g : Con) : set;  sort Sub(d g : Con) : set;
  sort Tm(g : Con) : Ty(g) -> set;
  empty : Con;  extend(g : Con, a : Ty(g)) : Con;
  // substitution, weakening, variables, Π and their laws
}
inductive Syntax = initial CwF;
computable def interpret : CwF.Hom(Syntax.model, SetModel) = Syntax.fold(SetModel);
```

**Elaboration.** `T.Model`, `T.Hom`, `T.Displayed` and the fold are generic
constructions over the theory, which the elaborator computes and the kernel
checks. `initial T` is the kernel signature whose constructors are `T`'s
operations and laws; `fold` is its eliminator with constant motives.

**Stages.**
- H1 (one sort, no indices): `Monoid`, `Group`, `Loop`.
- H2 (indexed families): theories with one indexed sort.
- H3 (inductive-inductive): `CauchyStructure`, `CwF`.

Models and homomorphisms need no stage at all, because they are records.

**Computability.** `fold` computes on constructors, and models are records
with eta. A closed `interpret(t)` for closed syntax `t` normalizes: the
evaluator is a fold into the set model.

## 2. Cells: boundaries written the way they are drawn

Path and higher constructors, and their clauses, take any of these
equivalent spellings. Each denotes a kernel boundary system, and the
inspector draws its diagram.

```
inductive Torus {
  base;
  p : base = base;
  q : base = base;
  surf : cell(i, j) {                 // named faces; any dimension
    i = 0 => q @ j;  i = 1 => q @ j;
    j = 0 => p @ i;  j = 1 => p @ i;
  };
}

inductive Torus2 {                    // the same space, with an equation between composites
  base; p : base = base; q : base = base;
  surf : trans(p, q) = trans(q, p);
}
```

- `x = y` and `PathP(…)` remain for dimension one.
- `cell(i, j, …) { face => term; … }` states the boundary as a system. It is
  exactly the kernel form, so errors show the face and both sides.
- An equation between composite paths gives a higher cell whose sides are
  the composites. It is a different signature for an equivalent space,
  and a generated lemma relates it to the square form.
- Clauses bind the cell's variables (`surf i j => …`). Their boundary
  obligations display the same diagram.

**Stage** H1. **Computability:** path constructors compute on their faces by
definition.

## 3. Relations and argument bundles

**Relations** declare a proposition-valued family on a sort, with its
notation:
- `relation Close(ε : Pos) on Real : prop notation u ≈[ε] v;` declares the
  sort `Close : Pos -> Real -> Real -> prop`;
- the notation is scoped to the declaration and its importers;
- a lemma that the relation is a proposition is generated.

**Bundles** name a repeated group of constructor arguments:
`bundle Approx = (x : Pos -> R, cauchy : …)`.
- Constructors take `a : Approx` and project `a.x`.
- A pattern `lim(a)` binds the bundle.
- The elaborator flattens bundles into the constructor's data and positions,
  so strict positivity and structural recursion are checked on the flattened
  form: a call on `a.x(δ)` is structural.
- In the Cauchy reals above, every closeness constructor that mentions a limit
  shrinks to one argument.

**Stage:** H3 for relations over the same declaration's sorts; otherwise any.
**Computability:** unaffected, since both are elaboration only.

## 4. H-levels by proof first

`: set` on a declaration means "this type must be a set". The elaborator
tries to prove it before adding a squash constructor:

- **No path constructors, and every argument type a set:** it generates the
  type's path characterization (below) and proves setness from it. There is
  no squash constructor, so closed elements keep constructor normal forms and
  equality stays decidable where the arguments' equality is.
- **Otherwise:** it adds the squash constructor.

The inspector reports which case happened. Writing `set!` forces the
constructor. `: prop` follows the same rule, using the generated
characterization to show that any two elements are equal.

**Why:** a squash constructor on a data type makes formal compositions
canonical and costs computation for nothing. Proving setness instead keeps
it.

## 5. Obligations separate from computational content

The point clauses of a `match` define a function; its path clauses prove
coherence. The two can be written apart:

```
def neg(x : Rat) : Rat = match x {
  class(a, b) => class(-a, b);
} obligations {
  glue(a, b, c, d, cross) => glue(-a, b, -c, d, cross_neg(cross));
};

def add(x y : Rat) : Rat = match x, y {
  class(a, b), class(c, d) => class(a * d + c * b, b * d);
} obligations by respects_each_argument {
  left(…) => …;       // one respect proof per argument,
  right(…) => …;      // not one per pair of constructors
};
```

- The elaborator names and prints every obligation as a goal. It shows the
  equation in its non-dependent form when the target is non-dependent.
  Obligations can be closed with any tactic: `obligations by hlevel;` or
  `by simp only […];`.
- **Several quotient arguments into a set** need one respect proof per
  argument. The mixed square clauses follow from the target being a set, so
  the elaborator generates them. That replaces the archive's two- and
  three-class descent machinery.
- Untruncated targets still need every cell, and the elaborator lists them.

**Computability:** point clauses are unchanged, and obligations are proofs.

## 6. Dependent pattern matching on indexed families, without K

Matching an element of an indexed family unifies the constructor's result
indices with the scrutinee's:

```
def head(A : U, n : Nat, xs : Vec(A, succ(n))) : A = match xs {
  cons(x, _, _) => x;                 // nil is impossible: 0 ≠ succ(n)
};
```

- **Unification** uses the generated injectivity and disjointness of data
  constructors, and solves a variable when it does not occur in the other
  side.
- **No K.** A reflexive equation `x = x` is deleted only with a proof that its
  type is a set, found by the h-level solver; otherwise the match is
  rejected with the unresolved equation shown. Loops stay loops (HoTT
  invariant 5).
- **Coverage.** Missing branches must be impossible. The elaborator shows
  the conflicting constructors, or asks for the branch.

**Computability.** Unification inserts transports along generated paths. On
closed data those compute. The inspector flags inserted transports on
non-propositional data, as HoTT invariant 4 requires.

## 7. Canonical quotients

A quotient with a normalizing function is represented by its normal forms,
while keeping the quotient's interface:

```
quotient Rat = Int and Pos by (a, b) ~ (c, d) := a * d = c * b
  canonical reduce                                // lowest terms
  proving related_to_normal : forall x, x ~ reduce(x)
      and normal_respects : forall x y, x ~ y -> reduce(x) = reduce(y);
```

- **Carrier.** The subtype `exists x : Int and Pos, reduce(x) = x` of fixed
  points. The underlying type must be a set, which makes the fixed-point proof
  a proposition.
- **Interface.**
  - `class(x)` is `(reduce(x), idempotence)`;
  - `glue` comes from `normal_respects` and subtype extensionality;
  - the eliminator is a view built on the fixed-point subtype, with the
    quotient universal property proved generically.
- **Computation.**
  - Closed rationals normalize to lowest terms, and `evaluate` prints them.
  - Equality is decidable whenever it is decidable on the representatives.
  - The eliminator computes as `elim(class(x)) ≡ f(reduce(x))`: definitional
    on canonical forms, and propositional for an arbitrary representative.
- **Trade-off.** The quotient type of stage H1 has `elim(class(x)) ≡ f(x)`
  instead, but no canonical forms. Declaring both gives a generated
  equivalence between them for transfer.

**Stage:** none; it is a subtype and a view. **Computability** improves: this
is how we get decimal-style answers out of the rationals.

## 8. Presentations: matching with another type's constructors

When two types are equivalent, one can be matched using the other's
constructors:

```
presentation Int as Successor.initial by int_successor_equivalence;

def double(z : Int) : Int = match z using Successor {
  zero => zero;
  succ(w) => succ(succ(double(w)));
  pred(w) => pred(pred(double(w)));
} obligations { pred_succ(w) => …; succ_pred(w) => …; };
```

- The elaborator transports the other type's eliminator along the
  equivalence. So a proof can use the "point and equivalence" presentation of
  the integers, as the circle's fundamental group wants, while computation
  uses the inductive representation.
- Several presentations of one type can coexist, and each is a view.

**Computability:** it runs through the equivalence's maps, which compute when
they are computable, and `computable` checks exactly that.

## 9. Derived declarations

`deriving (…)` on an `inductive` or `theory` asks the elaborator to generate
checked declarations:

| Derivation | For | Result |
| --- | --- | --- |
| `paths` | Types without path constructors | Encode–decode characterization `x = y ≃ Code(x, y)`, with injectivity and disjointness of constructors as corollaries |
| `decidable_equality` | Types without path constructors whose arguments have decidable equality | A computable decision procedure |
| `universal` | Every declaration | The maps-out equivalence with models |
| `irrelevance` | Constructors with proposition-valued arguments | `lim(x, c) = lim(x, c')` without writing the proof |
| `ind_prop`, `rec` | Every declaration | Induction into propositions and non-dependent recursion, as views |

- `paths` and `decidable_equality` supply section 4's setness proofs and
  section 6's unification rules. Deriving them is what lets a data type avoid
  a squash constructor.
- Every derived declaration is an ordinary term, checked by the kernel. It is
  marked `computable` when its dependencies allow.

## 10. Smaller conveniences

- **Nested declarations.** A declared type may occur inside a strictly
  positive type constructor, as in `node(children : List(Tree(A)))`. The
  elaborator translates this to a mutual declaration, together with a
  generated equivalence between the auxiliary type and `List(Tree(A))`.
- **Sections over models.** `section (R : CommRing.Model) { open R; … }`
  shares the model and its notation across lemmas. This replaces milestone
  6's separate section feature.
- **Theory morphisms.** `interpret Group in Monoid by …` records a translation
  between theories. Forgetful maps and free-model adjunctions are generated
  from it. This is later work.

## Priorities

| Tier | Features | Why first |
| --- | --- | --- |
| 1 | Theories (models, homomorphisms, identity, initial, fold); cells; relations and bundles; h-levels by proof; obligations; dependent matching without K; `paths`, `decidable_equality`, `universal` derivations | Remove the largest repetitions we measured and make the stages H1–H3 declarations readable |
| 2 | Canonical quotients; presentations; nested declarations; sections over models | Computation and multi-presentation reasoning for numbers and algebra |
| 3 | Theory morphisms; reflecting signatures as data | Later, once the generic constructions exist |

## Effect on the other roadmaps

- **Ergonomics milestone 6** (records, scoped notation, sections) merges into
  theories: models are the records, notation belongs to the theory, and
  sections range over models. Algebraic normalization then targets
  `CommRing.Model` directly.
- **HoTT F1** (structure descriptions and identity) becomes the engine behind
  `T.equality`. **F2**'s transfer uses presentations and generated
  equivalences.
- **The rebuild** can state its algebra as theories from the start: monoids,
  groups, rings, fields, vector spaces and ordered fields. Its numbers can use
  canonical quotients for the rationals, and its reals the initial model of
  `CauchyStructure`.

## Open questions

1. **Universe levels of generated records.** A model of a theory with a sort
   in `U` lives in `next(U)`. With G0 this is automatic, but it should be
   visible in signatures.
2. **Coherence for untruncated theories.** For theories like `Loop`, `T.Hom`
   needs cells up to the laws' dimension. Beyond two dimensions the generated
   fields grow quickly. Decide where to stop, and whether to generate only
   `universal` there.
3. **Choice of initial-model presentation.** A theory law can be stated as an
   equation between composites or as a square; the two give equivalent but
   different signatures. The first form written is the one used, and the
   other is related by a generated lemma. Confirm this is what users expect.
4. **Canonical quotients over non-sets.** Rejected. Their fixed-point
   carrier would not be a proposition-valued subtype.
