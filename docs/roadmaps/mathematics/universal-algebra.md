# Universal algebra

Status: proposed on 2026-10-17 at the maintainer's request. Nothing below is
in the library. The three probes quoted here were checked on 2026-10-17 with
`node cli/repl.mjs check` against main `3be74796`, and again at `79d5cbf1`
during review; their files are not fixtures. UA0–UA6 remain unimplemented. This roadmap
builds on [core theories](../high-level-abstractions/core-theories.md) (L2.4,
L2.6) and the [categories roadmap](../high-level-abstractions/categories.md)
(L2.4b, L3.4, L3.5); it adds acceptance examples to those packages and does
not reorder the [work plan](../work-plan.md#first-actions).

The [simplicial roadmap](../hott/simplicial-types.md), proposed on
2026-10-24, adds later comparison targets. UA0–UA6 remain ordinary
set-based algebra and category theory, independent of the directed kernel.
They may use ST1's agreed, still unimplemented arrow spelling
`x ->[C] y`, which elaborates to `C.Arr(x, y)` here. Existing `U`, `IsSet`
and `set` keep their meanings; higher algebra is a separate coherent
presentation, not these declarations with their `set` annotations removed.

## Goal

Two statements, both inside Cubist:

1. **There is a category of universal algebras.** Its objects are equational
   theories, its arrows interpretations of one theory in another. It is
   univalent, so isomorphic theories are equal.
2. **In it, the theory of groups is the pushout of the theories of monoids
   and quasigroups over the theory of magmas.** Dually, the category of groups
   is equivalent to an explicit category of compatible monoid and quasigroup
   models over a shared magma (UA6), and every concrete group, the cyclic
   group of order three say, gives such a model. That this category is a
   pullback, by its universal property in a synthetic category of
   categories, is a later comparison (ST6), described in decision 7.

Today a `theory` declaration elaborates away: its models are a Σ record, its
homomorphisms a generated record, and the theory itself is not a value
([core theories](../high-level-abstractions/core-theories.md#models)). The
category in statement 1 therefore needs theories as values. The construction
chosen below is the abstract clone.

## Why clones

- **Presentations are the wrong objects.** The theory of groups is presented
  with an inverse; the pushout of the monoid and quasigroup presentations has
  two divisions instead. In a category of presentations they are different
  objects and statement 2 is false. They present the same term operations:
  `left_div(x, y)` is `inv(x) * y`, and `inv(x)` is `left_div(x, one)`.
- **A clone is the term operations without the carrier.** On a set, a clone
  is a family of operations `A^n -> A`, one set per arity, containing the
  projections and closed under substitution. The abstract version keeps the
  sets `T(n)` of n-ary operations, the projections and substitution, with
  three laws: substituting into a projection returns the chosen argument,
  substituting the projections changes nothing, and substitution is
  associative. The clone of an equational theory has `T(n)` the terms in n
  variables modulo the equations, which is the carrier of the free model on
  n generators. Term-equivalent presentations have the same clone.
- **Clones are an algebraic theory themselves.** A Nat-indexed carrier family
  with operations and equational laws is a theory the language accepts today
  ([theory families](../high-level-abstractions/core-theories.md#theory-families)).
  So the generated `Clone.Hom` is clone homomorphisms, `Clone.cat` is the
  category of statement 1 once L3.4's `T.cat` exists, and the structure
  identity principle (L2.4b) makes it univalent, since an algebraic theory is
  standard in the sense of the
  [categories roadmap](../high-level-abstractions/categories.md#decisions).
- **One-sorted finitary Lawvere theories and finitary monads on sets are the
  same objects.** Clones need no category library to be declared, which is
  why they come first; the Lawvere-theory view is a later equivalence
  (open question 1).

## Evidence

Three probes, each a self-contained Cubist module importing only the library.
Declaration counts include the generated theory interfaces.

### Probe 1: the pushout presentation and the equivalence of models

47 declarations. The pushout of two theories along an ancestor that holds
every member they share is a theory that extends both, since `extends`
amalgamates fields once per ancestor
([extension](../high-level-abstractions/core-theories.md#extension)). `Magma`
is the only ancestor `Monoid` and `Quasigroup` have in common:

```text
theory AssociativeLoop(U < UU0) extends Monoid, Quasigroup {}
```

Its record has the carrier, multiplication, associativity, the unit and its
two laws, both divisions and the four division laws; nothing is added. The
probe then proves, with the library's `inverse_equiv`:

```text
computable def group_as_pushout{{U < UU0}}(G : Group(U)) : AssociativeLoop(U)
computable def pushout_as_group{{U < UU0}}(L : AssociativeLoop(U)) : Group(U)
computable def group_round_trip{{U < UU0}}(G : Group(U)) : pushout_as_group(group_as_pushout(G)) = G
computable def pushout_round_trip{{U < UU0}}(L : AssociativeLoop(U)) : group_as_pushout(pushout_as_group(L)) = L
computable def group_is_pushout(U < UU0) : ContrEquiv(next(U), Group(U), AssociativeLoop(U))
def same_magma{{U < UU0}}(G : Group(U)) : group_as_pushout(G).quasigroup.magma = G.loop.quasigroup.magma { rfl; }
```

- A group's implemented divisions supply the quasigroup fields directly.
- The inverse of a pushout model is left division of the unit. Its
  left-inverse law needs cancellation and associativity; the quasigroup laws
  alone give `y * left_div(y, one) = one` and not the other order.
- Both round trips are equalities of models, written as paths in the Σ record
  with the kernel's pair eta: operations by function extensionality, laws by
  `prop_over` with `pi_is_prop` and the carrier's setness. There is no
  generated structure identity for models yet, so these paths are by hand.
- Both forgetful maps to `Magma` agree definitionally, so the equivalence
  lives over magmas.
- It computes: carried through the pushout presentation and back, the additive
  group of the integers inverts 3 to `class((0, 3))`.

### Probe 2: clones, their models and their free models

59 declarations. `Fin(n)` is `exists i : Nat. exists k : Nat. succ(i + k) = n`
until H2 supplies indexed families.

```text
theory Clone(U < UU0) {
  T(n : Nat) : set U;
  proj(n : Nat, i : Fin(n)) : T(n);
  subst(m, n : Nat, f : T(m), g : Fin(m) -> T(n)) : T(n);
  law subst_proj(m, n : Nat, i : Fin(m), g : Fin(m) -> T(n)) : subst(m, n, proj(m, i), g) = g(i);
  law proj_subst(n : Nat, f : T(n)) : subst(n, n, f, fun (i : Fin(n)) => proj(n, i)) = f;
  law subst_assoc(k, m, n : Nat, f : T(k), g : Fin(k) -> T(m), h : Fin(m) -> T(n)) :
    subst(m, n, subst(k, m, f, g), h) = subst(k, n, f, fun (i : Fin(k)) => subst(m, n, g(i), h));
}

theory Algebra(U < UU0, C : Clone(U)) {
  A : set U;
  act(n : Nat, f : C.T(n), v : Fin(n) -> A) : A;
  law act_proj(n : Nat, i : Fin(n), v : Fin(n) -> A) : act(n, C.proj(n, i), v) = v(i);
  law act_subst(m, n : Nat, f : C.T(m), g : Fin(m) -> C.T(n), v : Fin(n) -> A) :
    act(n, C.subst(m, n, f, g), v) = act(m, f, fun (i : Fin(m)) => act(n, g(i), v));
}
```

- `full_clone(U, A, A_is_set) : Clone(U)` is every operation
  `(Fin(n) -> A) -> A`; its laws hold by beta and eta, each a `refl`.
- The generated `Clone.Hom` is exactly clone homomorphisms: an arity-indexed
  map commuting with projections and substitution.
- `Algebra(U, C)` is the type of models of a clone, with no theory declaration
  for `C`'s operations. A set is a model of its own full clone, acting by
  application, with both laws by `refl`.
- `free_algebra(U, C, n) : Algebra(U, C)` is `C.T(n)` acting by substitution,
  with the projections as generators. Its universal property is proved
  generically: `free_extension(U, C, n, X, v)` extends an assignment of n
  elements of any model to a homomorphism from the free model,
  `free_extension_generator` evaluates it on generators, and
  `free_extension_unique` shows any homomorphism agreeing on generators
  equals it, by the law that substituting projections changes nothing.
  This is the content of L2.6's free-model capability, obtained once for
  every clone rather than derived per theory.
- `Algebra.Hom` is the generated homomorphisms. `hom_ext` proves two equal
  when their maps are, preservation being a proposition over set carriers,
  and the identity and associativity laws of the generated `id` and `compose`
  follow by `refl` on maps. So for every clone, the objects, arrows,
  identities, composition and laws of its category of models exist. Packaging
  them as a `Precategory` waits for L3.4; univalence waits for L2.4b.
- `fold` is a reserved generated name (E175), and the probe named the map
  `extension`. That word is a proposed ST2 keyword, and keywords take
  priority over library names, so the library uses `free_extension`. A
  function extensionality path passed to `cong` needs a `typed` ascription.

### Probe 3: a concrete group in both forms

22 declarations, importing probe 1. The cyclic group of order three is an
inductive type with three constructors; addition is rotation, the laws are
case analyses, and the carrier is a set by Hedberg from decidable equality.

```text
def c3_group : Group(U0)
def c3_pushout : AssociativeLoop(U0) := group_as_pushout(c3_group);
def ModelPullback(U < UU0) : next(U) :=
  exists m : Monoid(U). exists q : Quasigroup(U). m.semigroup.magma =[Magma(U)] q.magma;
def c3_pullback : ModelPullback(U0) := (c3_group.monoid, c3_group.loop.quasigroup, refl(c3_group.monoid.semigroup.magma));
def pushout_to_pullback{{U < UU0}}(L : AssociativeLoop(U)) : ModelPullback(U)
def c3_back : Group(U0) := pushout_as_group(c3_pushout);
def c3_round_trip : c3_back =[Group(U0)] c3_group := group_round_trip(c3_group);
```

- `evaluate c3_pushout.left_div(one3, two3) expecting one3;` and
  `evaluate c3_pushout.right_div(zero3, one3) expecting two3;` pass, as does
  the recovered inverse, `evaluate c3_back.inv(one3) expecting two3;`.
- For any concrete group the recipe is the same: build it with `Group.make`;
  the pushout model and the pullback element are projections, with the magma
  equality by `refl`.
- One language point: a `match` whose motive mentions the scrutinee must
  alias it, `match x as z return … z …` (E533).

What no probe reaches: the cyclic group as a model of the pushout *clone*.
That clone does not exist as a value; its n-ary operations are the free
associative loop on n generators, terms modulo equations. The free magma
(binary trees) and the free monoid (lists) are plain inductive types, and the
free group on generators with decidable equality, which `Fin(n)` has, is the
set of reduced words. The free quasigroup and the pushout presentation are
not built from normal forms here; the generic route is a quotient by an
inductively generated congruence: L2.6's construction, or H2's indexed
families.

## Decisions

1. **Clones are the objects.** `Clone(U)` enters the library as in probe 2,
   with `full_clone`, and `Clone.cat` is the category of universal algebras
   once L3.4 exists. Once L2.4d lands, `Clone`, `Algebra` and
   `AssociativeLoop` declare `deriving (morphisms)`, which their `T.Hom` and
   `T.cat` then require. `Fin` stays a Σ type over `Nat` until H2; the clone
   interface does not depend on which `Fin` is used.
2. **Models of a clone are a parameterized theory.** `Algebra(U, C)` as in
   probe 2, with `free_algebra` and its universal property in the library.
   Its category is `Algebra.cat` at each `C`, a category parameterized by an
   object of another; L3.4's `T.cat` must accept theory parameters.
3. **Every equational theory gets a clone.** For a one-sorted theory whose
   laws are equations and whose `free` capability checks, `T.clone : Clone(U)`
   has `T(n)` the carrier of the free model on `Fin(n)` and substitution by
   fold. Not every declared theory qualifies: `Field` has laws outside the
   equational fragment (truncated inverses of nonzero elements, `zero ≠ one`)
   and no free model, theory families and many-sorted
   theories are out of scope (open question 4), and L2.6's capability may
   fail. `T.clone` comes from L2.6's `free` capability and its universal
   equivalence, so it is a library function on L2.6's output rather than a
   new generator. As a fixed generated name, `clone` joins the
   [reserved names](../../guides/keywords.md), with user bindings migrated
   first. L2.6's equational strategy refuses implemented members (E881);
   `Group` has them, so lifting that refusal, by generating the fold's
   preservation proofs for implemented members, is a prerequisite. The
   syntactic alternative, terms modulo Birkhoff consequence, needs H2 for the
   consequence relation and a completeness proof; it is not the primary
   route.
4. **Models in a clone.** For an equational theory `T` and a clone `C`, `T.In(C)`
   is the record of an operation of `C` for each operation of `T`, with `T`'s
   laws as equations in `C`. Set models are the case `C = full_clone(A)`:
   `T(U) ≃ exists A : set U. T.In(full_clone(A))`. The universal property of
   `T.clone` then reads `Clone.Hom(T.clone, C) ≃ T.In(C)`, and in particular
   `Algebra(U, T.clone) ≃ T(U)`. Whether `T.In` is generated or written per
   theory is open question 3; the four theories of statement 2 can be done by
   hand first, which also defers reserving `In` as a generated name.
5. **Pushouts of clones come from `extends`.** For `R extends P, Q {}` with
   an empty body, whose shared members are exactly those of an ancestor `S`
   (as `Magma` is for `Monoid` and `Quasigroup`), an `R`-structure in any clone is a
   `P`-structure and a `Q`-structure agreeing on `S`, by the record's
   amalgamation and pair eta. When `P` and `Q` share members outside one
   ancestor, the pushout is over the theory of all shared members instead.
   With decision 4 that is the universal property: `R.clone` with its four
   clone homomorphisms satisfies L3.5's `IsPushout` in the ordinary category
   `Clone.cat`. This is UA5 and needs no synthetic category of categories.
6. **The equality.** `Group.clone ≅ AssociativeLoop.clone` is given on
   generators, `inv` to `left_div(x, one)` and the divisions to `inv(x) * y`
   and `x * inv(y)`. Its round trips are equations in free models, and an
   equation valid in every model holds in the free model, so probe 1's lemmas
   supply them. With `Clone.cat` univalent, the isomorphism is the equality
   `Group.clone = Monoid.clone ⊔_{Magma.clone} Quasigroup.clone`, where the
   right side is the pushout object, unique up to equality in a univalent
   category.
7. **The dual statement in models.** Probe 1's equivalence is the object part
   of `Group.cat ≃ Monoid.cat ×_{Magma.cat} Quasigroup.cat`. The arrow part is
   the `Hom` correspondence: `Group.Hom` carries preservation fields for the
   implemented divisions, so a group homomorphism is an associative-loop
   homomorphism and conversely, with `map_inv` derived from `map_left_div`
   and `map_one`. First build an explicit `Precategory` using a shared-carrier
   presentation: monoid and quasigroup structures on one magma, with arrows
   pairs of homomorphisms sharing their magma map. Prove the comparison with
   probe 3's Σ-with-path `ModelPullback`, including transport of arrow data
   along its magma equality; the presentations are not definitionally the same.
   L3.5's `IsPullback` does not apply here, since it needs an ambient
   precategory and L3.4's precategories have hom-sets, while functors between
   univalent categories form no set (those from the terminal category into
   `Group.cat` are the groups). UA6 therefore proves an equivalence of
   categories with L3.4's functors, not an `IsPullback` certificate.
   ST6 later proposes the pullback universal property in a synthetic
   category of categories. It needs ST4's checked interpretations of these
   model categories, a comparison with this explicit construction, and the
   mapping-space universal property, including its compatibility with the
   forgetful functors. The UA6 equivalence alone supplies none of that
   automatically.
8. **Universes.** `Clone(U) : next(U)` and `Group(U) : next(U)`; the
   equivalence of probe 1 is in `ContrEquiv(next(U), …)`. Statement 2 is at
   each fixed `U`. Decision 7's pullback precategory has objects in
   `next(U)`, as `ModelPullback(U)` does, and hom-sets in `U`, as `T.cat`
   does for these theories, so it is a `Precategory(next(U), U)`. `T.clone`
   for a theory whose models are in `U` lives in
   `Clone(U)` when the free model's carrier does, which L2.6's strategy
   provides.

## Milestones

| Milestone | Content | Acceptance | Depends on |
| --- | --- | --- | --- |
| **UA0** Prerequisites | L2.4d morphism opt-ins; L3.4 `Precategory`, functors, equivalences of categories, `T.cat` with theory parameters; L3.5 `IsPushout`; L2.4b structure identity; L2.6 `free` with its universal equivalence, and E881 lifted for implemented members | Theirs | — |
| **UA1** Clones and their models | Probe 2 in the library: `Clone`, `full_clone`, `Fin`, `Algebra(U, C)`, `free_algebra`, `free_extension` with its generator and uniqueness laws, `hom_ext` and the category laws; fixtures for each; `deriving (morphisms)` on `Clone` and `Algebra` once L2.4d lands | The library's statements check; `Clone.cat` and `Algebra.cat` once UA0's L3.4 exists | None of UA0 for the statements; L2.4d and L3.4 for the categories |
| **UA2** Groups as pullback models | Probe 1 and probe 3 in `library/algebra.cubist` and fixtures: `AssociativeLoop`, the equivalence with `Group(U)`, the `Hom` correspondence, the Σ-with-path pullback and its equivalence with `AssociativeLoop(U)`, the cyclic group as an element | `evaluate` of divisions and recovered inverses on the integers and on `C3`; the `Hom` correspondence composes with identities | None of UA0 |
| **UA3** The clone of a theory | `T.clone` from L2.6's free models; `Algebra(U, T.clone) ≃ T(U)` for `Magma`, `Monoid`, `Quasigroup` and `Group`; the free magma (binary trees) and free monoid (lists) built by hand and shown equal to the generated clones | `Group.clone.T(1) ≃ Z`, the library's integers, as the free group on one generator; `Monoid.clone.T(n) ≃ List(Fin(n))` | UA1; L2.6 with E881 lifted |
| **UA4** Interpretations | `T.In(C)` for the four theories, `Clone.Hom(T.clone, C) ≃ T.In(C)`, and the principle that an equation valid in every set model holds in `T.clone` | A clone homomorphism `Monoid.clone -> Group.clone` built from an interpretation; the equation `left_div(x, one) * y = left_div(x, y)` transported into `AssociativeLoop.clone` | UA3 |
| **UA5** Group as a pushout of clones | `IsPushout(Clone.cat, …)` for every `R extends P, Q {}` with an empty body whose shared members are exactly an ancestor's, then the square of statement 2; `Group.clone ≅ AssociativeLoop.clone`; the equality by univalence of `Clone.cat` | The equality `Group.clone = Monoid.clone ⊔ Quasigroup.clone` over `Magma.clone` checks; `IsPushout` is a proposition and the pushout object is unique up to equality | UA4; L3.5; L2.4b |
| **UA6** Categories of models as pullbacks | Explicit shared-carrier `Precategory` (decision 7), its comparison with the Σ-with-path presentation, and `Group.cat` equivalent to it; `Algebra.cat(T.clone) ≃ T.cat`; the semantics functor on the square of statement 2. Its pullback universal property in a synthetic category of categories is a separate ST6 target | `C3` and the integers transported across both equivalences, with their divisions evaluated; arrow comparisons preserve identities and composition | UA2, UA3, UA4; L3.4; no directed-kernel dependency |

## Order

UA1 and UA2 need nothing from the categories packages and can enter the
library now, as the probes show. They are also the natural first clients of
L3.4's `T.cat` with theory parameters and of L2.4b's structure identity for
records, so they belong early in the
[language progression](../work-plan.md#first-actions), alongside the
algebraic-model examples of its first row. UA3 follows L2.6's universal
proofs and is the first consumer of free models with implemented members.
UA4 needs no categories package and prepares the next two. UA5 is an
acceptance example for L3.5's `IsPushout`; UA6 for L3.4's functors and
equivalences of categories. None of them resumes the paused mathematics
projects.

## Language work it drives

| Testbed | Language capability to develop and validate |
| --- | --- |
| Clones and `Algebra(U, C)` | Nat-indexed carrier families with function-typed operation arguments; parameterized theories whose parameter is a model; `T.cat` for parameterized theories; universe levels `next(U)` in generated interfaces |
| Equalities of models and homomorphisms | Structure identity for theory records (L2.4b), replacing hand-written record paths with `prop_over`; `T.Hom.ext` |
| `T.clone` and `T.In(C)` | L2.6's free capability with implemented members; generated interfaces that quantify over another theory's models; the equation-transport principle |
| Pushouts of clones and pullbacks of categories | L3.5's predicates on supplied cocones; functors between parameterized categories and an explicit pullback precategory; L3.4's equivalences of categories; univalence of `T.cat` for algebraic theories |
| Concrete groups | Decidable equality and Hedberg for enumerations; `match` motives over the scrutinee; `Fin` until H2 |

## Open questions

1. **Clone or Lawvere theory as the library primitive.** Clones need no
   category library; Lawvere theories are categories with finite products and
   fit L3.4's vocabulary. Decision: clones first, with the equivalence of the
   two as later work once L3.4 has finite products.
2. **`Fin`.** The Σ-type encoding works for the clone interface and the
   probes. Whether `T.clone`'s free models want an inductive `Fin` after H2
   is open; the interface should not change.
3. **Generated or hand-written `T.In(C)`.** A generator is one more
   interface per theory, like `T.Hom`. The four theories of statement 2
   suffice by hand; generate only when a second client appears.
4. **Many-sorted theories.** Clones are one-sorted. Theory families and
   multi-carrier theories such as modules need many-sorted clones or Lawvere
   theories; out of scope here.
5. **Equivalence of categories.** Decision 7 proves UA6 as an equivalence of
   categories between `Group.cat` and an explicit pullback precategory. Which
   presentation of equivalence L3.4 supplies (a functor that is fully
   faithful and essentially surjective, or an adjoint equivalence) decides
   how UA6 states it; both are provable from probe 1's maps and the `Hom`
   correspondence.
