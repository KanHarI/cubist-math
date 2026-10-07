# Language features for theories, inductive and higher inductive declarations

Status: adopted on 2026-09-25 by [ergonomics](proof-ergonomics-roadmap.md)
milestones 6 and 7. One-sort `inductive` declarations (work-plan L2.1) and
explicit `match` (L2.2a) were released with H1 on 2026-10-02, on by
default, in the subset the [H1 specification](h1-signature-specification.md)
admits, with explicit `obligations` (L2.2b). Core theories, section 1's
models, homomorphisms, isomorphisms, notation, sections and `extends`, were
implemented on 2026-10-05 (work-plan L2.4, [core theories](core-theories.md)),
and the library's algebraic hierarchy is written in them. Their syntax
revision, L2.4c, was done on 2026-10-06
([core theories](core-theories.md#revision-l24c)): carriers as fields,
`M : set U`, the theory's name as its models' type, theory families,
relation fields as families of propositions with notation, and `use`.
Initial and free models have their contract and first slice (L2.6,
2026-10-06): `initial N : T(…);`, `free W(A : U0) : T(…) on A;`, `N.model`
and `N.fold`. Squares have the box notation and `library/squares.cubist`
(L2.8, 2026-10-06). Uniqueness and `universal`, generated identity, the
`cell` face syntax for constructors, relations on declared types and
bundles, proof-first h-levels, per-argument obligations, dependent
matching, canonical quotients, presentations and derivations remain
proposals. Code blocks are proposed syntax unless they say they check. The [audit of 2026-09-28](audits/2026-09-28-audit.md) corrected
three promises here: the universal property of section 1, `Torus2` in
section 2 and proof-first h-levels in section 4.
G0 and the shared goal-layer core are delivered as of 2026-09-27. It builds on
[the higher inductive-inductive type design](higher-inductive-types-design.md)
(kernel roadmap item H, stages H1–H4) and on
[G0](cubical-kernel-roadmap.md) (universe-generic checking).

Examples write `A : U` with `U` unbound. They presuppose the implicit
universe binders of ergonomics milestone 5; under L1.1 each reads
`(U < UU0, A : U)`.

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

A **theory** declares sorts, operations and laws once. Its model record is
available independently of optional derivations. The revised
[categorical roadmap](categories.md) makes morphisms opt-in, and
[L2.6](core-theories.md#initial-and-free-models-l26) requires checked
`deriving (morphisms, free)` or the weaker `deriving (morphisms, initial)`.
These requests may fail; arbitrary propositional laws remain valid theory
fields and become proof obligations in generated models. The interfaces are:

- **`T(U)`**, the record type of models (named `T.Model` until L2.4c).
  Fields are the carriers,
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
- **`initial T`**, after a successful `initial` or `free` derivation: an
  initial model for the selected morphisms. A strictly positive equational
  presentation has an H1 construction strategy; positivity alone does not
  establish its laws or universal property. The checked capability includes:
  - `fold(M)`, the unique homomorphism into any model, computing on
    constructors;
  - `fold_unique`, its uniqueness;
  - `universal`, stated as separate typed results (corrected on
    2026-09-28): for a fixed model `M`, `T.Hom(initial T, M)` is
    contractible, which is `fold` and `fold_unique` together; for
    `free T on A`, `T.Hom(free T on A, M) ≃ (A → M.carrier)`; and a
    characterization of plain maps out of the carrier only where the
    theory's constructor and clause data give one, as for `Loop` below.
    An earlier draft wrote `(initial T → M) ≃ T.Hom(…)`, which conflates
    carrier functions with homomorphisms: the initial monoid has a
    singleton carrier, so it has two functions into a two-element monoid
    but one homomorphism. Higher theories need their coherence fields in
    `T.Hom` before any such statement. Work-plan L2.6 specifies this
    contract before `universal` is generated.
- **`free T on A`**, after successful `deriving (morphisms, free)`: the
  registered free construction instantiated at `A`, whose `fold(M, f)`
  extends `f : A → M.carrier`. Its universal property is relative to the
  selected carrier-forgetting functor. Taking `A = Void` supplies initiality;
  an initial-only capability does not supply free models on other types.

The examples below are schematic targets, subject to these derivation
obligations and the applicable kernel stage. A law such as `zero != one`
requires a proof in the candidate model. Unsupported construction or failed
proof search reports the outstanding obligation, not mathematical
nonexistence. `Field` can have morphisms while initial/free derivation fails.

This block is in the implemented syntax (L2.4, L2.4c and L2.6's first
slice). It checks after importing `nat`, `hlevels` and `integers` and
`use nat;`, with `IntAdd : Group(U0)` the integers under addition:

```
theory Monoid(U < UU0) deriving (morphisms, free) {
  M : set U;
  unit : M;
  mul(x, y : M) : M notation x * y;
  law unit_left(x : M) : unit * x = x;
  law unit_right(x : M) : x * unit = x;
  law assoc(x, y, z : M) : (x * y) * z = x * (y * z);
}

theory Group(U < UU0) extends Monoid deriving (morphisms, free) {
  inv(x : M) : M;
  law inv_left(x : M) : inv(x) * x = unit;
}

def square(G : Group(U0), x : G.M) : G.M := G.(x * x);     // notation from G's theory
def conjugate(G : Group(U0), g, x : G.M) : G.M { use G; exact g * x * inv(g); }

free FreeGroup(A : U0) : Group(U0) on A;
computable def exponent_sum(A : U0) : Group.Hom(FreeGroup.model(A), IntAdd) :=
  FreeGroup.fold(A, IntAdd, fun (a : A) => int_one);
```

- **Shared construction machinery.** The H1 strategy builds a theory's
  free carrier using an ordinary inductive declaration. An ordinary
  `inductive` still supplies its own eliminator without requesting or
  establishing a categorical initial/free capability.
- **The repetition disappears.** A ring lemma takes `(R : CommRing(U))` and
  writes `x * (y + z)` in `R`'s notation, instead of seven arguments per
  lemma.
- **Identity for free.** Structure identity is generated per theory, so
  `group_univalence` becomes an instance, not a development.
- **Recursion principles have an explanation.** For inductive-inductive types
  the recursion principle is folding into a model. The Cauchy reals' Lipschitz
  extension is exactly that: build a model on the target from `f`, then fold.
- **Extension.** `extends` reuses sorts, operations and laws. Every model of
  `Group` has an underlying model of `Monoid`, `G.monoid`, with the
  forgetful map generated.

The surrounding constructions compose in the same way. The `Loop` and
`CwF` theories below check as written. Their `initial` declarations and
`CwF.Hom` are proposed: `initial` refuses `Loop`'s untruncated carrier
today (E853; L2.6 now defers categorical initiality until morphism coherences are specified), `CwF`'s models have no homomorphisms yet
(E817), and several carriers need H3.

```
theory Loop(U < UU0) { M : U; base : M; loop : base = base; }
// Ordinary recursion is available; categorical initiality needs coherences.
inductive Circle { base; loop : base = base; }
```

`CauchyStructure` is the 2026-09-25 proposal, with section 3's relations
and bundles; core theories has the implemented syntax.

```
theory CauchyStructure deriving (morphisms, initial) { // later strategy
  sort R : set;
  relation Close(ε : Pos) on R : prop     notation u ≈[ε] v;
  bundle Approx = (x : Pos -> R, cauchy : forall δ, ε : Pos. x(δ) ≈[δ + ε] x(ε));
  rat(q : Rat) : R;
  lim(a : Approx) : R;
  law eq(u, v : R, near : forall ε : Pos. u ≈[ε] v) : u = v;
  rat_rat(q, r : Rat, ε : Pos, bound : abs(q - r) < ε) : rat(q) ≈[ε] rat(r);
  rat_lim(q : Rat, a : Approx, δ η : Pos, h : rat(q) ≈[η] a.x(δ)) : rat(q) ≈[δ + η] lim(a);
  lim_rat(a : Approx, r : Rat, δ η : Pos, h : a.x(δ) ≈[η] rat(r)) : lim(a) ≈[δ + η] rat(r);
  lim_lim(a, b : Approx, δ η θ : Pos, h : a.x(δ) ≈[θ] b.x(η)) : lim(a) ≈[δ + η + θ] lim(b);
}
inductive Real = initial CauchyStructure;                  // stage H3
```

```
theory CwF(U < UU0) deriving (morphisms, initial) {                                      // the syntax of type theory
  Con : set U;  Ty(g : Con) : set U;  Sub(d, g : Con) : set U;
  Tm(g : Con, a : Ty(g)) : set U;
  empty : Con;  extend(g : Con, a : Ty(g)) : Con;
  // substitution, weakening, variables, Π and their laws
}
initial Syntax : CwF(U0);                                  // proposed: stage H3
computable def interpret : CwF.Hom(Syntax.model, SetModel) := Syntax.fold(SetModel);
```

**Elaboration.** `T(U)`, `T.Hom`, `T.Displayed` and the fold are generic
constructions over the theory, which the elaborator computes and the kernel
checks. In the first equational derivation strategy, `initial T` uses a
kernel signature whose constructors are `T`'s operations and laws; `fold` is its eliminator with constant motives.

**Stages.**
- H1 (one sort, no indices): `Monoid`, `Group`, `Loop`.
- H2 (indexed families): theories with one indexed sort.
- H3 (inductive-inductive): `CauchyStructure`, `CwF`.

Models and homomorphisms need no stage at all, because they are records.
The first core theory release is work-plan L2.4: named records, explicit
homomorphisms, notation, sections and extensions. Generated identity and
displayed/coherence interfaces are L2.4b and require the supported HoTT F1
fragment. `initial` and `free` additionally require the applicable H stage;
an arbitrary polymorphic operation record does not qualify for them.

**Computability.** `fold` computes on constructors, and models are records
with eta. A closed `interpret(t)` for closed syntax `t` normalizes: the
evaluator is a fold into the set model.

## 2. Cells: boundaries written the way they are drawn

Path and higher constructors, and their clauses, take any of these
equivalent spellings. Each denotes a kernel boundary system, and the
inspector draws its diagram. The block below is proposed syntax: the
`cell` face syntax is L2.8's open part, while its box notation for
compositions and `library/squares.cubist` are done.

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
  and a generated lemma relates it to the square form. **This form is not
  H1** (corrected on 2026-09-28): the specification's 1.4 (Q3) admits
  constructor expressions only in boundaries, and a live probe rejects
  `Torus2` with that diagnostic. `Torus` in the square form is admitted.
  The composite presentation needs a separately specified translation to
  the square form, with its equivalence, or a later fragment; the kernel is
  not changed to accept it. `library/squares.cubist` proves the
  conversions between a square and an equation of composites
  (`square_to_path`, `path_to_square`, 2026-10-06); a declaration with a
  composite boundary still needs its own translation.
- Clauses bind the cell's variables (`surf @ i @ j => …`). Their boundary
  obligations display the same diagram.

**Stage** H1 for cube boundaries, as the specification's 1.4 admits them;
composite equations are a later, separately specified elaboration.
**Computability:** path constructors compute on their faces by definition.

## 3. Relations and argument bundles

Relations as fields of a theory are done (L2.4c, 2026-10-06):
`le(x, y : M) : prop U notation x <= y` is a family of propositions with
its evidence. The syntax below, relations on declared types and bundles,
is proposed.

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

**Status (2026-09-28): not implemented, and not part of H1's lowering.**
The released `: set` and `: prop` always generate the squash
constructor of the specification's 1.6, named `T.squash` in clauses. The
proof-first pass is work-plan L2.3b: it needs `paths` (section 9) for the
characterization and the h-level evidence of L2.5. It is not an editorial
label on the current behaviour. It changes the admitted signature, which
then has no squash constructor, and the clauses a `match` needs, so moving
a declaration between the two forms is a migration the verifier must see,
and `set!` keeps the constructor form available.

## 5. Obligations separate from computational content

The point clauses of a `match` define a function; its path clauses prove
coherence. The two can be written apart. Explicit `obligations` were
released with H1 (L2.2b); one respect proof per argument is proposed. In
proposed syntax:

```
def neg(x : Rat) : Rat := match x {
  class(a, b) => class(-a, b);
} obligations {
  glue(a, b, c, d, cross) => glue(-a, b, -c, d, cross_neg(cross));
};

def add(x, y : Rat) : Rat := match x, y {
  class(a, b), class(c, d) => class(a * d + c * b, b * d);
} obligations by respects_each_argument {
  first(…) => …;      // one respect proof per argument,
  second(…) => …;     // not one per pair of constructors
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
indices with the scrutinee's. In proposed syntax, at stage H2:

```
def head(A : U, n : Nat, xs : Vec(A, succ(n))) : A := match xs {
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
while keeping the quotient's interface. In proposed syntax (L2.7):

```
quotient Rat = Int and Pos by (a, b) ~ (c, d) := a * d = c * b
  canonical reduce                                // lowest terms
  proving related_to_normal : forall x, x ~ reduce(x)
      and normal_respects : forall x y, x ~ y -> reduce(x) = reduce(y);
```

- **Carrier.** The subtype `exists x : Int and Pos. reduce(x) = x` of fixed
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

The library's rationals (2026-10-05, `library/rationals.cubist`) are the
plain quotient, the field of fractions of the integers. Their operations
and equality compute, but a closed rational is a class of some fraction,
not one in lowest terms, so closed results are compared with the decidable
equality rather than printed reduced. This section remains the way to
canonical forms.

## 8. Presentations: matching with another type's constructors

When two types are equivalent, one can be matched using the other's
constructors. In proposed syntax (L2.7):

```
presentation Int as Successor.initial by int_successor_equivalence;

def double(z : Int) : Int := match z using Successor {
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
checked declarations. The clause's vocabulary and fixed generated names
are globally reserved under the [reserved-name policy](../guides/keywords.md):
user declarations, fields, constructors and binders cannot claim them.
References to generated members, named arguments for their existing fields,
and ordinary proofs of their predicates remain available.

| Derivation | For | Result |
| --- | --- | --- |
| `paths` | Types without path constructors | Encode–decode characterization `x = y ≃ Code(x, y)`, with injectivity and disjointness of constructors as corollaries |
| `decidable_equality` | Types without path constructors whose arguments have decidable equality | A computable decision procedure |
| `free` | A theory explicitly requesting `morphisms` | A generic free model, fold and checked restriction/fold equivalence; initiality on `Void`; may fail (L2.6) |
| `initial` | A theory explicitly requesting `morphisms` | An initial model, fold and checked contractibility of each outgoing homomorphism type; may fail (L2.6) |
| `universal` | A supported construction with its proof obligations discharged | The universal property in section 1's corrected form: a contractible homomorphism type, the free-model property, and a maps-out characterization only where the constructor and clause data give one; its contract is specified (L2.6) before it is generated |
| `irrelevance` | Constructors with proposition-valued arguments | `lim(x, c) = lim(x, c')` without writing the proof |
| `ind_prop`, `rec` | Every declaration | Induction into propositions and non-dependent recursion, as views |

- `paths` and `decidable_equality` supply section 4's setness proofs and
  section 6's unification rules. Deriving them is what lets a data type avoid
  a squash constructor.
- Every derived declaration is an ordinary term, checked by the kernel. It is
  marked `computable` when its dependencies allow.

On theories, the [categories roadmap](categories.md) adds `isomorphisms`
and `morphisms`, and proposes `limits` and the additive/abelian tower.
The decided L2.6 clause `deriving (morphisms, free)` requests both the free
construction and its universal proof; `morphisms, initial` is weaker.
`morphisms` also generates `T.IsInitial(N) := forall B. IsContr(T.Hom(N, B))`
(schematic universes), so initiality of an existing model can be proved
without requesting its automatic construction. The initial derivation
supplies a certificate of this same predicate.
Neither capability is advertised after generating only a type and a fold.
A law's propositionhood is separate from proving it in the constructed model.

## 10. Smaller conveniences

- **Nested declarations.** A declared type may occur inside a strictly
  positive type constructor, as in `node(children : List(Tree(A)))`. The
  elaborator translates this to a mutual declaration, together with a
  generated equivalence between the auxiliary type and `List(Tree(A))`.
  That proposal exceeds H1/H2's one-sort fragment: set/prop companions need
  H3, and untruncated companions may need H4. Work-plan L4.3 first specifies
  an admissible lowering; any earlier H1 subset needs a one-sort translation
  and its own acceptance cases.
- **Sections over models.** `section {{U < UU0}}(R : CommRing(U)) { … }`
  shares the model and its notation across lemmas. This replaces milestone
  6's separate section feature. Implemented with L2.4 on 2026-10-05: a
  section's models are selected, as by `use`, in each of its definitions, as in
  `library/algebra.cubist`'s ring lemmas and `library/rationals.cubist`.
- **Theory morphisms.** `interpret Group in Monoid by …` records a translation
  between theories. Forgetful maps and free-model adjunctions are generated
  from it. This is later work.

## 11. Computation blocks: monadic do and arrows

The [computation notation roadmap](computation-notation-roadmap.md) extends
this proposal with explicitly scoped blocks. Monadic `do using M` expands
to the selected record's `bind` and `pure`; `proc using R` generalizes
sequencing to arrows through checked lifting, composition and product
operations. Branching and dynamic arrow application require explicit
additional capabilities. Monad instances supply Kleisli arrows, so these
are two forms within one design.

The first mathematical examples are closure of linear span under addition
using truncated witnesses, and substitution in free algebras through
`fold`. Probability distributions are a later instance. The roadmap states
the dependent-type boundaries, preserves elimination restrictions and
computability, and separates laws proved by paths from kernel conversion.
Its syntax and interfaces are planned, not implemented. No new kernel rule
is required; particular instances depend on H1 or H3.

## Priorities

| Tier | Features | Why first |
| --- | --- | --- |
| 1 | Theories (models, homomorphisms, identity, initial, fold); cells; relations and bundles; h-levels by proof; obligations; dependent matching without K; `paths`, `decidable_equality`, `universal` derivations | Remove the largest repetitions we measured and make the stages H1–H3 declarations readable |
| 2 | Canonical quotients; presentations; nested declarations; sections over models; monadic computation blocks | Computation and multi-presentation reasoning for numbers and algebra; shorter existence and substitution constructions |
| 3 | Theory morphisms; reflecting signatures as data; arrow blocks and their capability extensions | Later, once the generic constructions exist; broader structured composition |

Done since: models, homomorphisms and sections over models (L2.4, L2.4c),
and the first slice of initial and free models (L2.6).

## Effect on the other roadmaps

- **Ergonomics milestone 6** (records, scoped notation, sections) merges into
  theories: models are the records, notation belongs to the theory, and
  sections range over models. Algebraic normalization then targets
  `CommRing(U)` directly.
- **HoTT F1** (structure descriptions and identity) becomes the engine behind
  `T.equality`. **F2**'s transfer uses presentations and generated
  equivalences.
- **The rebuild** can state its algebra as theories from the start: monoids,
  groups, rings, fields, vector spaces and ordered fields. Its numbers can use
  canonical quotients for the rationals, and its reals the initial model of
  `CauchyStructure`. Since 2026-10-05 the library states monoids to fields
  as theories; its rationals are the plain quotient for now (section 7).

## Open questions

1. **Universe levels of generated records.** A model of a theory with a sort
   in `U` lives in `next(U)`. With G0 this is automatic, but it should be
   visible in signatures.
2. **Coherence for untruncated theories.** For theories like `Loop`, `T.Hom`
   needs cells up to the laws' dimension. Beyond two dimensions the generated
   fields grow quickly. Specify the supported homomorphism spaces and
   universal proofs before offering `initial` or `free`; a recursor alone
   does not establish either capability.
3. **Choice of initial-model presentation.** A theory law can be stated as an
   equation between composites or as a square; the two give equivalent but
   different signatures. The first form written is the one used, and the
   other is related by a generated lemma. Confirm this is what users expect.
4. **Canonical quotients over non-sets.** Rejected. Their fixed-point
   carrier would not be a proposition-valued subtype.
