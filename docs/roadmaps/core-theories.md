# Core theories (L2.4)

Status: design, 2026-10-05; all four slices implemented the same day
(`web/cubist/theories.mjs`, `web/cubist/morphisms.mjs`,
`web/translator/theories.mjs`; evidence `cubist-tests/theories.cubist`,
`cubist-tests/theory_morphisms.cubist`, `cubist-tests/theory_sections.cubist`,
`tests/theories.test.mjs`, the reference's
[theories and models](../../web/reference/theories.html)). A definition in
a section has no implicit parameters of its own: the section's come first. Two additions the slices needed: `e.f` reads a field of
any value whose type is a theory's record, not only of a name, as
`T.Iso.inverse(f).to.map(x)`; and argument inference matches one
definition applied on both sides, `T.Hom(A, B)` against `T.Hom(M, N)`,
argument by argument before unfolding it, so a homomorphism's models are
implicit in its operations. This document fixes the contract of work-plan
L2.4: theory declarations, their models, scoped notation, sections,
extension, homomorphisms and isomorphisms. It follows
section 1 of the [language features proposal](inductive-language-features.md)
and milestone 6 of the [ergonomics roadmap](proof-ergonomics-roadmap.md),
and narrows both to what L2.4 delivers.

Everything here is elaboration: a theory expands to ordinary definitions,
which the kernel checks like any other. No kernel rule changes.

A revision of the syntax, with theory families and the combination of
independent theories, was decided on 2026-10-05: [L2.4c](#revision-l24c).
Its first slice, carriers as fields, the universe in the header and the
theory's name as the type of its models, is implemented (2026-10-06); the
rest is not. The sections after it describe the implemented grammar.

## Revision (L2.4c)

Decided on 2026-10-05. Each slice migrates in two commits, as the
retirement of `cases` did: the new forms beside the old, every source
moved and checked while the old still parse, then the old forms refused.

**First slice, done on 2026-10-06:** carriers as fields, `M : set U;`,
`P : prop U;` and `M : U;`; one universe named in the header,
`theory T(U < UU0)`; and the theory's name as the type of its models,
`Monoid(U0)`. `sort` is refused (E180) and so is `T.Model` (E396). Every
theory in `library/`, `cubist-tests/` and the reference moved while the
old forms parsed, and the verifier found the library's terms identical
(243, 44 and 59 declarations of `algebra`, `integers` and `rationals`). A
source of an earlier revision is read in the new forms
(`web/cubist/legacy-syntax.mjs`).

**Second slice, done on 2026-10-06:** the header binds several universes,
`theory Arrow(U, V < UU0)`, each carrier in one of them, and parameters,
`theory Pointed(U < UU0, G : Magma(U))`. The type of models takes them in
order, `make` takes the parameters first, and the projections read them
from the model's type. A homomorphism of a theory with parameters relates
two models with the same parameters and universes; without parameters,
each model has its own universes. A child takes its parents' parameters by
name, with the same types (E821), and their universes: the one universe of
each, or each by its name when there are several (E820). Evidence:
`cubist-tests/theory_headers.cubist` and the reference's
[header](../../web/reference/theories.html#header) section.

**Third slice, done on 2026-10-06:** homomorphisms by
[variance](../../web/reference/theories.html#morphisms), replacing E817's rule that every input and result be
a carrier. An input with no carrier, as `n : Nat` or a parameter's
`g : G.M`, is the same value on both sides; a covariant input, with
carriers right of every arrow, is pushed forward; a contravariant one is
pulled back; and a result is pushed forward. Pushing and pulling follow
arrows, non-dependent `forall` and pairs, so identity and composition are
generated and compute. An input mixed in a carrier, a contravariant
result, a dependent argument or another form mentioning a carrier leaves
the theory without homomorphisms, E817 saying which. The library's
generated terms are unchanged (the verifier: identical). Evidence:
`cubist-tests/theory_variance.cubist` and the reference's
[homomorphisms](../../web/reference/theories.html#morphisms) section.

**Fourth slice, done on 2026-10-06:** [theory families](#theory-families).
A carrier with indices, `F(A : set U) : set U`, where an index
`(A : set U)` holds `A` and its evidence; inside the theory `F(A)` passes
the evidence along (E823 when the index is not bound as one), and outside
it is written, `m.F(Nat, nat_is_set)` (open question 5's interim answer).
A relation is a family of propositions indexed by carriers, with a
notation (E824 for its form). Laws over a family's members are
propositions when the family is a set or a proposition. An operation's
argument may name an earlier argument that is the same on both sides or
pushed. A homomorphism maps each family at each index, pushing an index
that is an element of a carrier, so the homomorphisms of preorders are
the monotone maps; an isomorphism has round trips on each family of sets
at each index, none on a family of propositions, and a family of sets
indexed by a carrier leaves the theory without isomorphisms (E825). The
identity monad is a `Monad`, and its homomorphisms and isomorphisms
compute. Evidence: `cubist-tests/theory_families.cubist` and the
reference's [families](../../web/reference/theories.html#families)
section.

**Fifth slice, done on 2026-10-06:** [combining independent
theories](#combining-independent-theories). Carriers two parents give
under one name, kind and type merge; carriers of one name and different
kinds or indices (E828), or a name that is a carrier in one parent and not
in another (E827), are refused. Another field of one name from two
parents stays each parent's, named `label_name` in the child, and the
name is ambiguous: refused where it is used, in the theory (E830), on a
model (E832) and under `use`, with the qualified forms. An operator two
parents bind to two fields is ambiguous the same way (E831), and a
child's own notation for it is refused (E826). Inside the theory,
`label.f` names the field that parent gave as `f` (E829). Renaming in
`extends` still gives a name or notation of its own. Evidence:
`cubist-tests/theory_independent.cubist` and the reference's
[extension](../../web/reference/theories.html#extends) section.

**Sixth slice, done on 2026-10-06:** [qualified operators](#qualified-operators)
and `use`. `use m;` puts a model's fields and notation in scope for the
rest of a block, or of the file at its top level, a later `use` switching
it; `m.(e)` does so for one expression; `a m.(*) b` qualifies one
operator, with its usual precedence, and `m.(*)` alone is the operation.
A parent's operator is reached through its label, `x R.additive.(*) y` on
a model, `magma.(x * x)` and `x magma.(*) y` inside a theory. `open m;`,
its earlier spelling, migrates in two commits (E834 for a `use` of no
model; E835, E836 for a qualifier that is no model or an operator its
theory does not bind); `open` is then refused with a message naming
`use`, and an earlier revision's `open m;` is read as `use m;`. The unary
form `G.(-) x` waits for arithmetic `-` (L2.10b), and the file-level
shadowing warning for L2.10a's named notations. Evidence: `cubist-tests/theory_use.cubist` and the reference's
[selecting a model](../../web/reference/theories.html#open) section.
L2.4c is then complete; its open questions remain as recorded.

### Carriers are fields with an h-level

`sort` goes. A carrier is a field whose type is a universe, optionally with
an h-level, spelled as an inductive declaration's header spells its result
(`inductive Trunc(U < UU0, A : U) : prop U`):

```
theory Monoid(U < UU0) {
  M : set U;
  mul(x, y : M) : M notation x * y;
  law mul_assoc(x, y, z : M) : (x * y) * z = x * (y * z);
  one : M;
  law one_mul(x : M) : one * x = x;
  law mul_one(x : M) : x * one = x;
}
```

| Field | What the model holds |
| --- | --- |
| `M : set U;` | `M : U` and `M_is_set : IsSet(U, M)`, as `sort M : set;` does today |
| `P : prop U;` | `P : U` and `P_is_prop : IsProp(U, P)` |
| `M : U;` | `M : U` alone: a carrier with no h-level |

`set U` is a field's form, as it is a header's, not a type former. The
generators find a theory's carriers by their type, not by a keyword. A
carrier with no h-level has models at once: `theory Loop(U < UU0) { M : U;
base : M; loop : base = base; }` has the circle as a model. A path such
as `loop` is an operation, data, and the law check still refuses an
equation between its elements as a law, since it is not a proposition.
Its homomorphisms need a coherence field for each path-valued operation,
the image of `A.loop` against `B.loop` along `map_base`, and composition
needs generated path algebra; until those are specified such a theory has
no `T.Hom`, as with E817 today. The initial model of `Loop`, the circle
with its recursion as `fold`, is L2.6.

### The header names universes and parameters

`theory Monoid(U < UU0)` binds the universe of the theory's carriers, so a
field or a law can name it, as L2.10k's `Trunc(U, …)` needs. A theory may
bind several, `theory Pair(U, V < UU0)`, for carriers in different
universes. Whether the header binder is required, or optional with
`M : set` meaning the model's unnamed universe, is open.

The header may also bind parameters, which every model shares and no
homomorphism changes:

```
theory Module(U < UU0, R : CommRing(U)) {
  V : set U;
  smul(r : R.R, v : V) : V;
  …
}
```

A carrier varies under a homomorphism; a parameter is fixed. `R.R`
mentions no carrier of `Module`, so `smul`'s `r` passes through unchanged:
`Module.Hom` has only `map_V`, and its maps are linear over `R`, not maps
that may also change the ring. `Module(U0, integers)` is the type of
modules over the integers. Had the ring been carriers of the theory, a
homomorphism would map them too.

### A theory's name is the type of its models

`G : Monoid(U0)`, not `G : Monoid.Model(U0)`: `Monoid.Model` is retired.
`Monoid.make`, `Monoid.Hom`, `Monoid.Iso` and the projections stay beside
it, as `Trunc` and `Trunc.squash` do. Models do not lift along universe
cumulativity: `CommMonoid(U0)` is not a `CommMonoid(U1)` today
(a type mismatch, though its carrier lifts), and a generated lift is later
work if a use needs it.

### Theory families

A carrier may be a family, indexed by any type, a carrier included, and an
index may carry an h-level, as a carrier does:

```
theory Monad(U < UU0) {
  F(A : set U) : set U;
  pure(A : set U, a : A) : F(A);
  bind(A, B : set U, m : F(A), k : A -> F(B)) : F(B);
  law left_unit(A, B : set U, a : A, k : A -> F(B)) : bind(A, B, pure(A, a), k) = k(a);
  law right_unit(A : set U, m : F(A)) : bind(A, A, m, fun (a : A) => pure(A, a)) = m;
}

theory Graded(U < UU0) {
  V(n : Nat) : set U;
  mul(m, n : Nat, x : V(m), y : V(n)) : V(m + n);
}

theory Preorder(U < UU0) {
  M : set U;
  le(x, y : M) : prop U notation x <= y;
  law le_refl(x : M) : x <= x;
  law le_trans(x, y, z : M) : x <= y -> y <= z -> x <= z;
}
```

- `Monad` is a monad on sets. An index `A : set U` holds `A : U` and
  `A_is_set : IsSet(U, A)`, as a field `M : set U` does, so
  `F(A : set U) : set U` holds `F(A : U, A_is_set : IsSet(U, A)) : U` and
  `F_is_set(A : U, A_is_set : IsSet(U, A)) : IsSet(U, F(A, A_is_set))`,
  and `pure`, `bind` and the laws take each index with its evidence. The
  identity monad is a model: `F(A) := A`, whose setness is `A_is_set`.
  Indexed by every type, `F(A : U) : set U`, it would not be: its
  `F_is_set` would prove every type in `U` a set, and the circle is not
  one. `Maybe`, `List` and truncation take sets to sets, so those monads
  are models too. A monad on all of `U` with untruncated values is not a
  theory: its laws would be data, needing coherence (open question 4).
- An equation between elements of `F(A)` is a proposition, so the monad
  laws pass the law check, which refuses them today. Computation
  notation's N1 uses this theory, monads on sets.
- At a use, `G.F(Nat)`, the index's evidence is an argument; whether the
  author writes it or the h-level solver supplies it is open (question 5).
- A homomorphism maps each index: `map_F(A : set U) : M.F(A) -> N.F(A)`,
  and preserves each operation at each index. It has no naturality field:
  the signature has no action on maps to be natural for, and a monad's
  naturality follows from preserving `pure` and `bind`.
- Indices match definitionally, as all types do: no generator inserts a
  transport. An index equal only by a proof, as `m + n` and `n + m` are,
  needs the transport written where it is used.
- **A relation is a family of propositions indexed by carriers.** `le(x, y
  : M) : prop U` holds `le` and its evidence; `x <= x` is an element of a
  proposition family, which the law check accepts, as it accepts an element
  of a proposition carrier. Today a relation cannot be stated: `le(x, y :
  M) : U0` with the law `x <= x` is refused (E818). A family indexed by a
  carrier is mapped along that carrier's map: `Preorder.Hom` has
  `map_le(x, y : A.M) : A.le(x, y) -> B.le(map_M(x), map_M(y))`, so its
  homomorphisms are exactly the monotone maps, with nothing to write. The
  ordered rings and fields of the numbers' order (work-plan first actions)
  are theories of this kind.
- An isomorphism has round trips on each set carrier and, on a set family
  indexed by no carrier, at each index:
  `from_to_F(A : set U, x : M.F(A)) : from.map_F(A)(to.map_F(A)(x)) = x`.
  On a proposition carrier or family they hold of themselves, so none is
  generated: an isomorphism of preorders is a bijection monotone both
  ways.
- A set family indexed by a carrier, `F(x : M) : set U`, gets a `T.Hom`
  and no `T.Iso` for now. Its round trip sends `y : A.F(x)` to
  `from.map_F(to.map_M(x))(to.map_F(x)(y))`, which lies in
  `A.F(from.map_M(to.map_M(x)))`, not `A.F(x)`, so it can equal `y` only
  after a transport along the carrier's round trip. Without that field,
  maps that are not inverse on the fibers would pass: over `M = Unit` with
  `F(tt) = Nat`, identity on the carrier and zero on the fibers both ways.
  The transported field is open question 6.

**Variance.** Checking needs none: there is no subtyping beyond universe
cumulativity, and types match by conversion. Generating homomorphisms does.
A homomorphism's preservation field relates an operation's inputs in `A` to
its inputs in `B`, and how depends on where the carriers sit in each
input's type:

| Input | Example | Preservation |
| --- | --- | --- |
| No carrier | `n : Nat`, `r : R.R` for a parameter `R` | the same value on both sides |
| Covariant: carriers right of every arrow | `x : M`, `k : A -> F(B)` | push the `A`-input forward: `map(x)`, `fun a => map_F(B)(k(a))` |
| Contravariant: carriers left of an arrow | `f : X -> Real`, as in `integrate(f : X -> Real) : Real` | pull the `B`-input back: for every `f : B.X -> Real`, `A.integrate(fun (x : A.X) => f(map_X(x))) = B.integrate(f)`, which says the map preserves measure |
| Mixed: both | `g : M -> M`, as in `iterate(g : M -> M, x : M) : M` | none generated |

Pushed and pulled inputs compose: a homomorphism after a homomorphism
pushes forward, or pulls back, along both maps in turn, so identity and
composition are generated as now. A mixed input relates `g_A` and `g_B`
only by a hypothesis, `map ∘ g_A = g_B ∘ map`, and two such
homomorphisms do not compose in general: there need be no input in the
middle model related to both. A theory with a mixed input gets no
`T.Hom`, as with E817 today: no homomorphisms are generated that cannot
compose (decided on 2026-10-05). Its isomorphisms, which carry any input
across with `to` and `from`, can be generated later. This replaces
E817's rule, which admits only inputs and results that are carriers and
so refuses `power(x : M, n : Nat) : M`, whose `n` passes unchanged.

A valuation is covariant in this sense: `v(x : K) : Gamma` takes a carrier
and returns a value. With `Gamma` a parameter, a homomorphism preserves the
valuation, `B.v(map(x)) = A.v(x)`, as an extension of valued fields
restricts; with `Gamma` a carrier, the value groups' map appears,
`B.v(map_K(x)) = map_Gamma(A.v(x))`. Maps that only bound the valuation,
as `|f(x)| <= |x|`, are another kind of morphism, with an inequality for an
equation; a theory's generated `Hom` is the strict kind, and others are
ordinary definitions.

### Combining independent theories

Two developers write theories without knowing of each other; a third
declares a theory that is both, changing neither:

```
theory Magma(U < UU0) {
  M : set U;
  mul(x, y : M) : M notation x * y;
}

theory Action(U < UU0) {
  M : set U;
  act(x, y : M) : M notation x * y;
  law act_idem(x : M) : x * x = x;
}

theory Both(U < UU0) extends Magma, Action {
  law mixed(x : M) : magma.(x * x) = action.(x * x);
}
```

Today `Both` cannot be declared: its parents' carriers clash by name, and
renaming both to one name is refused too, since carriers merge only when
they are copies of one ancestor (as `Semiring`'s two monoids are). The
revision:

- **Carriers merge by name.** A carrier two parents give under one name,
  of one kind (`set` or `prop`) and with the same indices, is one carrier
  of the child, wherever the parents come from: a theory that is both is
  both on one set. To keep them apart, the child renames one,
  `Action(M := N)`. Carriers of one name and different kinds are refused.
- **Everything else stays the parents'.** An operation, a constant or a
  law from two unrelated parents under one name is two fields. A clash is
  not an error when the child is declared: the unqualified name, or the
  operator, is ambiguous in the child and refused where it is used, with
  the qualified forms in the message. Each stays reachable through its
  parent's label: `B.magma.mul`, `x B.magma.(*) y`, and inside the
  theory `magma.(x * x)`. A child that wants an unqualified name or
  operator gives one by renaming in its `extends` clause,
  `Action(act := act notation x + y)`, as it can today; it is never
  required to.
- **One ancestor is still shared.** A field that two parents reach from
  one ancestor, with one name and one type, is one field (`AbelianGroup`
  through `Group` and `CommMonoid`), and its notation one binding.
- **Within one theory, a clash stays an error** (E804, E803): its author
  controls both fields.
- Generated names stay unique: a homomorphism's fields for ambiguous
  operations are named by label, `map_magma_mul`.

The present fixture, `SharedOperator` in `cubist-tests/theories.cubist`,
covers only a clash inside one theory. The revision's acceptance adds the
cross-parent cases: `Both` above, used through both labels; a child that
renames one notation; an ancestor reached twice; and carriers of one name
and different kinds, refused.

### Qualified operators

`a G.(+) b` applies `G`'s binding of `+` to `a` and `b`, with `+`'s
precedence and associativity, so `a G.(+) b G.(+) c` is
`(a G.(+) b) G.(+) c`. `G.(-) x` is the unary form, and `G.(+)` alone is
the operation as a function, as an argument to a fold. Parentheses that
hold a lone operator are this form; anything else in them is `G.(e)`. A
parent's operator is reached through its label, `x R.additive.(*) y`.
Only the operator is qualified: `a` and `b` are read where they stand,
not in `G`. Whether they should be read in `G`'s notation instead, as in
`G.(a + b)`, is open. The notation roadmap lists every way to reach another
notation under a selection, and how a later `use` switches it
([switching](notation.md#switching-and-reaching-another-notation)); `use`
replaced `open` (its decision 7).

### Acceptance

- The migration: every theory in `library/`, `cubist-tests/` and the
  reference moved to the new forms and checked while `sort` and
  `T.Model` still parse, then refused.
- Several carriers: a set acting on a set, with `map_S` and `map_X`, round
  trips on both, and composition computing. No fixture covers more than one
  carrier today.
- A parameter: `Module(U0, integers)`, whose homomorphisms have only
  `map_V`.
- Families: the identity monad as a `Monad` on sets; `Graded`; `Preorder`,
  whose homomorphisms are monotone, with isomorphisms that have no round
  trips on `le`, and the law check accepting `x <= x`; a set family
  indexed by a carrier, with a `T.Hom` and no `T.Iso`.
- Variance: an input with no carrier (`power(x : M, n : Nat)` gets its
  `Hom`); a covariant input (`bind`); a contravariant input, pulled back,
  with identity and composition; a mixed input, refused with a message
  naming it.
- Independent parents: the cases listed under
  [combining independent theories](#combining-independent-theories).
- Qualified operators and `use`, with the notation roadmap's cases.

### Open questions

1. Whether `theory T(U < UU0)` is required, or optional with `M : set`
   meaning the model's universe.
2. How a qualified operator's operands are read (above).
3. Whether a child can drop a parent's notation without giving it another.
4. Homomorphisms of theories with carriers of no h-level: the coherence
   fields of path-valued operations, and how far up to generate them.
5. How a family's index evidence is given at a use, as `Nat`'s setness in
   `G.F(Nat)`: written by the author, or supplied by the h-level solver.
   Two proofs of it are equal but not definitionally, so `G.F(Nat)` under
   two proofs is two types, which meet only through a transport.
6. The round trip of a set family indexed by a carrier, after a transport
   along the carrier's round trip, and with it that theory's `T.Iso`.

## Scope

L2.4 delivers, in slices:

1. **Notation packs and `open`.** A model's operations bound to operators and
   names for the rest of a block. `open m;` is now `use m;` (L2.4c).
2. **`theory`, `T.Model` and `extends`.** Declarations of sorts that are sets
   or propositions, constants, operations with notation, and laws; the record
   type of models, its constructor and its fields; single and multiple
   extension, with renaming.
3. **`section`.** Shared parameters for a group of declarations, opened for
   their statements and proofs.
4. **`T.Hom` and `T.Iso`.** Homomorphisms and isomorphisms, with identity and
   composition, and the inverse of an isomorphism.

Not in L2.4: generated structure identity, `T.equality : (M = N) ≃
T.Iso(M, N)`, and displayed models (L2.4b, through HoTT F1); sorts that are
not sets or propositions, whose homomorphisms need coherence fields; relation
fields; `initial T` and `free T on A` (L2.6, whose contract is specified
[below](#initial-and-free-models-l26)); numerals interpreted in a model; type-directed overloading and
instance search. Structure scope stays explicit: an operator means one thing
in a scope, chosen by `use` or `section`, never by the types of its operands.
The [notation roadmap](notation.md), L2.10, adopts explicit model notation
views as the next direction: an expression or block selects its model before
its operators and literals are elaborated. `v.(expression)` and `use v;`
are its decided spellings; its remaining grammar and elaboration gates are
draft. Existing `use` and section semantics remain compatible
during that migration; type-based automation is optional later work, requiring
evidence that it preserves the explicit semantics.

## Theories

```
theory Semigroup(U < UU0) {
  M : set U;
  mul(x, y : M) : M notation x * y;
  law mul_assoc(x, y, z : M) : (x * y) * z = x * (y * z);
}

theory Monoid(U < UU0) extends Semigroup {
  one : M;
  law one_mul(x : M) : one * x = x;
  law mul_one(x : M) : x * one = x;
}

theory Group(U < UU0) extends Monoid {
  inv(x : M) : M;
  law inv_mul(x : M) : inv(x) * x = one;
}
```

The header names the universe of the carriers, which a field may mention.
A theory's body lists, in order:

- **carriers** (sorts), `M : set U;` or `P : prop U;`: a type in the
  model's universe, with the evidence of its h-level as a field
  (`M_is_set`, `P_is_prop`); or `M : U;`, with no h-level, whose equations
  are not propositions and whose models have no homomorphisms (until
  L2.4c's slice of 2026-10-06, `sort M : set;`);
- **constants**, `one : M;`, and **operations**, `mul(x, y : M) : M`, whose
  argument and result types are sorts of the theory, each with an optional
  `notation`;
- **laws**, `law name(binders) : statement;`, propositions about the earlier
  fields. A statement must be evidently a proposition: an equation between
  elements of a sort (the sorts are sets or propositions), `Void` or `Unit`,
  an element of a proposition sort, or `forall`, `->` into one, or `and` of
  two. Anything else, such as `law point : M;` or an `exists`, is refused,
  since homomorphisms ignore laws. `Unit` and `Void` are reserved names, so
  no declaration can stand in for them here.

Inside the body the theory's own notation, and its parents', is in scope, and
each field is in scope by its name from its declaration on.

A notation is one of the binary operators the grammar already has, `x + y`
or `x * y`, or a relation, `x < y` or `x <= y`. Unary minus is refused
until it becomes arithmetic, and `~` inverts a path, so negation and
inverses are named operations.

This is the implemented L2.4 grammar. L2.10's proposed operators and literals
are separate work. Reversal moved to `~` first (L2.10i, 2026-10-06),
keeping the groupings `-p @ i` and `p @ -i & j` had, so that `-` can
become arithmetic.

## Models

A theory `T` declares, in its module:

- `T(U < UU0) : next(U)`, the type of models whose sorts are in `U`: a
  Σ record of the fields in order, with the kernel's pair eta (`T.Model`
  until L2.4c);
- `T.make{{U < UU0}}(…)`, its constructor, one parameter per field, so that
  named arguments build a model field by field;
- for each field `f`, `T.f{{U < UU0}}(m : T(U))`, its projection, typed
  through the earlier projections, so that `T.one(m) : T.M(m)`.

`m.f` is `T.f(m)` wherever `m`'s type is a theory's record, and `T.f` is
otherwise a qualified name, as `Trunc.squash` is. Goals and messages show
`m.f` for a projection.

```
import nat, hlevels;

def additive : Monoid(U0) := Monoid.make(M := Nat, M_is_set := nat_is_set,
  mul := add, mul_assoc := nat_add_assoc, one := 0, one_mul := nat_zero_add,
  mul_one := nat_add_zero);
```

## Notation and `use`

`use m;` selects the model `m`: in a proof block for the rest of the block,
and at a file's top level for the definitions and directives after it. Each
field of `m` is in scope by its name, as the projection `m.f`, and each
notation of `m`'s theory means `m`'s operation:

```
def square(G : Group(U0), x : G.M) : G.M {
  use G;
  exact x * x;
}
```

A name or operator that `use` binds shadows the one it had, as `let` does,
until the block ends; a later `use` of another model shadows an earlier
one. `m.(e)` selects `m` for one expression, and `x m.(*) y` qualifies one
operator. Until L2.4c this statement was `open m;`, which is now refused
with a message naming `use`; an earlier revision's `open m;` is read as
`use m;`. An operator means only what a view, a `use` or a section binds,
and a section or `use` selects its model's view, innermost first: L2.10j
retired the fallback to `add` and `mul` in scope, and every selection is
complete.

L2.10 extends this explicit selection to expression views, including theorem
statements, with operand views determining numeral interpretations and a
printer that retains the model whenever omitting it would change meaning.
It does not change the behavior of existing `use` statements or sections
as an incidental part of introducing that syntax.

## Sections

```
section {{U < UU0}}(G : Group(U)) {
  def square(x : G.M) : G.M := x * x;
  def square_one : square(one) = one { … }
}
```

A section's parameters, in braces or not, are the first parameters of every
declaration in it, as written: the rule takes all of them, so it does not
depend on what a declaration uses. A parameter whose type is a model is
opened for each declaration's statement and proof. Inside the section a
declaration of the section is applied to the section's parameters already,
so `square(one)` there is `square{{U}}(G, one)` outside. A recursive call
passes them unchanged too: in `power(x, n)`, `power(x, k)` is
`power{{U}}(G, x, k)`. Sections do not nest in L2.4.

## Extension

`extends` takes the parents' fields, in order, before the theory's own. A
theory may extend several parents. An ancestor that two parents reach
contributes its fields once when it arrives with the same fields under the
same names: `CommGroup extends Group, CommMonoid` has one `Monoid`, and
`Group`'s `inv` with `CommMonoid`'s `mul_comm`.
An ancestor that arrives renamed is another copy: below, the additive and
the multiplicative structure each have their own `Monoid`, with `add` and
`mul`, on the one sort `R`.

A parent can be renamed and labelled:

```
theory AbelianGroup extends Group {
  law mul_comm(x, y : M) : x * y = y * x;
}

theory CommMonoid extends Monoid {
  law mul_comm(x, y : M) : x * y = y * x;
}

theory CommRing extends
    additive_ : AbelianGroup(M := R, mul := add notation x + y, one := zero, inv := neg,
      mul_assoc := add_assoc, one_mul := zero_add, mul_one := add_zero, inv_mul := neg_add,
      mul_comm := add_comm),
    multiplicative : CommMonoid(M := R) {
  law mul_add(x, y, z : R) : x * (y + z) = x * y + x * z;
}
```

A renaming gives a parent's field a name in the child, and an operation a
notation in place of its own; renaming a sort to one name in two parents, as
`M := R` above, makes it one sort of the child. Two fields of one name from
different parents are refused unless they are one ancestor's field shared
as above; the error names both and asks for a renaming. A child model has
each parent's model: `T.p(m) : P(U)` for a parent `P` labelled `p`, and
`m.p` writes it. An unlabelled parent's label is its name in snake case,
`G.monoid` for `Group extends Monoid`.

## Homomorphisms and isomorphisms

For a theory whose sorts are sets or propositions and whose operations take
and return sorts:

- `T.Hom{{U, V < UU0}}(A : T(U), B : T(V)) : max(U, V)` has a map
  for each sort, `map_M : A.M -> B.M` (`map` when there is one sort), and
  for each constant and operation a field that the map preserves it:
  `map_one : map(A.one) = B.one`, `map_mul(x, y : A.M) : map(x * y) =
  map(x) * map(y)`, with `A`'s operation on the left and `B`'s on the right.
  Laws need no field: they are propositions about sets.
- `T.Hom.id(A) : T.Hom(A, A)` and `T.Hom.compose(g, f) : T.Hom(A, C)` for
  `f : T.Hom(A, B)` and `g : T.Hom(B, C)`.
- `T.Iso(A, B)` has a homomorphism each way, `to` and `from`, and for each
  sort that they are inverse: `from_to(x : A.M) : from.map(to.map(x)) = x` and
  `to_from(y : B.M) : to.map(from.map(y)) = y`.
- `T.Iso.id(A)`, `T.Iso.compose(g, f)` and `T.Iso.inverse(f)`.

All of them are generated definitions, checked by the kernel, and computable:
closed homomorphisms apply and compose by evaluation. A child theory's
homomorphisms preserve its parents' operations too, and `T.Hom` has the
forgetful map to each parent's homomorphisms, `f.p`.

**Proposed morphism opt-in, L2.4d (2026-10-07).** The
[categories roadmap](categories.md) separates `deriving (isomorphisms)` by
transport from `deriving (morphisms)`, which generates `T.Hom` and its default
category and implies isomorphisms. Unsupported opt-ins fail at the theory.
The decided [L2.6 contract](#initial-and-free-models-l26) additionally
requires `deriving (morphisms, free)`, or the weaker `morphisms, initial`,
for initial/free instances. These capabilities include their universal
proofs and can fail; ordinary recursion alone is not an initial capability.

## Elaboration

The [reserved-name policy](../guides/keywords.md) applies to these generated
interfaces and to the planned deriving vocabulary: fixed generated names
cannot be used as user fields or binders. Generated members remain callable,
and dynamically formed names still require collision checks before publication.

A theory expands, before checking, into the definitions above, in the
module that declares it, in order: the record and its constructor, the
projections, each parent's model, then `Hom` and `Iso` with their
operations. The expansion is source the translator elaborates like a
user's own, so every generated definition is inspectable by name. The
module needs `hlevels` for the sorts' evidence, and the elaborator says so
when it is missing.

`use` and sections bind names and operators lexically, recorded in the
inspector with the projection each stands for. The operator elaboration
reads an operator's binding before its fallback, the `add` or `mul` in
scope.

## Initial and free models (L2.6)

**Revised on 2026-10-07, at the maintainer's request.** Initial and free
objects are checked capabilities requested on a theory. This replaces the
2026-10-06 contract's automatic construction for a fixed signature fragment
and its recursion-only use of `initial`. The opt-in and full proof interface
below are specified, not implemented. Declaration and fold prototypes alone
do not establish the capability.

### Opt-in and meaning

The proposed clause is shared with [morphism derivation](categories.md):

```text
theory T(...) deriving (morphisms, free) { ... }
```

`morphisms` selects the theory's homomorphisms. `free` requests a construction
and a checked universal property relative to those morphisms and the chosen
forgetful functor. Initially that functor takes a model to its single carrier
and a homomorphism to its carrier map. Changing the morphisms or the forgetful
functor changes the obligation; a construction for another category cannot
be reused without a proof. Several carriers and other forgetful functors
need a later explicit interface.

- **`deriving (morphisms, free)`** requests a free model for every generator
  type in the declared universe range, its generator map, fold, computation,
  and universal-property proof. It also supplies the initial model by taking
  the generator type to be `Void`.
- **`deriving (morphisms, initial)`** requests only an initial model and its
  universal property. This is a weaker capability: an initial object alone
  gives no free construction on arbitrary generators.
- `free` and `initial` require an explicit `morphisms` opt-in. Neither
  `isomorphisms` alone nor the existence of a model meets that requirement.
- Theory parameters remain fixed. Derivation must work uniformly under the
  header's assumptions and for the promised universes. A proof for one
  parameter value does not establish the generic capability.

After successful derivation, these declarations name instances of the
registered construction; they do not independently derive it:

```text
initial N : Monoid(U0);
free W(A : U0) : Monoid(U0) on A;
```

Here `Monoid` must request `deriving (morphisms, free)`, or, for the first
line alone, `deriving (morphisms, initial)`. `free` without the capability
fails at its use; `initial` accepts either capability. Fixed generated names are globally reserved, including `model`, `fold`,
`fold_map`, `fold_unique`, `universal`, `squash` and `gen`: no user field,
constructor, declaration or binder may claim them, whether or not that
particular theory requests a derivation. The same policy covers the deriving
vocabulary and the categorical interfaces in the
[reserved-name policy](../guides/keywords.md). Generated members remain
callable and their labels remain usable in calls. All dynamically formed
names are still checked for collisions before publishing declarations.

### The initiality predicate

`deriving (morphisms)` also supplies `T.IsInitial`, independently of any
request to construct an initial or free object. For fixed universes and
theory parameters, its definition is, schematically:

```text
T.IsInitial(N : T(...)) :=
  forall B : T(...). IsContr(T.Hom(N, B))
```

It takes a model with its operations and laws. `CommRing.IsInitial(integers)`
is therefore the type of a theorem about the existing integer ring model.
`IsContr`'s universe argument is suppressed here. The predicate is an
ordinary generated definition checked by the kernel, not a new trusted
primitive, and remains available when `initial` or `free` derivation is
unsupported. A proof's component at `B` contains the unique homomorphism
and its uniqueness proof.

Once L3.5 supplies the category library's generic `IsInitial(C, N)`, the
theory-specific predicate is its specialization at `T.cat`. The direct
homomorphism-type definition allows the language interface to precede that
library. `IsInitial`, `IsTerminal`, `IsLimit` and `IsColimit` are reserved interface
names, supplied through ordinary checked definitions. User declarations and
fields cannot replace them. Reserving the names does not add a trusted proof
rule or implement an otherwise unsupported construction.

### What successful derivation proves

For a fixed target model `B`, with carrier `B.M`, the results are separate
typed statements. The following uses mathematical notation; universe
arguments to `IsContr` and `ContrEquiv` are suppressed.

| Capability | Checked result |
| --- | --- |
| Initial | `N.model : T(...)`, `N.fold(B) : T.Hom(N.model, B)`, and `N.universal : T.IsInitial(N.model)` |
| Free on `A` | `W.model : T(...)`, `W.gen : A -> W`, and `W.fold(B, g) : T.Hom(W.model, B)` for each `g : A -> B.M` |
| Free universal property | `W.universal(B) : ContrEquiv(T.Hom(W.model, B), A -> B.M)`, whose forward map restricts to generators and whose inverse is `fold` |

Applying `N.universal` to `B` gives
`IsContr(T.Hom(N.model, B))`, whose center is `N.fold(B)`. A hand-written
initiality theorem and the automatic certificate have the same public type.

The carrier projection above is schematic: the generator reads its actual
name from the theory, not a required field name `M`. The equivalence is for
the stated restriction map, rather than an arbitrary equivalence of the two
types. It includes both inverse laws. Initiality from `free` uses the
contractibility of `Void -> B.M` and this equivalence.

The first strategy's folds compute on point constructors by conversion:
fixed arguments pass unchanged, recursive carrier arguments are folded,
and `W.fold(B, g).map(W.gen(a))` is `g(a)`. The generated
`N.fold_unique(B, f)` proves pointwise equality with `N.fold(B).map`.
For `free`, `W.fold_unique` additionally takes agreement with `g` on every
generator. `T.Hom.ext` then promotes pointwise agreement to equality of
homomorphisms: for this strategy the remaining fields are propositions.
These checked proofs, not just the recursive function, complete derivation.
A later strategy must state which computation rules are by conversion and
which have propositional proofs.

### Construction strategies and laws

A theory declaration may contain every law admitted by the theory language.
[L2.11](categories.md#decisions) broadens that check to anything the `hlevel`
solver proves a proposition. That establishes proof irrelevance of the law,
not that the law holds in a proposed model. Valid theories need not admit
initial or free objects.

The first automatic strategy is the existing H1 construction for a
single-carrier equational presentation:

1. The carrier is a set or proposition. Each operation input is the carrier
   or a fixed type independent of it; the result is the carrier. The stored
   data, including generators, must fit the declared carrier universe.
2. Replace carrier occurrences in operations by the new declared type.
   Each operation becomes a constructor; `free` adds `gen(a : A)`.
3. Each equation between operation terms becomes a path constructor with
   the translated boundary. Add the carrier's set or proposition squash.
   H1 checks the complete signature and its boundaries.
4. Assemble the model from the constructors, law paths and squash evidence.
   Fold by recursion: apply the target's operations to the recursive
   results, use its law proofs for path clauses and its h-level evidence
   for squash clauses. Prove uniqueness by induction and homomorphism
   preservation; equality in the target carrier is a proposition.

This is a derivation strategy's supported fragment, not the definition of a
valid theory or a claim that other theories have no free objects. The first
strategy does not handle carrier families, multiple carriers, inputs such
as `M -> M`, or laws using derived operations without a checked translation
of their boundaries. Path-valued operations on set or proposition carriers
also wait for a specified homomorphism interface; setness alone does not
make the current `T.Hom` generator handle them.

**Additional laws become proof obligations.** A strategy can construct a
candidate from the equational part and then prove its remaining laws. It
must prove every law before assembling a model of the full theory, and
check the folds and universal property for the full theory's morphisms.
An unresolved law leaves the requested derivation failed, with its precise
goal and context. No law is dropped, assumed or replaced by an axiom.
The implementation may use proof search or explicitly supplied checked
evidence; syntax for supplying derivation evidence must be specified before
that extension ships.

For example, `zero != one`, written `zero = one -> Void`, asks for a
function from an equality to the empty type. It cannot become an equality
constructor. One way to discharge this obligation is a known model `B` of
the equational part with distinct zero and one: fold the candidate into
`B`, so any equality of its zero and one contradicts `B`'s proof. For a
free object, sending every generator to `B.zero` supplies the assignment.
This proves this particular law; it is not a procedure for arbitrary
propositional laws. A supplied witness or proof remains an explicit
dependency, with no new hidden assumptions.

### Failure is part of the contract

An explicit derivation request may fail at the theory declaration. No
partial capability is registered, and the error names the field, unsupported
construction, or unproved obligation. Removing the failed request leaves
the underlying theory usable; requesting `morphisms` alone does not request
initial or free objects. `free` never silently falls back to `initial` or
to a type with only a recursor. A parent's free capability is not inherited
automatically: a child's additional laws require its own derivation.

Diagnostics distinguish:

- **Unsupported construction or unproved obligation:** the current strategy
  cannot supply the requested term or proof. This does not establish
  mathematical nonexistence.
- **Proved obstruction:** a checked obstruction can justify nonexistence.
  No general decision procedure for existence is promised. Failure of
  proof search alone must never be reported as such an obstruction.

`Field` is a useful mathematical counterexample: all fields, with unital
field homomorphisms, have no initial object, because a field cannot map to
fields of different characteristics. Hence they have no free functor on
all generator types either. `Field` may request `morphisms`; a request for
`initial` or `free` must fail. An implementation without the checked
nonexistence proof reports its unsupported construction or outstanding
obligation, not a theorem it has not proved. Merely allowing `inverses` or
`zero_ne_one` as propositional law fields changes none of this
([Stacks Project, characteristic of a field](https://stacks.math.columbia.edu/tag/09FQ)).

### Proving a universal property by hand

These opt-ins control automatic generation, not which theorems can be
stated or proved. With `CommRing` deriving `morphisms`, the existing integer
model can be proved initial by constructing, for every target `R`, a term
of `IsContr(CommRing.Hom(integers, R))`. Together these form a theorem
`integers_initial : CommRing.IsInitial(integers)` (universe arguments
suppressed). This requires no `initial` or `free` capability: it is an ordinary theorem
about an existing model. The same proof restricts to target rings with
`zero != one`, since the integers satisfy that law too.

If automatic derivation also produces an initial commutative ring, its
universal property and the integers' theorem give an isomorphism between
the two models. The generated carrier need not replace the existing
integer representation. A hand-written theorem does not implicitly
register a derivation capability; an interface for reusing supplied
constructions and proofs can be specified separately.

### Higher theories and recursion

An untruncated example such as `Loop` still has a useful declared type, the
circle, and its eliminator. That is separate from deriving an initial or
free object for specified morphisms. Until its homomorphisms, coherence
fields and universal proof are supported, `deriving (morphisms, initial)`
or `deriving (morphisms, free)` fails. The circle remains available through
an ordinary `inductive` declaration and recursion. This replaces the old
exception that allowed `initial Circle : Loop(U0)` with recursion only and
no morphism opt-in. A later higher-theory strategy must specify its
homomorphism spaces and the level at which the universal property holds.

### Slices

1. L2.4d's opt-in and the capability registry: separate theory admission
   from derivation, specify universes, forgetful functor, collision checks
   and diagnostic obligations. L2.11 supplies general propositional laws.
2. The H1 equational strategy: declared type, model and computing fold;
   preserve existing prototype evidence, but do not advertise a completed
   `free` or `initial` capability yet.
3. Pointwise uniqueness, `T.Hom.ext`, the universal equivalence and its
   inverse laws; then publish successful capabilities and their named
   instances. Include the weaker `initial`-only derivation.
4. Additional-law obligations, with checked evidence and a specified way
   to supply it; `zero != one` is the first non-equational case.
5. Higher theories only after their morphism and coherence interface is
   specified. Recursors alone stay ordinary inductive constructions.

### Acceptance

- A monoid opts into `morphisms, free`: closed folds compute, pointwise
  uniqueness checks, and the restriction/fold equivalence has both inverse
  laws. The initial instance is free on `Void` and has a contractible
  carrier; counting generators is a free-monoid fold.
- Groups on `A` use the same strategy and prove their universal property.
- With only `CommRing`'s morphisms derived, `CommRing.IsInitial` is in
  scope and a hand-written `integers_initial : CommRing.IsInitial(integers)`
  checks as an ordinary theorem. It
  restricts to nontrivial rings and identifies the integers with any
  separately generated initial ring by an isomorphism.
- A theory with `morphisms` but no `free` rejects a `free` use. An
  `initial`-only capability supplies no free capability. Missing morphisms
  and generated-name collisions produce specific refusals.
- A theory can state `zero != one` without requesting a construction. A
  derivation with an outstanding proof of that law fails and displays it;
  supplied separating-model evidence discharges it when the other
  obligations are met. A false law is never accepted as an assumption.
- `Field` remains usable with `morphisms`; `initial` and `free` derivations
  fail. An unsupported strategy is not reported as a proof of nonexistence.
- A child's extra laws are checked even if its parent derives `free`.
- `Iterate`, multiple carriers, and unsupported path-valued operations are
  reported as strategy limitations. Ordinary circle recursion works while
  its categorical derivation is refused until coherences are supplied.

## Acceptance

Met on 2026-10-05: the library's `algebra`, `integers` and `rationals`, and
the fixtures named in the status above.

- `Semigroup`, `Monoid`, `Group`, `AbelianGroup`, `CommRing` and `Field` as
  library theories, with `Nat` a commutative monoid twice, the integers a
  commutative ring and the rationals a field, as quotients.
- A ring lemma takes one model argument and uses its notation.
- Homomorphisms compose, identity is a unit for composition, and an
  isomorphism's inverse is an isomorphism, on closed models by `evaluate`.
- Refusals: a field whose name two parents give, a law that is not about the
  theory's fields or is not evidently a proposition, an operation whose
  arguments are not sorts (for `Hom`), a notation that is not an operator, an
  `open` (now `use`) of a value that is not a model.

## Known limits

Found since the slices landed, each a candidate for a later slice rather
than a defect in this contract:

- **A law cannot be a truncation.** `Trunc(U, exists y : R. x * y = one)`
  is a proposition by its declaration at `prop`, but was not by the law
  check's form. Done with L2.10k (2026-10-06): the check accepts a type
  declared at `prop`.
- **A law cannot name the theory's universe,** which `Trunc` takes first:
  the universe of a theory's sorts had no name in its body. L2.10k needs
  that too. Done: the header names it ([L2.4c](#revision-l24c),
  2026-10-06).
- **Sorts are single sets or propositions, not families.** A monad's
  carrier `F(A : U0) : U0` is accepted as an operation, but its laws are
  equations in `F(B)` and are refused (E818). Computation notation's N1
  needs carrier families. Decided: theory families
  ([L2.4c](#revision-l24c)).
- **Independent theories cannot be combined on one carrier.** Two parents
  that each declare `M : set U;` clash on `M`, and renaming both to one
  name clashes too: carriers merge only as copies of one ancestor. An
  operator that two unrelated parents bind is refused (E804) unless the
  child renames one. Decided: carriers merge by name, and other clashes are
  ambiguous only where used ([L2.4c](#revision-l24c)).
- **No fixture records a wrong homomorphism's refusal.** Doubling offered
  as a homomorphism of `Nat`'s multiplicative monoid is refused, by the
  type of its preservation field, but only an ad hoc check shows it.
