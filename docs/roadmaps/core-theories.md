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
independent theories, was decided on 2026-10-05
([L2.4c](#revision-l24c)) and implemented in six slices on 2026-10-06.
The sections after it describe the implemented grammar.

## Revision (L2.4c)

Decided on 2026-10-05 and done on 2026-10-06, in six slices. Each slice
migrated in two commits, as the retirement of `cases` did: the new forms
beside the old, every source moved and checked while the old still
parsed, then the old forms refused.

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
variance (see **Variance** under [theory families](#theory-families)),
replacing E817's rule that every input and result be
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
form `G.(-) x` came with arithmetic `-` (L2.10b); the file-level
shadowing warning is not implemented yet. Evidence: `cubist-tests/theory_use.cubist` and the reference's
[selecting a model](../../web/reference/theories.html#open) section.
L2.4c is then complete; its open questions remain as recorded.

### Carriers are fields with an h-level

`sort` is gone (E180, since L2.4c). A carrier is a field whose type is a universe, optionally with
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
| `M : set U;` | `M : U` and `M_is_set : IsSet(U, M)`, as `sort M : set;` did before L2.4c |
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
  laws pass the law check, which refused them before L2.4c's families. Computation
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
  of a proposition carrier. Before L2.4c a relation could not be stated:
  `le(x, y : M) : U0` with the law `x <= x` was refused (E818). A family indexed by a
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

Before L2.4c, `Both` could not be declared: its parents' carriers clashed
by name, and renaming both to one name was refused too, since carriers
merged only when they were copies of one ancestor (as `Semiring`'s two
monoids are). The revision:

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

`SharedOperator` in `cubist-tests/theories.cubist` covers a clash inside
one theory. `cubist-tests/theory_independent.cubist` covers the
cross-parent cases: `Both` above, used through both labels; children that
rename a notation; an ancestor reached twice; and carriers of one name and
different kinds, refused.

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
  trips on both, and composition computing. `Arrow` in
  `cubist-tests/theory_headers.cubist` has two carriers and its identity
  homomorphism; no fixture yet checks round trips on both or composition.
- A parameter: `Module(U0, integers)`, whose homomorphisms have only
  `map_V`. No fixture covers it yet; `Pointed` in
  `cubist-tests/theory_headers.cubist` covers parameters.
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
   extension, with renaming. `T.Model` is now `T(U)` (L2.4c).
3. **`section`.** Shared parameters for a group of declarations, opened for
   their statements and proofs.
4. **`T.Hom` and `T.Iso`.** Homomorphisms and isomorphisms, with identity and
   composition, and the inverse of an isomorphism.

Not in L2.4: generated structure identity, `T.equality : (M = N) ≃
T.Iso(M, N)`, and displayed models (L2.4b, through HoTT F1); sorts that are
not sets or propositions, whose homomorphisms need coherence fields; relation
fields; `initial T` and `free T on A` (L2.6, whose contract is specified
[below](#initial-and-free-models-l26)); numerals interpreted in a model; type-directed overloading and
instance search. L2.4c later added carriers with no h-level and relation
fields, and L2.10c numerals in a model. Structure scope stays explicit: an
operator means one thing in a scope, chosen by `use` or `section`, never by
the types of its operands. The [notation roadmap](notation.md), L2.10,
extended explicit selection on 2026-10-06: named notations, `v.(e)` and
`use v;`, arithmetic operators, literals read by the library, and printing
in the selected notation (L2.10a–e), with the name-based fallback retired
(L2.10j). Type-based automation is optional later work, requiring evidence
that it preserves the explicit semantics.

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
  inputs and results may mention the carriers or not (see **Variance**
  under [theory families](#theory-families)), each with an optional
  `notation`;
- **laws**, `law name(binders) : statement;`, propositions about the earlier
  fields. A statement must be evidently a proposition: an equation between
  elements of a sort (the sorts are sets or propositions), `Void` or `Unit`,
  an element of a proposition carrier or relation, a type declared at
  `prop`, as `Trunc(U, …)` (L2.10k), or `forall`, `->` into one, or `and`
  of two. Anything else, such as `law point : M;` or a bare `exists`, is
  refused, since homomorphisms ignore laws. `Unit` and `Void` are reserved names, so
  no declaration can stand in for them here.

Inside the body the theory's own notation, and its parents', is in scope, and
each field is in scope by its name from its declaration on.

A notation is a binary operator, `x + y`, `x - y`, `x * y`, `x / y` or
`x ^ y`, unary `-x`, or a relation, `x < y` or `x <= y` (L2.10b); `>` and
`>=` are never declared. An operand of another view names it, as
`x ^ nat.(n)`. A derived operation may read plain numerals, `notation
numeral` (L2.10c). `~` reverses a path and is never a notation.

This is the implemented grammar, with L2.10b's operators and L2.10c's
literals. Reversal moved to `~` first (L2.10i, 2026-10-06), keeping the
groupings `-p @ i` and `p @ -i & j` had, so that `-` could become
arithmetic.

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
import nat;
import hlevels;
import algebra;
use nat;

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

L2.10 extended this selection to expressions and theorem statements on
2026-10-06 (L2.10a–e), with operand views, literals read in the selected
notation, and a printer that keeps the model where omitting it would
change meaning. Only L2.10j changed sections: their selections are
complete.

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
    additive : AbelianGroup(M := R, mul := add notation x + y, one := zero, inv := neg,
      mul_assoc := add_assoc, one_mul := zero_add, mul_one := add_zero, inv_mul := neg_add,
      mul_comm := add_comm),
    multiplicative : CommMonoid(M := R) {
  law mul_add(x, y, z : R) : x * (y + z) = x * y + x * z;
}
```

A renaming gives a parent's field a name in the child, and an operation a
notation in place of its own; renaming a sort to one name in two parents, as
`M := R` above, makes it one sort of the child. Two fields of one name from
unrelated parents are both kept, named by label, as `first_point` and
`second_point` (`Bipointed` in `cubist-tests/theory_independent.cubist`),
and the bare name is refused where it is used (E830, E832). Carriers of
one name, kind and type merge
([combining independent theories](#combining-independent-theories)). A
child model has each parent's model: `T.p(m) : P(U)` for a parent `P` labelled `p`, and
`m.p` writes it. An unlabelled parent's label is its name in snake case,
`G.monoid` for `Group extends Monoid`.

## Homomorphisms and isomorphisms

For a theory whose carriers are sets or propositions and whose operations'
inputs and results the maps can follow (see **Variance** under
[theory families](#theory-families)):

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

**Proposed revision, L2.4d (2026-10-07).** Morphisms would be derived only
on request ([categories](categories.md)):

- **`deriving (isomorphisms)`** generates `T.Iso` by transport. This
  covers fields of any variance and families indexed by a carrier, which
  E817 and E825 refuse today.
- **`deriving (morphisms)`** generates `T.Hom` as described here. It adds
  the default category `T.cat` and implies `isomorphisms`.

An opt-in that cannot be honoured refuses the theory, naming the field. The
library's algebraic hierarchy would opt into `morphisms`. `initial` and
`free` would require it where `fold` is a `T.Hom`; an untruncated carrier
keeps the recursion-only `fold` below, with no opt-in.

## Elaboration

A theory expands, before checking, into the definitions above, in the
module that declares it, in order: the record and its constructor, the
projections, each parent's model, then `Hom` and `Iso` with their
operations. The expansion is source the translator elaborates like a
user's own, so every generated definition is inspectable by name. The
module needs `hlevels` for the sorts' evidence, and the elaborator says so
when it is missing.

`use` and sections bind names and operators lexically, recorded in the
inspector with the projection each stands for. An operator means only what
the selection binds; with nothing selected it is an error that suggests
`use nat;` (L2.10j).

## Initial and free models (L2.6)

**Specified** on 2026-10-06; **the first slice done** the same day
(`web/translator/initial-models.mjs`): `initial` and `free` declare the
type, its model and `fold`, which computes on constructors and generators,
with the refusals. `cubist-tests/initial_models.cubist` covers the
library's monoids. `initial` and `free` of its commutative monoids, groups
and commutative rings also check, with `fold` computing on the unit and on
generators, but no fixture holds them (checked 2026-10-07). This is the contract the
audit's finding 4 asks for before any `universal` is generated: separate
typed results, each stated for a fixed target model, and none of the form
`(initial T → M) ≃ T.Hom(…)`, which is false (the initial monoid has one
element, so two functions into a two-element monoid but one homomorphism).

### Which theories

`initial` and `free` take a theory `T` at fixed universes and parameters,
as `Monoid(U0)`, whose fields are:

1. **One carrier**, `M : set U`, `M : prop U` or `M : U`. Several carriers,
   families and relations are later work.
2. **Strictly positive operations.** Each input is the carrier or a type
   that does not mention it, and each output is the carrier, or a path in
   the carrier between operation terms, as `Loop`'s
   `loop : base = base`. An operation that takes the carrier under an arrow,
   as `iterate(g : M -> M, x : M)`, is refused (theory_variance's `Iterated`).
3. **Equational laws.** Each law is an equation between terms built from the
   operations and the law's own variables, which range over the carrier or
   over types that do not mention it. A conditional law, a truncation, as
   `Field`'s `inverses`, or a law about another type is refused, naming the
   law.
4. Derived operations are definitions over the fields, and are generated for
   the initial model as for any model; a law may not use one.

Anything else is refused at the declaration, with the first field that fails
and why.

### What a declaration gives

```text
initial N : Monoid(U0);
free W(A : U0) : Monoid(U0) on A;
```

`initial N : T(…)` declares, with no new kernel rule:

- `N`, a declared type ([L2.1](work-plan.md)) at the carrier's universe and
  h-level: a constructor for each operation, named as the operation, `N.mul`
  and `N.one`; a path constructor for each law, `N.mul_assoc`; and the
  squash of a `set` or `prop` carrier. `free` adds the generator,
  `W.gen(a : A)`. The declared type is checked as any other: a law whose
  boundary H1 does not admit is refused with H1's reason.
- `N.model : T(…)`, the model on `N`: the constructors are its operations,
  the path constructors its laws, and the squash its h-level evidence.
- `N.fold(M) : T.Hom(N.model, M)`, for any model `M` of `T` at the same
  universes and parameters, by recursion: each constructor clause applies
  `M`'s operation to the recursive results, each law clause is `M`'s law
  there, and the squash clause is `M`'s carrier evidence. `free` takes the
  generators' type and images too: `W.fold(A, M, g : A -> M.M)`.

Each result below is a separate typed statement, for a fixed target model:

1. **Computation**, by conversion: `N.fold(M).map(N.c(x, …))` is
   `M.c(N.fold(M).map(x), …)`, and `W.fold(A, M, g).map(W.gen(a))` is `g(a)`.
2. **Uniqueness, pointwise:** `N.fold_unique(M, f) : forall x : N.
   f.map(x) = N.fold(M).map(x)` for every `f : T.Hom(N.model, M)`, by
   induction into the family of equalities in `M`'s carrier, which are
   propositions there. For `free`, given `agrees : forall a : A.
   f.map(W.gen(a)) = g(a)`.
3. **Initiality:** `N.universal(M) : IsContr(T.Hom(N.model, M))`. It needs
   `T.Hom.ext`, generated with `T.Hom`: two homomorphisms with equal maps
   are equal, each preservation field being a proposition in a set.
4. **The free property:** `W.universal(M) : ContrEquiv(T.Hom(W.model, M),
   A -> M.M)`, restriction to the generators, whose inverse is `fold`.

A theory whose carrier is untruncated, as `Loop` with the circle for its
initial model, has no `T.Hom` until path-valued operations' coherence
fields are specified (L2.4c). Its `initial` gives the declared type and
`N.fold(M) : N -> M.M` as a function, by the type's recursion, with
computation on its point and path constructors, and no uniqueness. A
characterization of plain maps out of a carrier is stated only where the
constructors give one, as the declared type's own eliminator does.

### Slices

1. The declarations: the theory check, the declared type, `N.model`,
   `N.fold` and its computation, and the refusals.
2. `fold_unique`, pointwise.
3. `T.Hom.ext`, then `universal` for `initial` and for `free`.
4. Untruncated carriers: `initial` for `Loop`, with recursion only.

### Acceptance

- `initial N : Monoid(U0)`: `N.fold(M).map(N.one)` is `M.one` by `rfl`, and
  the carrier is contractible: the identity and the constant homomorphism to
  `N.one` agree, by `fold_unique` into `N.model` itself.
- `free W(A : U0) : Monoid(U0) on A`: folding into `Nat`'s additive monoid
  with `g := fun (a : A) => 1` counts generators, and computes on closed
  words; `fold_unique` against the homomorphism that counts by recursion.
- `free` groups on `A`, through `Group`'s laws.
- `initial Circle : Loop(U0)`: the circle, with its recursion.
- Refusals: `Field` (a truncated law), `Iterated` (the carrier under an
  arrow), a theory with two carriers, a law that uses a derived operation.

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
  needs carrier families. Done: theory families
  ([L2.4c](#revision-l24c)'s fourth slice, 2026-10-06).
- **Independent theories cannot be combined on one carrier.** Two parents
  that each declare `M : set U;` clash on `M`, and renaming both to one
  name clashes too: carriers merge only as copies of one ancestor. An
  operator that two unrelated parents bind is refused (E804) unless the
  child renames one. Done: carriers merge by name, and other clashes are
  ambiguous only where used ([L2.4c](#revision-l24c)'s fifth slice,
  2026-10-06).
- **No fixture records a wrong homomorphism's refusal.** Doubling offered
  as a homomorphism of `Nat`'s multiplicative monoid is refused, by the
  type of its preservation field, but only an ad hoc check shows it.
