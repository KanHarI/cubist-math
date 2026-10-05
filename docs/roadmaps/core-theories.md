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
independent theories, was decided on 2026-10-05 and is not implemented:
[L2.4c](#revision-l24c). The sections after it describe the implemented
L2.4 grammar.

## Revision (L2.4c)

Decided on 2026-10-05; nothing here is implemented yet. Existing theories
keep checking until the migration, which lands in two commits, as the
retirement of `cases` did: the new forms beside the old, every source
moved and checked while the old still parse, then the old forms refused.

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

### The universe is named in the header

`theory Monoid(U < UU0)` binds the universe of the theory's carriers, so a
field or a law can name it, as L2.10k's `Trunc(U, …)` needs. A theory may
bind several, `theory Module(U, V < UU0)`, for carriers in different
universes. Whether the header binder is required, or optional with
`M : set` meaning the model's unnamed universe, is open.

### A theory's name is the type of its models

`G : Monoid(U0)`, not `G : Monoid.Model(U0)`: `Monoid.Model` is retired.
`Monoid.make`, `Monoid.Hom`, `Monoid.Iso` and the projections stay beside
it, as `Trunc` and `Trunc.squash` do. Models do not lift along universe
cumulativity: `CommMonoid.Model(U0)` is not a `CommMonoid.Model(U1)` today
(a type mismatch, though its carrier lifts), and a generated lift is later
work if a use needs it.

### Theory families

A carrier may be a family, indexed by any type:

```
theory Monad(U < UU0) {
  F(A : U) : set U;
  pure(A : U, a : A) : F(A);
  bind(A, B : U, m : F(A), k : A -> F(B)) : F(B);
  law left_unit(A, B : U, a : A, k : A -> F(B)) : bind(A, B, pure(A, a), k) = k(a);
  law right_unit(A : U, m : F(A)) : bind(A, A, m, fun (a : A) => pure(A, a)) = m;
}

theory Graded(U < UU0) {
  V(n : Nat) : set U;
  mul(m, n : Nat, x : V(m), y : V(n)) : V(m + n);
}
```

- `F(A : U) : set U` holds `F(A : U) : U` and
  `F_is_set(A : U) : IsSet(U, F(A))`. An equation between elements of
  `F(A)` is a proposition, so the monad laws pass the law check, which
  refuses them today. Computation notation's N1 uses this.
- A homomorphism maps each index: `map_F(A : U) : M.F(A) -> N.F(A)`, and
  preserves each operation at each index. It has no naturality field: the
  signature has no action on maps to be natural for, and a monad's
  naturality follows from preserving `pure` and `bind`.
- Indices match definitionally, as all types do: no generator inserts a
  transport. An index equal only by a proof, as `m + n` and `n + m` are,
  needs the transport written where it is used.

**Variance.** Checking needs none: there is no subtyping beyond universe
cumulativity, and types match by conversion. Generating homomorphisms does:
a homomorphism maps arguments forward only. An operation's argument may
mention a carrier only where a forward map reaches it, covariantly: `k : A
-> F(B)` maps to `N` by composing with `map_F(B)`. An argument such as
`g : F(A) -> A` would need the inverse map, so a theory with one has no
`T.Hom` (its isomorphisms could still be generated, later). This replaces
E817's rule, which admits only arguments and results that are carriers.

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
replaces today's `open` (its decision 7).

### Open questions

1. Whether `theory T(U < UU0)` is required, or optional with `M : set`
   meaning the model's universe.
2. How a qualified operator's operands are read (above).
3. Whether a child can drop a parent's notation without giving it another.
4. Homomorphisms of theories with carriers of no h-level: the coherence
   fields of path-valued operations, and how far up to generate them.

## Scope

L2.4 delivers, in slices:

1. **Notation packs and `open`.** A model's operations bound to operators and
   names for the rest of a block.
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
separately); numerals interpreted in a model; type-directed overloading and
instance search. Structure scope stays explicit: an operator means one thing
in a scope, chosen by `open` or `section`, never by the types of its operands.
The [notation roadmap](notation.md), L2.10, adopts explicit model notation
views as the next direction: an expression or block selects its model before
its operators and literals are elaborated. `v.(expression)` and `use v;`
are its decided spellings; its remaining grammar and elaboration gates are
draft. Existing `open` and section semantics remain compatible
during that migration; type-based automation is optional later work, requiring
evidence that it preserves the explicit semantics.

## Theories

```
theory Semigroup {
  sort M : set;
  mul(x, y : M) : M notation x * y;
  law mul_assoc(x, y, z : M) : (x * y) * z = x * (y * z);
}

theory Monoid extends Semigroup {
  one : M;
  law one_mul(x : M) : one * x = x;
  law mul_one(x : M) : x * one = x;
}

theory Group extends Monoid {
  inv(x : M) : M;
  law inv_mul(x : M) : inv(x) * x = one;
}
```

A theory's body lists, in order:

- **sorts**, `sort M : set;` or `sort P : prop;`: a type in the model's
  universe, with the evidence of its h-level as a field (`M_is_set`,
  `P_is_prop`);
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
or `x * y`, or a relation, `x < y` or `x <= y`. Unary minus stays path
inversion, so negation and inverses are named operations.

This is the implemented L2.4 grammar. L2.10's proposed operators and literals
are separate work. They move reversal to `~` first (L2.10i), keeping the
groupings of `-p @ i` and `p @ -i & j`, so that `-` becomes arithmetic.

## Models

A theory `T` declares, in its module:

- `T.Model(U < UU0) : next(U)`, the type of models whose sorts are in `U`: a
  Σ record of the fields in order, with the kernel's pair eta;
- `T.make{{U < UU0}}(…)`, its constructor, one parameter per field, so that
  named arguments build a model field by field;
- for each field `f`, `T.f{{U < UU0}}(m : T.Model(U))`, its projection, typed
  through the earlier projections, so that `T.one(m) : T.M(m)`.

`m.f` is `T.f(m)` wherever `m`'s type is a theory's record, and `T.f` is
otherwise a qualified name, as `Trunc.squash` is. Goals and messages show
`m.f` for a projection.

```
import nat, hlevels;

def additive : Monoid.Model(U0) := Monoid.make(M := Nat, M_is_set := nat_is_set,
  mul := add, mul_assoc := nat_add_assoc, one := 0, one_mul := nat_zero_add,
  mul_one := nat_add_zero);
```

## Notation and `open`

`open m;` is a proof statement. For the rest of its block, each field of `m`
is in scope by its name, as the projection `m.f`, and each notation of `m`'s
theory means `m`'s operation:

```
def square(G : Group.Model(U0), x : G.M) : G.M {
  open G;
  exact x * x;
}
```

A name or operator that `open` binds shadows the one it had, as `let` does,
until the block ends; a later `open` of another model shadows an earlier
one. Where no model's notation binds `+` or `*`, they keep their meaning
today: `add` and `mul` in scope, as for `Nat`. L2.10j retires that
fallback; an operator then means only what a view, an `open` or a section
binds, and a section or `open` selects its model's view, innermost first.

L2.10 extends this explicit selection to expression views, including theorem
statements, with operand views determining numeral interpretations and a
printer that retains the model whenever omitting it would change meaning.
It does not change the behavior of existing `open` declarations or sections
as an incidental part of introducing that syntax.

## Sections

```
section {{U < UU0}}(G : Group.Model(U)) {
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
different parents are refused unless they are one ancestor's field shared
as above; the error names both and asks for a renaming. A child model has
each parent's model: `T.p(m) : P.Model(U)` for a parent `P` labelled `p`, and
`m.p` writes it. An unlabelled parent's label is its name in snake case,
`G.monoid` for `Group extends Monoid`.

## Homomorphisms and isomorphisms

For a theory whose sorts are sets or propositions and whose operations take
and return sorts:

- `T.Hom{{U, V < UU0}}(A : T.Model(U), B : T.Model(V)) : max(U, V)` has a map
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

## Elaboration

A theory expands, before checking, into the definitions above, in the
module that declares it, in order: the record and its constructor, the
projections, each parent's model, then `Hom` and `Iso` with their
operations. The expansion is source the translator elaborates like a
user's own, so every generated definition is inspectable by name. The
module needs `hlevels` for the sorts' evidence, and the elaborator says so
when it is missing.

`open` and sections bind names and operators lexically, recorded in the
inspector with the projection each stands for. The operator elaboration
reads an operator's binding before its fallback, the `add` or `mul` in
scope.

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
  `open` of a value that is not a model.

## Known limits

Found since the slices landed, each a candidate for a later slice rather
than a defect in this contract:

- **A law cannot be a truncation.** `Trunc(U, exists y : R. x * y = one)`
  is a proposition by its declaration at `prop`, but not by the law check's
  form. L2.10k's partial field inverse needs the check to accept an
  application of a type declared at `prop`.
- **A law cannot name the theory's universe,** which `Trunc` takes first:
  the universe of a theory's sorts has no name in its body. L2.10k needs
  that too. Decided: the header names it ([L2.4c](#revision-l24c)).
- **Sorts are single sets or propositions, not families.** A monad's
  carrier `F(A : U0) : U0` is accepted as an operation, but its laws are
  equations in `F(B)` and are refused (E818). Computation notation's N1
  needs carrier families. Decided: theory families
  ([L2.4c](#revision-l24c)).
- **Independent theories cannot be combined on one carrier.** Two parents
  that each declare `sort M : set;` clash on `M`, and renaming both to one
  name clashes too: carriers merge only as copies of one ancestor. An
  operator that two unrelated parents bind is refused (E804) unless the
  child renames one. Decided: carriers merge by name, and other clashes are
  ambiguous only where used ([L2.4c](#revision-l24c)).
- **No fixture records a wrong homomorphism's refusal.** Doubling offered
  as a homomorphism of `Nat`'s multiplicative monoid is refused, by the
  type of its preservation field, but only an ad hoc check shows it.
