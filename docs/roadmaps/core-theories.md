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
instance search, which the roadmaps defer. Structure scope stays explicit:
an operator means one thing in a scope, chosen by `open` or `section`, never
by the types of its operands.

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
today: `add` and `mul` in scope, as for `Nat`.

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
