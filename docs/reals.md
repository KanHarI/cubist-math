# Real-number development

The shared interface is an **Archimedean ordered field with Cauchy
completeness**. Dedekind completeness is a separate property. The constructive
modules do not assume excluded middle or choice.

**Status: foundational development, not three completed real fields.** The
definitions and lemmas below are checked by the kernel. No theorem yet supplies
a `CompleteOrderedField` instance for any of the three construction carriers.
In particular, the parameter named `Q` is an abstract small type; this work has
not yet constructed the rational ordered field.

## Shared interface

[ordered_fields.proof](../web/proofs/ordered_fields.proof) defines a commutative
ring, a proposition-valued strict order, non-strict order and apartness, lattice
operations, order-compatible arithmetic, and inversion for elements apart from
zero. It proves cancellation, uniqueness of inverses, and `zero != one` from
the stated laws.

[complete_fields.proof](../web/proofs/complete_fields.proof) adds:

- `Archimedean`: every element is below some natural-number multiple of one.
- `FieldCauchy`: a sequence **with a modulus**. Each positive epsilon supplies
  an actual natural bound, not merely the proposition that a bound exists.
- `FieldConverges` and `CauchyComplete`: a limit and its convergence evidence.
- `CompleteOrderedField`: the ordered-field laws, Archimedean property, and
  Cauchy completeness together.
- `DedekindComplete`: every inhabited, rounded, disjoint, located two-sided
  cut is realized. This is separate from `CompleteOrderedField`.

The distinction between the two completeness properties, and the two-sided
cut conditions, follow the [HoTT book's real-number chapter](https://github.com/HoTT/book/blob/master/reals.tex).
This formulation does not impose classical trichotomy or the assertion that
every inhabited bounded subset has a supremum on the constructive interface.

`complete_field_ordered` and `complete_field_limit` consume an already supplied
field certificate. They are accessors, not proofs that a particular construction
is a complete ordered field.

## Construction modules and checked results

| Module | Checked development | Additional assumptions |
| --- | --- | --- |
| [Constructive Dedekind cuts](../web/proofs/dedekind_cuts.proof) | Proposition-valued cuts; principal cuts; preservation and reflection of strict order; injectivity of the principal-cut map; downward/upward closure, separation, irreflexivity and transitivity of cut order | The base order, density, and absence of endpoints are explicit parameters where needed. Truncation; no excluded middle or choice. |
| [Classical Boolean cuts](../web/proofs/boolean_cuts.proof) | Boolean predicates with cut laws; decoding to constructive cuts; conversion back with proofs that both memberships are preserved | Decoding uses no classical principle. Encoding arbitrary proposition-valued cuts uses `LEM`; predicate equality also uses univalence and function extensionality. No choice. |
| [Ordinary Cauchy quotient](../web/proofs/cauchy_quotient.proof) | Sequences with moduli; eventual-closeness relation; equivalence-relation laws under explicit reflexivity and radius-composition hypotheses; quotient carrier; mere existence of representatives | Constructive through the quotient construction. Simultaneous representatives use the explicit `RepresentativeChoice` argument. No global choice axiom is loaded. |

[set_quotients.proof](../web/proofs/set_quotients.proof) represents classes by
predicates with a **truncated** witness that the predicate describes a class.
It proves surjectivity of the class map and, for a proposition-valued equivalence
relation, that two classes are equal exactly when their representatives are
related. The generic carrier can be formed for other relations too; its name
does not certify setness or a quotient universal property for those relations.

`RepresentativeChoice(A, relation, sequence)` is the particular countable
choice instance that combines the individually inhabited representative fibers
of a sequence. It is a theorem parameter, not a new axiom and not a proof of
countable choice. Its conclusion remains truncated. Consequently, the axiom
list for `cauchy_sequence_representatives` does not include choice: the choice
hypothesis is visible in its type instead.

The ordinary quotient is distinct from the book's higher inductive-inductive
Cauchy completion. The latter avoids countable choice; that construction has
not been implemented here. The book discusses the role of countable choice in
the ordinary construction and compares Cauchy and Dedekind reals in the
[same chapter](https://github.com/HoTT/book/blob/master/reals.tex).

## Universes and foundational assumptions

`Q : Type` is small. Predicates `Q -> Type`, and hence proposition-valued cuts,
live in `Type1`. The shared interface accepts a carrier `F : Type1`, so these
cuts do not have to be replaced with Booleans to fit its universe.

[field_logic.proof](../web/proofs/field_logic.proof) specializes the **existing**
prelude truncation and function-extensionality axioms at `Type1` using the new
explicit-universe primitives. [field_extensionality.proof](../web/proofs/field_extensionality.proof)
adds small-proposition extensionality via the existing univalence axiom and
equality lemmas for dependent pairs in `Type1`.

There is a foundational qualification: the existing prelude `lib_Trunc` returns
a type in **U0 even for an input in a higher universe**. `FieldExists` retains
that signature. This is universe-lowering truncation; this development is not
claimed to avoid resizing strength. It adds no resizing axiom, classical axiom,
choice axiom, or unchecked kernel rule. Changing that existing foundation to
universe-preserving truncation would be a separate change.

## Remaining construction proofs

1. Construct the rational ordered field and discharge its order, arithmetic,
   density, and radius-composition obligations.
2. Prove setness and extensionality of the cut carrier, define its arithmetic
   and lattice operations, and prove all ordered-field laws.
3. Prove the Archimedean property, Cauchy completeness, and Dedekind completeness
   of the constructive cut construction.
4. Prove the Boolean conversion round trips and transport the full field
   certificate to the classical carrier.
5. Complete the quotient's setness and elimination interface, descend arithmetic
   and order to Cauchy classes, and prove completeness with the precisely stated
   choice assumption. Relate that assumption to set-level countable choice.
6. Exhibit the three named `CompleteOrderedField` certificates and compare them
   under their stated assumptions.

No item in that list is replaced by an axiom asserting that a candidate is a
complete ordered field. In the web source explorer, each real-number module
links to this status and checks its actual declarations.
