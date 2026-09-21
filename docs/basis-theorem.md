# General vector-space basis theorem

Status: foundations checked; the general existence theorem and the derivation
of Zorn from choice are **not yet formalized**. This is a continuation target,
not an added axiom or an asserted checked theorem.

## Checked interfaces

- `vector_spaces`: a vector space over a supplied `AlgebraicField` is an
  abelian group with a scalar action satisfying the four module laws.
- `field_vector_spaces`: every field embedding K -> L makes L a K-vector
  space. `ExtensionVectorSpace(K,E)` uses the specified extension inclusion.
- `linear_maps`: bundled linear maps, composition, pointwise extensionality,
  linear isomorphisms, coherent carrier equivalences and their univalence paths.
- `finite_bases`: `FiniteBasis(K,V,n)` supplies a linear isomorphism K^n -> V.
  Both coordinate roundtrips and coordinate uniqueness are checked. There is
  an explicit one-element basis for the scalar space K. No choice is used.
- `linear_span`: actual finite combinations indexed by `Fin(n)`, their
  proposition-valued span, and the general subset-basis interface
  `VectorBasis(K,V)`. Zero belongs to every span, generators belong to their
  span, span is monotone, the empty subset is independent, and independent
  subsets cannot contain the zero vector.

`Span` is a truncation of finite-combination witnesses; it does not choose
coordinates. Independence quantifies over **injective** finite lists of
members, so repeating a vector cannot manufacture a false dependence.

`FiniteBasis` and `VectorBasis` are two useful interfaces. Their equivalence
for an explicitly enumerated finite subset has **not** yet been proved.
No assertion of finite dimension or dimension invariance follows merely
from defining `ExtensionDegreeWitness`.

## Intended statement and assumptions

For every small bundled field K and small-carrier vector space V, prove
mere existence of `VectorBasis(K,V)`. A predicate on the carrier is in U1,
so the basis record and the family of candidate independent subsets must
be tracked at their actual universes. Do not silently resize them to U0.

Use the existing universe-specialized `Choice(U)` interface. Zorn must be
**derived**, not declared as an axiom and not left as an extra theorem
parameter in the final basis theorem. Track any `LEM(U)` instances needed
by the classical construction as well. The truncation interfaces retain
their existing signatures; do not add a stronger resizing assumption.

The finite-coordinate development remains constructive. Neither an
arbitrary field nor its vector spaces acquire a decidable equality or a
chosen basis implicitly.

## Mathematical route from choice to Zorn

One route is the Hartogs/transfinite-recursion proof. Its following steps
are mathematical specifications; they still need checked library proofs.

1. For a set P, construct a well-ordered type h(P) with no injection into P
   (Hartogs' lemma). Account for the universe of well-order relations and
   their identifications. Do not add a type of all ordinals or a universe code
   primitive to the kernel.
2. For a nonempty partially ordered P in which every chain has an upper
   bound, suppose there is no maximal element. Classically, each chain then
   has an element strictly above every member: take an upper bound and an
   element strictly above that bound. The empty chain uses nonemptiness.
3. Apply choice to the set of chains to obtain a function assigning such a
   strict upper bound. This is the actual choice step; ordinary mere upper
   bounds cannot be projected as data without justification.
4. By transfinite recursion on h(P), choose the next point strictly above
   all earlier points. Inductively the earlier points form a chain, and the
   resulting map h(P) -> P is strictly increasing, hence injective.
5. This contradicts Hartogs' property. Conclude the existence of a maximal
   element using the explicitly recorded classical assumptions.

A different checked proof of Zorn from choice may replace this route if it
requires less infrastructure. Its dependence on choice must remain visible;
renaming an assumed maximality principle is not a derivation.

## From Zorn to a basis

Fix V. Order its proposition-valued independent subsets by inclusion.
Use extensionality/univalence to turn mutual inclusion into equality of
subsets, so this is a partial order on actual subset records.

The empty subset is independent. For a chain C of independent subsets,
its union is independent: a proposed dependence mentions only finitely
many vectors; the chain property puts those vectors together in one member
of C, where all coefficients must vanish. Prove this finite-character
argument, including empty chains, rather than choosing a representative
from each truncated membership proof.

Zorn yields a maximal independent subset B. If a vector v is outside its
span, B union {v} is independent. Indeed, in a finite vanishing combination,
a nonzero coefficient of v lets us divide by it and express v in the span
of B, a contradiction. If that coefficient is zero, independence of B
forces the remaining coefficients to be zero. Classical decisions used to
split these cases must be explicit. Since B is contained in its span, v is
not in B, so this contradicts maximality. Therefore B spans V and is a basis.

## Next formal lemmas

1. Concatenate finite combinations; prove the combination laws, scalar
   multiplication, zero coefficients, reindexing, and elimination of repeated
   vectors. Establish subspace closure of `Span` and finite character.
2. Prove extension of an independent subset by a vector outside its span,
   including the coefficient-division step using the existing nonzero
   inverse API. Do not assume decidable equality of arbitrary field elements.
3. Construct chain unions of independent subsets and prove their
   independence. Introduce only the order/chain interfaces needed by Zorn.
4. Develop Zorn from `Choice(U)` with checked universe bookkeeping, then
   apply it to the independent-subset order and finish basis existence.
5. Connect explicit finite bases to the subset interface. Separately prove
   finite dimension invariance and the tower law needed for Galois theory.

The general basis theorem will not by itself prove that an extension is
finite-dimensional, that two finite bases have the same length, or the
extension-degree tower law.
