# General vector-space basis theorem

Status (2026-09-22): **the general basis-existence theorem is checked**.

```cubist
theorem vector_space_has_basis(K : AlgebraicField, V : VectorSpace(K)) :
  FieldExists(VectorBasis(K, V))
```

Read it in `web/proofs/vector_basis_existence.cubist`, or open
`/proof.html?proof=vector_basis_existence&name=vector_space_has_basis`.
This is mere existence for every bundled small-carrier vector space, with no
finite-dimensionality hypothesis and no chosen basis supplied by the caller.
The chain-complete form of Zorn used here is proved from choice, not assumed.

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
- `finite_combinations`: concatenation of indexed families, addition of
  their combinations, and scalar multiplication of coefficients. The scalar
  action sends the zero vector to zero.
- `vector_subspaces` and `span_subspace`: subspace bundles, span closure
  under addition and scalar multiplication, the least-subspace property,
  and idempotence of span as an equality of predicates using univalence.
- `predicate_chains`: unions of U1-indexed families of small predicates;
  chains are directed, and every finite family in a nonempty directed union
  has a common member containing it. Membership and the cover remain
  truncated: no choice function is extracted.
- `independent_unions`: directed and chain unions are independent. The
  empty-chain case needs no supplied inhabitant: when proving a particular
  coefficient vanishes, that coefficient's vector supplies the seed locally.
- `independent_order`: independence evidence is a proposition, with an
  explicit cubical path between proofs. Independent subsets form a partial
  order under inclusion. Antisymmetry uses univalence, and chain unions are
  least upper bounds of the full subset records.

- `vector_arithmetic`: zero and negative scalars, cancellation by a nonzero
  scalar, and the additive interchange needed to isolate a summand.
- `finite_remainders` and `finite_omission`: isolate or delete any finite
  index, with injectivity, avoidance, coverage, and an exact combination law.
- `span_exchange`: a nonzero coefficient in a vanishing combination puts
  its vector in the span of all the other vectors.
- `independent_extension`: adjoining a vector outside the span preserves
  independence; a maximal independent subset spans and is a basis.
- `chain_complete_orders`: chain suprema and their universal property;
  partial-order carriers are sets, proved using path induction.
- `bourbaki_tower` and `bourbaki_witt`: the least closed tower is a chain;
  its supremum is a fixed point of a progressive endomap.
- `zorn_chain_complete`: choice supplies a merely selected strict-successor
  function if there were no maximal element; Bourbaki–Witt contradicts it.
- `vector_basis_existence`: instantiate that maximality theorem with the
  checked independent-subset order and turn a maximal subset into a basis.

`Span` is a truncation of finite-combination witnesses; it does not choose
coordinates. Independence quantifies over **injective** finite lists of
members, so repeating a vector cannot manufacture a false dependence.

`FiniteBasis` and `VectorBasis` are two useful interfaces. Their equivalence
for an explicitly enumerated finite subset has **not** yet been proved.
No assertion of finite dimension or dimension invariance follows merely
from defining `ExtensionDegreeWitness`.

## Checked statement and assumptions

The field and vector-space carriers lie in U0. Their types of predicates,
independent subsets, and bases lie in U1. Chain indices and Choice's domain
are checked at U1; they are not silently treated as small carriers.

The final theorem reports exactly these assumptions:

- `Choice(U1)`;
- `LEM(U0)`;
- `Truncate`, `TruncateIntro`, `TruncateProp`, and `TruncateElim` at U0 and U1.

The library's existing `Truncate(U1) : U1 -> U0` already lowers the universe
of a proposition. The tower construction uses this existing resizing strength
for its membership predicate. No axiom signature, kernel rule, or universe
mechanism was changed. Univalence and function extensionality are supplied
by the cubical development rather than additional assumptions.

The finite-coordinate development remains constructive. Scalar cancellation,
omission maps, and partial orders being sets are axiom-free. The extension
argument uses LEM explicitly to conclude that a coefficient is zero when it
cannot be nonzero. The result remains truncated: there is no implicit chosen
basis or coordinate function.

## Checked route from choice to maximality

The implementation uses a classical tower argument rather than Hartogs or a
new ordinal library. For mathematical background, see the
[Bourbaki tower formalization by Smolka, Schäfer, and Doczkal](https://www.ps.uni-saarland.de/extras/itp15/bourbaki.html).

1. In a chain-complete partial order, form the least family closed under a
   progressive map and chain suprema. Membership asserts its universal
   property, with propositional truncation.
2. Prove that each tower point is stable from below: advancing a strictly
   earlier tower point stays below it. Stable points separate the tower.
3. Conclude that the whole tower is a chain. Its supremum belongs to the
   tower, and advancing it cannot exceed that supremum, so it is fixed.
4. If there were no maximal element, every point would merely have a strict
   successor. `Choice(U1)` selects such successors only under a truncation.
   The domain and every fiber are proved sets before applying Choice.
5. Eliminate the selected function into the proposition Void: its fixed
   point contradicts strictness. Classical double-negation elimination gives
   mere existence of a maximal element.

`zorn_chain_complete` requires a supplied least upper bound for each chain,
including the empty chain. Independent subsets provide those bounds by
union. The more general version of Zorn for orders with only mere upper
bounds has not been formalized here; it is not needed for this basis theorem.

## From Zorn to a basis

Fix V. Order its proposition-valued independent subsets by inclusion.
Use extensionality/univalence to turn mutual inclusion into equality of
subsets, so this is a partial order on actual subset records.

The empty subset is independent. For a chain C of independent subsets,
its union is independent: a proposed dependence mentions only finitely
many vectors; the chain property puts those vectors together in one member
of C, where all coefficients must vanish. This finite-character argument, including empty chains, is checked without
choosing a representative from each truncated membership proof.

Zorn yields a maximal independent subset B. If a vector v is outside its
span, B union {v} is independent. Indeed, in a finite vanishing combination,
a nonzero coefficient of v lets us divide by it and express v in the span
of B, a contradiction. If that coefficient is zero, independence of B
forces the remaining coefficients to be zero. Classical decisions used to
split these cases must be explicit. Since B is contained in its span, v is
not in B, so this contradicts maximality. Therefore B spans V and is a basis.

## Remaining linear algebra for Galois theory

1. Connect explicit finite coordinate bases to enumerated independent subsets.
2. Develop finite exchange and dimension invariance, including reindexing and
   elimination of repeated generators where useful.
3. Define extension degree with its finiteness hypotheses and prove the
   degree tower law.
4. Optionally generalize maximality to the upper-bound-only form of Zorn,
   and prove that any prescribed independent subset extends to a basis.

The general basis theorem does not establish finite-dimensionality, equality
of lengths of finite bases, or the extension-degree tower law automatically.

## Validation

Full suite: **269 tests passed**, including the complete canonical corpus.
The basis theorem and reformatted source also pass the browser regression.

- Every new declaration and its dependencies pass the cubical C checker.
- The focused basis benchmark checks 676 declarations and 35 templates,
  with no failed, blocked, or over-100ms entries on the development machine.
- Regression tests instantiate arbitrary spaces, the zero-dimensional
  coordinate space, and the scalar space of F2; assert the exact axiom
  boundary; and reject an attempt to turn mere existence into a chosen basis.
