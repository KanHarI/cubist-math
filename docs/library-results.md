# Results of the first library

This records, in mathematical English, what the first proof library
established. It lists only two kinds of result:

- **The convex hull:** the frontier results of each line of development. Each
  one needs the supporting material beneath it, so supporting lemmas, laws and
  definitions are not listed separately.
- **Iconic results,** marked ★, even when later results build on them.

Statements here are deliberately independent of the old formalization: they
name no definitions, encodings or proof structure. A rebuild should choose its
own. The archived modules that contain each area are listed at the end, for
reference only.

**Logical footprint** is recorded for each result, because the rebuild should
keep assumption-free results computing:

| Tag | Meaning |
| --- | --- |
| **C** | Assumption-free; closed instances compute. |
| **T** | Uses propositional truncation, which the first library postulated rather than constructed. |
| **LEM** | Uses excluded middle for propositions. |
| **AC** | Uses the axiom of choice for sets. |

Univalence and function extensionality are theorems of the cubical theory and
are not tagged.

## Foundations

- ★ **Hedberg's theorem.** A type with decidable equality is a set. More
  generally, a type whose path spaces carry weakly constant endomaps is a set.
  [C]
- **Equivalences from inverses.** Every quasi-inverse (a map with an inverse
  and both inverse homotopies) can be corrected to a half-adjoint equivalence,
  in every universe. Being an equivalence is a proposition. [C]
- ★ **Structure identity principle.** Consider structures on sets (operations
  with law evidence) whose notion of isomorphism is proposition-valued,
  reflexive, and reflects identities. For these, equality of structured sets
  is equivalent to isomorphism. [C]
- **Set quotients.** For an equivalence relation on a type:
  - the quotient exists and is a set;
  - it is effective: classes are equal exactly when their representatives are
    related;
  - every relation-respecting map into a set descends uniquely.

  The construction needs no quotient axiom and never chooses representatives.
  [T]
- ★ **Choice gives sections.** With the axiom of choice, every surjection
  between sets merely has a right inverse. [AC]

## Numbers and counting

- ★ **Euclid's theorem.** For every natural number there is a larger prime.
  [C]
- **Integers.** The integers form a set, and successor is an equivalence of
  them. [C]
- ★ **Numerals by univalence.** Binary numbers and positional numerals in
  every base b ≥ 2 are equivalent to the unary natural numbers:
  - representations are unique;
  - addition, multiplication and factorial correspond;
  - base b converts to binary directly.

  10! = 3,628,800 is computed in binary, in base 2 and in base 10, and carried
  between every pair of representations by transport along these
  equivalences. [C]
- **Uniqueness of finite cardinality.** If the n-element and m-element types
  are equivalent, then n = m. [C]
- ★ **Counting functions and permutations.** There are mⁿ functions from an
  n-element set to an m-element set. There are k! self-equivalences of a
  k-element set. Both are stated as equivalences of types. [C]
- ★ **Binomial types.** For finite sets, the type of decidable subtypes of an
  n-element set that are merely equivalent to a k-element set (Rijke's
  binomial type) has "n choose k" elements. Pascal's rule holds as an
  equivalence of types. [T]
- **Finite choice and fibered counting.** A finite product of merely
  inhabited types is merely inhabited, with no choice axiom. A type fibered
  over an n-element base with m-element fibers has nm elements. [T]

## Order and sets

- ★ **Cantor–Schröder–Bernstein.** Two sets with injections in both
  directions are equivalent. [LEM]
- ★ **Bourbaki–Witt fixed-point theorem.** On a partial order in which every
  chain, including the empty chain, has a supremum, every progressive map
  (x ≤ f(x)) has a fixed point. [LEM]
- ★ **Zorn's lemma.** In such a chain-complete partial order there is a
  maximal element. [AC, LEM]

## Groups

- ★ **Univalence for groups.** The type of isomorphisms between two groups is
  equal to the type of equalities between them. Distinct isomorphisms give
  distinct equalities. [C]
- **Subgroup lattice.** Subgroups form a complete lattice under intersection.
  Image and inverse image along a homomorphism are adjoint. Kernels are
  normal. [T]
- **Normality and cosets.** Multiplication of cosets is well defined exactly
  when the subgroup is normal. [T]
- ★ **Quotient groups.** A group modulo a normal subgroup is a group. The
  projection is an epimorphism, and every homomorphism that kills the
  subgroup factors uniquely through it. [T]
- ★ **First isomorphism theorem.** G/ker(h) is isomorphic to the image of h.
  [T]
- ★ **A non-normal subgroup.** The symmetric group on three letters has six
  elements, and a point stabilizer in it is not normal. [C]

## Homotopy types

- ★ **The fundamental group of the circle is the integers.** The circle is
  the suspension of the two-point type. Its loop space is a set, and as a
  group it is isomorphic, and hence equal, to the additive group of integers,
  by the winding number. [C]
- **Degree and retractions.** The n-th power map of the circle has degree n.
  A map of nonzero degree is not null-homotopic. ★ No contractible type
  retracts onto the circle, which is the homotopy form of the no-retraction
  theorem. [C]
- **Punctured planes as bouquets of circles.** Model the plane with n
  punctures by a bouquet of n circles:
  - every loop is merely a word in the generators;
  - winding around each puncture is a homomorphism to the integers;
  - the generators are nontrivial and pairwise distinct.

  [T]
- ★ **The twice-punctured plane is not abelian.** Its two generating loops do
  not commute. So there is a noncontractible loop with zero winding around
  every puncture, and winding numbers do not classify loops. [C] Every
  additive period vanishes on that loop. [T]

## Linear algebra

- ★ **Every vector space has a basis.** [AC, LEM]
- ★ **Invariance of dimension.** The dimension of a finite-dimensional space
  does not depend on the basis, and isomorphic spaces have equal dimension.
  Every finite spanning family contains a basis. Subspaces of
  finite-dimensional spaces are finite-dimensional. [LEM]
- **Finite free spaces are projective,** and restriction of scalars
  multiplies bases, which gives the input to the tower law. [T]

## Polynomials

- **Polynomial rings.** Polynomials over a field form an integral domain in
  which degrees add. Division with remainder exists and is unique. Bézout's
  identity holds. Every nonzero ideal is principal. Every nonconstant
  polynomial has an irreducible factor. [LEM]
- ★ **Roots.** The factor theorem holds. A nonzero polynomial of degree n has
  at most n roots in any field extension. Evaluation commutes with field
  embeddings. [LEM]
- **Adjoining a root.** For an irreducible polynomial p, the residue ring
  modulo p is a field of degree deg p over the base, with basis
  1, x, …, x^(deg p − 1). Its embeddings into another field correspond
  exactly to the roots of p there. [LEM]

## Fields and Galois theory

Where noted, results take an algebraically closed field as a hypothesis. The
first library never constructed algebraic closures.

- **Explicit finite fields.** The fields with two and four elements are
  constructed. Isomorphic fields are equal, and so are isomorphic field
  extensions, including their embedding of the base. [C]
- ★ **Tower law.** [M:K] = [M:L]·[L:K]. A tower is finite exactly when both
  of its steps are. Finite extensions are algebraic, and finitely generated
  algebraic extensions are finite. The minimal polynomial divides every
  polynomial that the element annihilates. Finite extensions form a
  distinguished class in Lang's sense. [LEM]
- ★ **Splitting fields.** Every nonconstant polynomial has a root in some
  finite extension. Every nonzero polynomial has a finite splitting field, and
  splitting fields are normal. [LEM]
- **Counting embeddings,** into a supplied algebraically closed field:
  - a finite extension extends every embedding of its base;
  - a finite separable extension L/K has exactly [L:K] embeddings over a
    given embedding of K;
  - a finite normal separable extension E/K has exactly [E:K] automorphisms.

  [LEM]
- ★ **Dedekind–Artin independence.** Distinct field embeddings are linearly
  independent. [LEM]
- ★ **Artin's theorem.** For a finite group H of automorphisms of E,
  [E : E^H] = |H|, and the fixed field determines H. [LEM]
- ★ **Fundamental theorem of Galois theory.** Let E/K be finite, normal and
  separable, and embed E in an algebraically closed field. Then subgroups of
  the automorphism group correspond exactly (as an equivalence of types) to
  intermediate fields. For each intermediate field M, the subgroup fixing M
  is finite of some order h, and [E:K] = h·[M:K]. [LEM]
- ★ **Galois groups as fundamental groups,** where automorphisms of E/K are
  loops at E in the type of extensions of K. For F₄ over F₂:
  - this loop group is cyclic of order two, generated by Frobenius, which
    exchanges the roots of X² + X + 1;
  - F₂ and F₄ are the only intermediate fields;
  - the Galois correspondence for decidable subobjects is an equivalence
    proved with neither excluded middle nor choice.

  [C]

## Analysis

The first library constructed neither the rational nor the real numbers. Real
constructions (constructive Dedekind cuts, classical Boolean cuts, a quotient
of Cauchy sequences) were begun but not completed. Every result below holds
over any supplied ordered field, Archimedean or complete where stated.

- **Limits.** Limits are unique and respect the field operations. Convergent
  sequences are Cauchy. [T]
- ★ **Complex numbers over an ordered field.** They form a commutative ring
  with i² = −1, and conjugation is an involution. The squared norm is
  multiplicative. A complex number is invertible exactly when its squared
  norm is positive, which is constructive. Every nonzero number is
  invertible given excluded middle. Over complete scalars, complex Cauchy
  sequences converge. [T; LEM for the nonzero form]
- **Fine subdivisions.** Over an Archimedean field, every interval merely has
  arbitrarily fine tagged dyadic subdivisions, without choice. [T]
- ★ **Integration along segments.** Over complete scalars, a uniformly
  continuous integrand has a unique integral along a straight segment. It is
  the limit of dyadic Riemann–Stieltjes sums and does not depend on the
  choice of tags. It is linear, integrates a constant c to c times the
  displacement, and is additive when the segment is split at its midpoint.
  [T]
- **Periods on punctured planes.** Every additive period of loops in a
  punctured plane is the winding-weighted sum of its local contributions.
  Periods can be constructed as limits of approximate periods, independently
  of the approximation. [T]
- **Towards the fundamental theorem of algebra.** A dominating term keeps
  z + t·q away from zero for 0 ≤ t ≤ 1, and algebraic closure implies the
  existence of square roots. The theorem itself was not reached. [T]

## Where the archive keeps them

For reference only. Names are module names in the archived library.

| Area | Modules |
| --- | --- |
| Foundations | `sets`, `equivalence_from_inverse`, `structured_sets`, `set_quotients`, `quotient_descent`, `quotient_sets`, `surjections` |
| Numbers and counting | `euclid`, `integers`, `binary_*`, `radix_*`, `finite_cancellation`, `function_counting`, `permutations`, `binomial_*`, `finite_dependent_counts` |
| Order and sets | `schroeder_bernstein`, `bourbaki_witt`, `zorn_chain_complete` |
| Groups | `group_univalence`, `subgroup_*`, `normal_subgroups`, `group_cosets`, `quotient_group_universal`, `group_first_isomorphism`, `non_normal_subgroup` |
| Homotopy types | `circle`, `circle_group_identity`, `circle_degree`, `bouquet_*`, `puncture_*` |
| Linear algebra | `vector_basis_existence`, `finite_dimension`, `dimension`, `spanning_subfamilies`, `subspace_carriers`, `finite_linear_lifts`, `scalar_restriction` |
| Polynomials | `polynomial_*` |
| Fields and Galois theory | `finite_fields`, `algebraic_fields`, `extension_degree`, `finite_towers`, `splitting_fields`, `normal_extensions`, `embedding_counts`, `artin_*`, `galois_*`, `f4_*` |
| Analysis | `dedekind_cuts`, `cauchy_quotient`, `field_limits`, `complex_*`, `fine_interval_*`, `affine_*`, `puncture_periods`, `complex_deformation` |
