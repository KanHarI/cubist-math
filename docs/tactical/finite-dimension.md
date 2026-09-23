# Finite dimension, extension degree, and the tower law

Checked on 2026-09-22 in the cubical C kernel. The development introduces no
axioms and changes no kernel or language code.

## Results

- `finite_dimension.finite_dimension_invariance`: two finite bases of the
  same vector space, of sizes m and n, imply m = n.
- `dimension.dimension_linear_iso`: linearly isomorphic finite-dimensional
  spaces have equal dimensions.
- `extension_degree.extension_degree`: the unique natural-number degree of
  an extension with explicit finite-dimensionality evidence.
- `extension_degree.finite_extension_tower`: two finite steps in a commuting
  tower give a finite composite extension.
- `extension_degree.tower_law`: **[M:K] = [M:L] · [L:K]**. This holds for any
  evidence of finiteness for the three extensions, not only the particular
  product basis used in the proof.
- `extension_degree.extension_degree_iso`: isomorphic extensions over K
  have equal degrees, proved by transporting along their univalent equality.

The current field and vector carriers lie in U0, as in the existing bundled
interfaces. Infinite extensions have no default natural-number degree.

## Finite spanning and the converse tower criterion

The subsequent development checks `finite_spanning_subfamily_basis`: every
finite spanning family contains an indexed, independent spanning subfamily.
`family_basis_coordinates` turns that data into a coordinate basis.
`finite_subspace_basis` supplies a mere finite basis for any predicate subspace
of a finite-dimensional vector space. The proofs use LEM(U0) and small
truncation, not Choice.

`finite_extension_tower_converse` derives finiteness of L/K and M/L from
finiteness of M/K in a commuting tower. `finite_extension_tower_iff` combines
both directions. These results have focused regression coverage in
`tests/finite-spanning.test.mjs`. They also support the finite field-generator
and embedding-count proofs described in [polynomial algebra](polynomial-algebra.md).

## Coordinate data versus dimension

`FiniteBasis(K,V,n)` is a linear isomorphism K^n → V. It contains expansion,
coordinates, and both inverse laws. Different bases remain different data.

`HasDimension(K,V,n)` is the propositional truncation of that basis type.
`FiniteDimensional(K,V)` is the dependent pair

```cubist
exists n : Nat, HasDimension(K, V, n)
```

This pair is proved a proposition: dimension invariance identifies its
natural numbers, and truncation identifies its evidence. Thus projecting n
is legitimate without choosing a basis. Mere existence of a finite basis
also suffices, by elimination into this proposition.

`ExtensionDegreeWitness` continues to retain an actual basis.
`ExtensionDegree(K,E,n)` asserts its mere existence, and
`extension_degree(K,E,finite)` projects the unique number. The specification,
basis comparison, and independence from finiteness evidence are all checked.
The identity extension has degree one, and degree zero is impossible.

## Dimension invariance: finite elimination

The main intermediate result is stronger than invariance:

> An injective linear map K^m → K^n implies m ≤ n.

Induct on n. A positive-dimensional coordinate space cannot inject linearly
into K^0: the image of its first coordinate vector cannot equal the image of
zero. For the induction step, the image u of the first coordinate vector is
nonzero. A finite search finds a nonzero entry; a coordinate permutation
moves it to the first position.

Write a for that entry and choose its inverse b from the field's supplied
inverse law. On the remaining source coordinates define

- h(v) = f(0,v);
- c(v) = b · first(h(v));
- g(v) = tail(h(v) − c(v)u).

Each map is proved linear. The corrected vector has first coordinate zero.
If g(v) is zero, the full corrected vector is zero, so
f(0,v) = c(v)f(e₀). Injectivity gives (0,v) = c(v)e₀, whose tail gives v = 0.
A separate kernel criterion then proves that g is injective. Induction
finishes the inequality. Applying it to both directions of a linear
isomorphism and using antisymmetry of natural-number order proves invariance.

The pivot search uses **LEM(U0)** on scalar equality. The elimination
algebra, kernel criterion, and coordinate permutations are constructive.
No axiom of choice is used. This proof does not assert that an arbitrary
bijection between coordinate carriers preserves dimension.

## Tower construction and equality

`RestrictScalars(K,L,e,V)` retains the additive group and precomposes the
scalar action with the embedding e : K → L. Linear maps and isomorphisms
restrict with it.

Given an m-element K-basis of L and an n-element L-basis of M, compose:

1. K^(n·m) ≅ (K^m)^n, using the checked bijection of finite product indices;
2. (K^m)^n ≅ L^n, using the lower basis pointwise;
3. L^n ≅ M, using the upper basis after restricting scalars.

The identity comparison at the end checks the actual scalar operations
through the composite embedding. It does not identify arbitrary law records
by definitional equality. The resulting `field_tower_basis` is axiom-free.

A `FieldTower` is a path from the composite K → L → M embedding to the
specified K → M embedding. `field_tower_basis_triangle` transports the basis
along that path. Truncated bases eliminate into the proposition asserting
the product degree; uniqueness yields the numerical tower law.

Paths of complete vector spaces transport dimension evidence. For fields,
the existing structure-identity theorem supplies a path of full extensions
from an extension isomorphism; `extension_degree_iso` uses it directly.
No higher homotopies are collapsed to a chosen equality proof: dimension is
a set-valued invariant of the existing univalent structures.

## Modules

| Module | Role |
| --- | --- |
| `linear_constructions` | Linear sums, differences, scalar maps, isomorphism composition, kernel criterion |
| `function_linear_isos` | Pointwise maps, reindexing, currying and product coordinates |
| `scalar_restriction` | Restricted scalar action, restricted maps, constructive product basis |
| `coordinate_splitting` | First coordinate, zero insertion, tail and extensionality |
| `coordinate_elimination` | Pivot correction and injectivity of the reduced map |
| `finite_dimension` | Pivot search, injective dimension bound, basis-size invariance |
| `dimension` | Truncated basis existence, unique dimension and invariance |
| `extension_degree` | Degree, finiteness, commuting-tower law and univalent invariance |

## Assumptions and validation

The numerical invariance results use LEM(U0) and existing small truncation
families. The product-basis theorem and its transport along a tower triangle
use no axioms. The degree-relation tower theorem uses only small truncation.
No result in this increment uses Choice, Zorn, or U1 resizing.

Regression tests check zero-dimensional spaces, arbitrary bases of the
coordinate plane and scalar space, coordinate permutations, identity degree,
arbitrary towers, and extension isomorphisms. Negative checks reject choosing
a basis from truncation, an incorrect degree, substituting a bijection for a
linear isomorphism, and silently changing the bottom embedding of a tower.

The focused dependency benchmark checks 747 concrete declarations and 35
universe templates, with all concrete declarations below 100ms. The full
suite passes 273 tests. The browser regression opens both the dimension
invariance and tower-law pages without diagnostics. All 272 proof sources
pass the formatter check. See `tests/dimension.test.mjs`.

## Remaining work for Galois theory

This increment proves the finite tower formula when both steps have finite
bases. The subsequent [polynomial and algebraic-extension development](polynomial-algebra.md)
supplies the converse finiteness criterion, finite spanning-family reduction,
subspace bases, and indexed independent subset bases. Artin's fixed-field
theorem and the core finite normal separable correspondence are also now
checked; the latter takes a supplied algebraically closed target and embedding.
See the [active Galois checkpoint](galois-handoff.md#active-checkpoint-2026-09-23)
for the remaining finite milestones and current validation. The numerical
validation above records this earlier dimension increment.
