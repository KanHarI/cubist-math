# Complex analysis roadmap

**Status:** checked algebraic prerequisites, not proofs of the fundamental
theorem of algebra, the residue theorem, or Great Picard. The concrete real
field instances described in the [real-number roadmap](reals-roadmap.md) are still incomplete.

Development is paused as of 2026-09-19. The
[handoff and resumption guide](../tactical/complex_analysis_handoff.md) records the latest
checked integral laws, validation, outstanding obligations and entry points.

## Checked now

All carriers below may live in `U1`, as our proposition-valued Dedekind
constructions do. No kernel operations or axioms were added.

The new [limit and homotopy-descent results](../tactical/analysis_limits.md) prove scalar
and complex limit laws, Cauchy completeness of complex pairs over supplied
complete scalars, and construction of additive periods from Cauchy
approximations with vanishing errors. The general construction takes limits
on representatives before descending to homotopy paths.
[Finite contour sums](../tactical/contour_sums.md) now supply explicit approximation data,
composition and telescoping laws, exact refinement errors, and scalar
tag-error estimates in terms of sampled variation. Complex tag errors now
have checked coordinate bounds and convergence to zero. Changing tags
preserves an existing limit under the vanishing-error and bounded-variation
hypotheses, without sign decisions or square roots. Admissible finite
sampling schemes are now defined. The affine dyadic construction described
below proves convergence for those samples; general-contour convergence and
the homotopy estimates remain to be proved.

[Geometric interval curves](../tactical/complex_curves.md) now include straight segments
with checked endpoints and constructive uniform continuity. The existing
domination estimate proves that the corresponding interval deformation
avoids zero. Joint continuity for a family of loops and the comparison with
homotopy-type paths remain open.
Ordered finite samples of these curves now have checked coordinate variation
bounds, independent of the sample count. These parameter samples are now
connected to the original contour sums: changing tags preserves an existing
limit when sampled integrand errors tend to zero. Admissibility, uniform
continuity along the curve, and a sufficiently fine mesh now imply the
finite error bounds. An arbitrary finite subdivision of one coarse interval
now has a checked error bounded by its width times the value-error tolerance
and the affine coordinate length. Per-edge subdivisions can also be flattened
to one sample list with exactly the sum of their contributions. The global
affine refinement estimate now controls the error of this actual flattened
sum by `delta * outer width * coordinate length`, without a sample-count
factor. Constructive midpoints and their admissible two-edge subdivisions
are now checked as well. Recursive bisection constructs exactly `2^n` edges
with checked width bounds. Archimedeanness then gives mere existence of
admissible samples below every positive mesh, preserving its truncation
without choice. These widths are now proved to decrease, giving fine samples
at every sufficiently deep level. Actual scalar convergence moduli are also
constructed from explicitly supplied Archimedean bound functions; extracting
such functions from the merely existential interface is not assumed.
Cross-level refinement identities now connect the actual dyadic samples.
Their sums are proved Cauchy, and supplied scalar completeness constructs a
unique affine dyadic integral. Its midpoint splitting, constant-integrand
formula and complex linearity are proved. These results do not yet establish
comparison with arbitrary fine partitions or homotopy invariance; see the
[integral construction](../tactical/complex_curves.md#constructed-affine-dyadic-integrals).

| Module | Result |
| --- | --- |
| [field_products.cubist](../../web/proofs/field_products.cubist) | Equality of pairs is determined by coordinate equalities; a product of sets is a set. |
| [complex_numbers.cubist](../../web/proofs/complex_numbers.cubist) | Coordinate carrier and operations, separated from the ring proofs so limit arguments can import them directly. |
| [ring_laws.cubist](../../web/proofs/ring_laws.cubist) | Derived ring identities, including multiplication by zero and negatives, distribution and cancellation. |
| [complex_coordinates.cubist](../../web/proofs/complex_coordinates.cubist) | Explicit proofs of the coordinate identities for complex multiplication. |
| [complex_algebra.cubist](../../web/proofs/complex_algebra.cubist) | `Complex(F) = F and F`, its commutative-ring certificate, injective real embedding, `i² = -1`, conjugation, norm square, and the inverse formula given a reciprocal of the norm square. |
| [ordered_squares.cubist](../../web/proofs/ordered_squares.cubist) | Nonnegative squares and strictly positive squares of apart-from-zero scalars, without deciding signs. |
| [complex_norm_coordinates.cubist](../../web/proofs/complex_norm_coordinates.cubist) | The polynomial identity proving multiplicativity of the squared norm. |
| [complex_inverses.cubist](../../web/proofs/complex_inverses.cubist) | Positive squared norm if and only if an inverse exists; failure of positive apartness implies zero. These results are constructive over a supplied ordered field. |
| [classical_complex_inverses.cubist](../../web/proofs/classical_complex_inverses.cubist) | An inverse from ordinary negated equality with zero, using the existing excluded-middle axiom explicitly. |
| [complex_polynomials.cubist](../../web/proofs/complex_polynomials.cubist) | Monic coefficient vectors and Horner evaluation; actual linear roots and uniqueness; a precise algebraic-closure property and its exact-square-root consequence. |
| [polynomial_difference.cubist](../../web/proofs/polynomial_difference.cubist) | A recursive polynomial expression `q` with `p(x) = p(r) + (x-r)q(x)`; hence the factor identity when `p(r) = 0`. |
| [homotopy_paths.cubist](../../web/proofs/homotopy_paths.cubist) | Naturality with moving basepoints; a null homotopy kills loops; loops in a contractible type are null. All axiom-free. |
| [circle_degree.cubist](../../web/proofs/circle_degree.cubist) | Circle power maps have their stated degree, positive degree obstructs contraction and extension through a contractible homotopy type, and the circle cannot retract from a contractible type. Uses only the single univalence axiom. |
| [complex_deformation.cubist](../../web/proofs/complex_deformation.cubist) | A dominating squared norm guarantees `z + t*q != 0` for `0 <= t <= 1`, with the correct endpoints. Uses only the truncation present in the ordered-field interface. |
| [quadratic_identities.cubist](../../web/proofs/quadratic_identities.cubist) | The scalar parallelogram identity by explicit ring rewrites, without axioms. |
| [ordered_bounds.cubist](../../web/proofs/ordered_bounds.cubist) | Constructive weak-order addition and multiplication bounds, as prerequisites for the polynomial radius estimate. |
| [complex_periods.cubist](../../web/proofs/complex_periods.cubist) | Every additive complex-valued period on the puncture homotopy type is the winding-weighted sum of its supplied local contributions. This does not construct contour integration or prove the local residue calculation. |

The ring assumptions are ordinary parameters to these theorems. For example,
`complex_commutative_ring` takes a `CommutativeRing(F, ...)` certificate and
constructs one for pairs; it does not postulate real or complex arithmetic.
The ring and coordinate modules have empty axiom dependency lists. The period
formula uses existing univalence, function extensionality, and truncation,
through the homotopy generation proof. Order and
constructive inverse results depend only on existing truncation principles;
their scalar order interfaces themselves contain truncated disjunctions. The
two explicitly classical corollaries also depend on excluded middle. No
result added here uses choice. The
algebraic-closure **property** uses propositional truncation, and its
square-root consequence uses only the existing truncation principles.

The inverse formula supplies `(a*d, -b*d)` when `(a*a+b*b)*d = 1`.
Thus `(a+bi)^(-1) = (a-bi)/(a*a+b*b)`; the denominator is the squared
norm, not its square root. With positive squared norm as input, constructing
the inverse needs neither excluded middle nor choice.
`complex_ordered_field_inverses` now discharges that premise from a supplied
ordered-field certificate and positive squared norm. Conversely, an inverse
forces positive squared norm, using norm multiplicativity and the scalar
inverse laws. Failure of positive norm forces both coordinates to vanish.
`classical_complex_nonzero_inverse` separately uses excluded middle to pass
from `z != 0` to positive apartness. Negated equality alone supplies no positive
lower bound constructively. This records the corollary's proof dependency;
it is not a claim that full excluded middle is necessary for every possible
real-number model or inverse theorem. This does not finish a concrete complete
complex field: construction of the underlying complete real field remains
open.

## Exact algebraic closure

The target `MonicAlgebraicClosure(F, ...)` says that every monic polynomial of
positive degree merely has an exact root:

```text
forall n, forall coefficients : MonicCoefficients(F, succ(n)),
  FieldExists(exists z : F, monic_eval(..., coefficients, z) = zero)
```

It is a definition of a property, **not an axiom and not a theorem that complex
numbers satisfy it**. Its restriction to monic polynomials avoids deciding
whether an arbitrary leading coefficient is zero. Normalization of a general
polynomial requires an invertible leading coefficient.

Truncated existence is intentional: this statement does not supply a function
selecting a root for every polynomial. Nor does it merely assert arbitrarily
small values of a polynomial. `algebraic_closure_implies_square_roots` checks
that even its degree-two instance entails exact square roots of arbitrary
coefficients, under truncation.

There is a real choice-sensitive issue here. Richman's
[*The fundamental theorem of algebra: a constructive development without
choice*](https://msp.org/pjm/2000/196-1/pjm-v196-n1-p10-p.pdf)
discusses the difficulty already for complex square roots and develops a
choice-free formulation using completion of root multisets. Exact roots,
approximate root multisets, and roots over Cauchy presentations must not be
silently interchanged. This is a reason to audit the chosen real construction
and logical assumptions; it is not a machine-checked independence result for
this kernel.

The primary route is now the **winding-number proof**, using the circle work
already present. It needs continuous topology and polynomial estimates, but
does not need contour integrals, the residue theorem, or Liouville. For a monic
polynomial `p(z) = z^n + q(z)` of positive degree:

1. Choose `R > 1` large enough that `|q(z)| < |z^n|` on `|z| = R`.
2. The homotopy `z^n + t*q(z)` stays away from zero on that circle. Its image
   under `p` therefore has winding `n`.
3. If `p` had no roots, `p((1-t)*R*u)` for `|u| = 1` would contract this image
   loop to `p(0)`, entirely in the punctured target plane. Its winding would
   consequently be zero, contradicting `n > 0`.

This is the argument in [Leinster's notes on the fundamental theorem of
algebra](https://webhomes.maths.ed.ac.uk/~tl/fta.pdf). For arbitrary nonzero
leading coefficient, first normalize the polynomial to be monic. Repeated
factorization after root existence gives complete splitting.

The existing `winding_positive` theorem checks the winding of the abstract
`n`-fold loop. `circle_power_degree` now lifts this to circle maps, and
`positive_degree_no_contractible_extension` proves the abstract contradiction
used in step 3. The homotopies need not fix the basepoint; naturality tracks
its motion explicitly. This result concerns a contractible **homotopy type**,
not the raw set of disk coordinates, whose identity paths are equalities.

`complex_linear_deformation_nonzero` supplies the zero-avoidance argument for
step 2: if `normSquared(q) < normSquared(z)`, then `z + t*q` cannot be zero on
the real unit interval. The proof uses `normSquared(t*q) = t*t*normSquared(q)`
and `t*t <= 1`; cancellation would contradict strict dominance. It requires
neither square roots nor excluded middle. Continuity of this family is not
yet formalized, and it is not yet specialized to polynomial coefficients.

The missing bridge is continuous planar topology: the disk's
contraction, the topological unit circle and its comparison with our homotopy
`S1`, and the leading-term estimate. The image loop represents `n` times the
generator; a degree-`n` circle map is not in general an equivalence.

The user has authorized theorem-specific choice or excluded middle when
needed, keeping the shared foundations constructive and displaying every
dependency. In this proof, the final conversion of a contradiction into mere
root existence can use excluded middle. Earlier conversions from “not zero”
to positive apartness and the topology lemmas also need an explicit audit;
they are not automatically constructive. No global choice of roots is needed
by the classical proof strategy. The constructive approximation route should
retain its own statement and assumptions.

## Great Picard

The requested target is the holomorphic version: in every punctured
neighborhood of an isolated essential singularity, every complex value with
at most one exception is attained infinitely often. The meromorphic version on the Riemann sphere has a different
exception bound and is not being substituted for this statement.

A useful intermediate formulation is that a holomorphic function on a
punctured disk which omits two distinct values cannot have an essential
singularity at the puncture. Turning this into the usual positive assertion
about infinitely many preimages also needs a logical audit. We should not
choose an exceptional value when the theorem asserts only “at most one.”

Picard requires additional analytic estimates beyond Cauchy's theorem and
residue calculations. One route uses normal families and omitted-value
estimates. Boas's [complex analysis course notes](https://haroldpboas.gitlab.io/courses/618-2015a/notes.pdf)
prove the needed Montel criterion using the modular function and the
twice-punctured plane, then deduce Great Picard. That gives a route related to
our puncture project, but requires analytic covering maps and compactness
arguments in addition to loop generation. There are currently no definitions of holomorphic functions,
isolated essential singularities, or normal families in Cubist, so there
is no checked Picard theorem yet.

## Relation to puncture homotopy

The [puncture graph results](../tactical/puncture_homotopy.md) prove loop generation and
winding facts for an abstract homotopy type. They now also prove the full
additive period formula on that type and specialize it to complex addition.
Homotopy types and their paths are the intended representation of deformation
information throughout this development. These results do not construct continuous
complex contours, prove a comparison with a punctured plane, define a contour
integral, or establish analytic bounds. Those are separate prerequisites.
In particular, a twice-punctured plane's noncommutative loop structure alone
does not imply Picard's analytic conclusion.

The separate [geometric-curve development](../tactical/complex_curves.md#constructed-affine-dyadic-integrals)
now constructs unique dyadic integral limits along affine curves from uniform
continuity, Cauchy completeness and actual Archimedean bounds. Its midpoint
splitting, constant-integrand and complex-linearity laws are proved from
finite sums and uniqueness of limits. Comparison with general partitions,
homotopy invariance and the punctured-plane comparison remain unproved.

The implementation order is therefore real-field instances and complex
inverses, polynomial estimates and continuous topology, algebraic closure by
winding, then integrals, Cauchy theory, the residue theorem and the further
analytic estimates for Great Picard. Logical dependencies must remain visible
at every stage; no theorem target is to be imported as its own axiom.
