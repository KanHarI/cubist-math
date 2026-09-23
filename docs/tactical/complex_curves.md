# Geometric complex curves

The kernel now checks straight-line curves over a supplied constructive
ordered field. These are prerequisites for geometric contour integration
and the leading-term deformation in the algebraic-closure argument. They
do not yet prove any of the three complex-analysis targets.

## Interval and continuity

`FieldUnitInterval` is the subtype of scalar coordinates `t` with `0 <= t`
and `t <= 1`. Its two endpoint constructors take a proof of `0 <= 1`,
available from the ordered-field laws. `ComplexUniformCurve` says that for
every positive epsilon there is an actual positive delta such that
delta-close parameters have epsilon-close real and imaginary coordinates.
The same delta works for all pairs of parameters.

For `gamma(t) = z + t*e`, the construction takes

```text
L = max(max(re(e), -re(e)), max(im(e), -im(e)))
delta = epsilon / (1 + L)
```

Here division means multiplication by the positive reciprocal constructed
from the ordered-field inverse law. Lattice laws prove the bounds without
a sign decision. The positive `1 + L` makes the construction valid for
constant curves as well. The kernel checks `delta > 0` and `delta*L < epsilon`.
The scalar increment identity and multiplication bounds then prove uniform
continuity, first on the entire scalar line and then on the unit interval.

| Module | Checked result |
| --- | --- |
| [field_affine](../../web/proofs/field_affine.cubist) | Canonical lattice magnitude bounds, bounds on parameter differences, the affine increment identity, and the resulting closeness estimate. |
| [field_interval](../../web/proofs/field_interval.cubist) | Closed interval parameters, their bounds, and endpoint constructors. |
| [complex_affine](../../web/proofs/complex_affine.cubist) | A canonical coordinate box and constructive uniform continuity of `z + t*e`. |
| [complex_curves](../../web/proofs/complex_curves.cubist) | Restriction to interval curves; uniform continuity and endpoints of `a + t*(-a+b)`; avoidance of zero for `z + t*e` when `normSquared(e) < normSquared(z)`. |

The continuity theorem has no supplied modulus or coordinate bound:
both are constructed. Completeness of the scalars is not needed for these
results. The only axiom dependencies are existing propositional truncation
and its introduction rule. There is no excluded middle, choice, or new
kernel operation.

## Ordered sampling and variation

The checked [variation proof](../../web/proofs/complex_curve_variation.cubist)
now constructs weights for `gamma(t) = z + t*e` on every finite ordered
sampling of the unit interval. Let `r = max(re(e), -re(e))` and
`s = max(im(e), -im(e))`. For consecutive parameters `u <= v`, the real
and imaginary increments have magnitude bounds `(v-u)*r` and `(v-u)*s`.
Their combined total is at most `r+s`, independently of the number of
samples. Repeated parameters and an empty edge list are included.

[interval_weights](../../web/proofs/interval_weights.cubist) proves the exact
telescoping identity `sum((v-u)*L) = (last-first)*L` and the upper bound
by a nonnegative `L`. [affine_variation](../../web/proofs/affine_variation.cubist)
supplies the individual magnitude estimates under `IntervalOrderedSamples`.
This ordering condition is essential: telescoping alone does not make
signed increments into magnitude bounds. The complex theorem constructs
the coordinate bounds from the lattice laws; it assumes neither a variation
certificate nor an inverse operation. Its only axiom dependency is the
existing truncation in the scalar interface.

The sample domain here is the parameter interval, retaining the association
between each sample and its parameter. Tags do not affect these weights.
The variation statement itself does not require that each integrand tag
lie between its adjacent vertices. The admissibility layer below now imposes
that condition when estimating changes in integrand values. A sequence of
refining partitions with mesh tending to zero remains to be constructed.

## Contour sums on parameter samples

[sample_maps](../../web/proofs/sample_maps.cubist) maps vertices and tags through
a curve and proves that evaluating the mapped samples agrees with evaluating
the pulled-back edge expression. [parameter_contours](../../web/proofs/parameter_contours.cubist)
defines the latter explicitly as

```text
sum(values(tag) * (curve(next) - curve(previous))).
```

When `values(t) = integrand(curve(t))`, the kernel proves equality with the
original contour sums on the mapped vertices and tags. It also proves the
exact finite change-of-tags identity. These algebraic results are axiom-free.
There is no requirement that the curve be injective: weights remain functions
of the parameters, even if the curve revisits a complex point.

[parameter_contour_bounds](../../web/proofs/parameter_contour_bounds.cubist),
[parameter_contour_estimates](../../web/proofs/parameter_contour_estimates.cubist), and
[parameter_contour_limits](../../web/proofs/parameter_contour_limits.cubist)
prove the coordinate error estimates and transfer of limits for this
parameter domain. [parameter_increment_bounds](../../web/proofs/parameter_increment_bounds.cubist)
packages the separately proved real and imaginary increment bounds for use
by those estimates.

[curve_contour_estimates](../../web/proofs/curve_contour_estimates.cubist) connects
`ComplexCurveVariation` to the finite mapped complex sums. The separate
[curve_contour_limits](../../web/proofs/curve_contour_limits.cubist) then proves
the limit-transfer results. In particular,
`affine_curve_contour_tag_independent_limit` supplies the proved variation
certificate for `z + t*e`, so no extra variation assumption appears in its
statement. If the sampled integrand errors are bounded by nonnegative
`delta(n)` tending to zero, and the sums for the old tags converge to `value`,
then the sums for the new tags converge to that same `value`. Both use the
same sequence of ordered sampled vertices.

This result transfers an existing limit. The later dyadic construction below
now supplies a Cauchy proof and a limit under explicit actual Archimedean
bounds and completeness. Arbitrary sampling schemes still need comparison
with that construction. The limit proofs use only existing truncation,
introduction, and elimination; they add
no excluded middle, choice, kernel rule, or theorem-specific axiom.

## Admissible tags and a sufficiently fine mesh

`IntervalAdmissibleTags` requires each tag's parameter to lie inclusively
between its adjacent vertices. `IntervalMeshBelow` requires every adjacent
parameter difference to be strictly less than a supplied positive threshold.
The kernel proves that admissibility implies ordered vertices. It also
constructs left- and right-endpoint tag lists and proves them admissible for
every ordered sampling, including repeated vertices and zero edges.

| Module | Checked result |
| --- | --- |
| [interval_tag_bounds](../../web/proofs/interval_tag_bounds.cubist) | Two tags in one sufficiently short interval are close. Endpoint bounds are inclusive; the mesh bound is strict. |
| [sample_tagged](../../web/proofs/sample_tagged.cubist) | Finite tag conditions and explicit endpoint tag lists with their condition proofs. |
| [interval_sampling](../../web/proofs/interval_sampling.cubist) | Admissibility, mesh conditions, the derived ordering, and admissible endpoint tags. |
| [parameter_tag_sampling](../../web/proofs/parameter_tag_sampling.cubist) | Lifts local tag estimates to the complete sampled tag-error certificate. |
| [uniform_curve_tags](../../web/proofs/uniform_curve_tags.cubist) | Uniform continuity of the sampled values produces a positive mesh threshold controlling all admissible tag errors. |
| [curve_tag_stability](../../web/proofs/curve_tag_stability.cubist) | A positive mesh threshold making any two admissible contour sums on the same vertices epsilon-close, with affine and endpoint-tag specializations. |

The estimate first constructs a positive value-error radius `delta` with
`delta*L < epsilon`. Uniform continuity of `integrand(curve(t))` supplies a
positive parameter threshold. For a finer mesh, admissible tags in each
edge satisfy that threshold, so the proved variation bound controls their
total contour error. For affine curves, `L` and its variation certificate
are constructed from the lattice bounds on the slope.

Thus `affine_contour_uniform_tag_stability` assumes uniform continuity of
the integrand along the curve, but no supplied sampled-error certificate,
variation certificate, or previously convergent tag scheme. The endpoint
corollary compares the actual constructed right- and left-endpoint sums.
These finite results depend only on existing truncation and its introduction
rule; they use neither excluded middle nor choice.

## Finite subdivisions of coarse intervals

[affine_refinement](../../web/proofs/affine_refinement.cubist) now compares one
coarse contribution with an arbitrary finite subdivision of that interval.
For `curve(t) = z + t*slope`, put

```text
L = max(re(slope), -re(slope)) + max(im(slope), -im(slope)).
```

Given uniform continuity of `integrand(curve(t))` and `delta > 0`, the theorem
`affine_refinement_uniform_estimate` constructs a positive mesh threshold.
For an interval `[a,b]` narrower than that threshold, any admissible finite
subdivision and any coarse tag `u` in `[a,b]` satisfy

```text
fine contour sum = integrand(curve(u)) * (curve(b) - curve(a)) + error
ComplexBoxBound(error, delta * ((b-a) * L)).
```

Both coordinates of the error are bounded in magnitude. The theorem supplies
the error as data and refers to the actual mapped contour sum. It assumes
neither convergence nor a supplied error or variation certificate. The
width factor is retained so that errors can later be summed across coarse
cells without multiplying the bound by their count.

The coarse tag need not belong to every fine subinterval.
[interval_refinement](../../web/proofs/interval_refinement.cubist) instead proves
that all fine tags belong to the outer interval, then uses continuity on
that common interval. [parameter_refinement](../../web/proofs/parameter_refinement.cubist)
proves that repeating the coarse tag makes the fine sum telescope exactly,
and computes the error when those repeated tags are changed to the fine tags.
[sample_refinement_tags](../../web/proofs/sample_refinement_tags.cubist) supplies
the finite containment and repeated-tag proofs. The algebraic identities use
no axioms; the affine estimate depends only on `lib_Trunc` in the scalar
order interface, without excluded middle or choice.

[sample_subdivisions](../../web/proofs/sample_subdivisions.cubist) represents a
separate subdivision for every edge of a coarse partition. Its flattening
theorem constructs one actual sample list with the same outer endpoints and
sum equal to the sum of the per-edge contributions. Adjacent pieces carry
equality witnesses for their shared endpoint; zero-edge pieces are allowed
only with equal endpoints. This theorem is axiom-free.

[affine_partition_refinement](../../web/proofs/affine_partition_refinement.cubist)
now combines these results across an entire partition. Given uniform continuity
along the affine curve and `delta > 0`, it constructs one positive mesh threshold.
For any coarse partition below that mesh, with a coarse tag in each interval
and admissible tags in each supplied subdivision, it constructs an actual
flattened subdivision and proves

```text
flattened contour sum = sum of the supplied per-edge contributions
flattened contour sum = coarse contour sum + error
ComplexBoxBound(error, delta * (outer width * L)).
```

The conclusion concerns the original mapped complex contour sums, and keeps
the equality to the supplied subdivisions. There is no factor for the number
of coarse edges or refined samples. The zero-edge case is included.
[interval_subdivisions](../../web/proofs/interval_subdivisions.cubist) states the
geometric admissibility conditions and telescopes the local radii.
[complex_subdivision_estimates](../../web/proofs/complex_subdivision_estimates.cubist)
constructs and adds the error witnesses using
[complex_perturbations](../../web/proofs/complex_perturbations.cubist).
[sample_subdivision_conditions](../../web/proofs/sample_subdivision_conditions.cubist)
maps finite families of conditions, without choice or truncating their witnesses.
The global affine estimate depends only on the existing `lib_Trunc` in the
order interface.

[interval_bisection](../../web/proofs/interval_bisection.cubist) now constructs a
midpoint between any weakly ordered interval endpoints. Both new widths are
proved equal to half the original width, including degenerate intervals.
It builds the actual two-edge subdivision and verifies its left endpoint
tags. The ordered-field theorem supplies halving from the inverse of two;
there is no supplied midpoint oracle or choice assumption. Its additional
truncation introduction/elimination dependencies come from that existing
halving construction.
[sample_join_conditions](../../web/proofs/sample_join_conditions.cubist) proves
that concatenating subdivisions with matching endpoints preserves their tag
conditions, including empty prefixes and suffixes. This axiom-free result
will keep the samples admissible when the bisections are iterated.

Here **dyadic** means repeated halving: one interval becomes two, then four,
then eight. The unit parameter interval has width `1 / 2^n` at level `n`.
These are subdivisions of the curve's parameter, not equal arc-length pieces.
Their contour sums sample the integrand on each small interval and multiply
by the curve's complex displacement across that interval.

[dyadic_sampling](../../web/proofs/dyadic_sampling.cubist) now recursively bisects
both half-intervals and joins their samples. At depth `n` the result has
exactly `2^n` edges, admissible tags, and every edge's width is bounded by
`n` halvings of the original width. Empty-width intervals are included.
[dyadic_mesh](../../web/proofs/dyadic_mesh.cubist) converts this weak width bound
into the existing strict mesh predicate whenever the scalar bound is smaller
than the requested mesh. Its condition maps preserve the actual sample data.

[dyadic_width_bounds](../../web/proofs/dyadic_width_bounds.cubist) proves
`(n + 1) * refined_width <= original_width`.
[dyadic_decay](../../web/proofs/dyadic_decay.cubist) combines that estimate with
positive reciprocals and Archimedeanness to prove that arbitrarily small
dyadic widths merely exist. No excluded middle or choice is used.
[fine_interval_samples](../../web/proofs/fine_interval_samples.cubist) then proves
that every weakly ordered interval has admissible dyadic samples below any
positive mesh, again with mere existence. Midpoints, tags, widths and counts
are derived; no partition oracle is an input.

The truncation is deliberate: `Archimedean` supplies a merely existing natural
bound. This result does not select a natural modulus for each mesh. The
existing `FieldCauchy` interface asks for actual moduli, so using it will need
an explicit modulus or a separately justified conversion. The proof never
eliminates a truncation directly into the sampling data.

[dyadic_tails](../../web/proofs/dyadic_tails.cubist) proves that these widths
decrease with the natural index. Once a width is below a tolerance, every
later width remains below it. Archimedeanness therefore gives a merely
existing bound for the entire tail, not just one small sample.
[fine_interval_tails](../../web/proofs/fine_interval_tails.cubist) constructs
admissible samples below the requested mesh at every later level. The family
comes from recursive bisection, so no choice of samples is needed.

[dyadic_convergence](../../web/proofs/dyadic_convergence.cubist) also checks actual
`FieldConverges` convergence of the scalar widths to zero when an
`ArchimedeanBounds` function is supplied. That stronger datum returns an
actual natural witness for each field element; it is explicitly separate
from `Archimedean`. The modulus uses a bound for `width / epsilon`.
With ordinary Archimedeanness, only the per-tolerance tail existence is
claimed. These lemmas introduce neither excluded middle nor choice.

Joining refinement families is now checked in
[subdivision_join](../../web/proofs/subdivision_join.cubist): the actual per-edge
subdivisions concatenate with an exact identity for their ordered sum.
[Endpoint transport](../../web/proofs/subdivision_transport.cubist) and
[condition preservation](../../web/proofs/subdivision_join_conditions.cubist)
handle the dependent endpoint types without assuming equality of their
proofs. [subdivision_refinement](../../web/proofs/subdivision_refinement.cubist)
combines two such refinement certificates when both the coarse and fine
halves are joined. These results are axiom-free and require no commutativity
of the sum. The certificate identifies sums for the specified edge function;
it does not identify arbitrary sample lists merely because their sums agree.

[dyadic_data](../../web/proofs/dyadic_data.cubist) exposes the actual recursively
constructed samples, with checked equations for the initial edge and the
join of two sampled halves. The data-producing definitions are transparent
so these equations compute. The midpoint and its bounds are projections
of the same constructed witness, not independently chosen points.
[dyadic_refinement](../../web/proofs/dyadic_refinement.cubist) now proves that
level `n + k` refines level `n`: it constructs the per-edge subdivisions,
proves their tags are admissible, and identifies their ordered total with
the actual finer sum. This holds for any monoid-valued edge function;
commutativity, excluded middle, and choice are not required.

[subdivision_tagged_zip](../../web/proofs/subdivision_tagged_zip.cubist) combines
coarse-edge bounds and admissibility of the actual per-edge refinements.
[dyadic_refinement_mesh](../../web/proofs/dyadic_refinement_mesh.cubist) applies
this to obtain the mesh hypotheses required by the analytic estimates.
[curve_refinement_estimates](../../web/proofs/curve_refinement_estimates.cubist)
transfers an estimate for a constructed flattening to the specified fine
samples, using their exact sum identity rather than identifying sample lists.

[dyadic_contour_estimates](../../web/proofs/dyadic_contour_estimates.cubist) now
proves an actual cross-level bound: for a uniformly continuous integrand along
an affine curve, each positive `delta` supplies one positive mesh such that
all dyadic levels `n` meeting that mesh and all refinements `n + k` differ by
a `ComplexPerturbation` bounded by `delta * outerWidth * coordinateLength`.
The bound is independent of both sample counts. This remains a finite-sum
estimate, with the supplied field and continuity assumptions explicit.

## Constructed affine dyadic integrals

[complex_refinement_cauchy](../../web/proofs/complex_refinement_cauchy.cubist)
proves the common-refinement argument: compare levels `m` and `n` through
`m + n`, using half the requested tolerance for each comparison. The resulting
bound is an actual natural number, as required by `ComplexCauchy`.

[affine_dyadic_limits](../../web/proofs/affine_dyadic_limits.cubist) applies this
to the actual sums, using the proved mesh estimate and dyadic width decay.
It requires `ArchimedeanBounds`, which supplies actual natural witnesses;
the merely existential `Archimedean` field property is not silently strengthened.
Uniform continuity supplies a mesh for the requested integrand error, and
the natural bound for the shrinking width supplies the sampling index.
Zero segment length is covered without deciding whether it is zero.

[affine_integrals](../../web/proofs/affine_integrals.cubist) then applies
`CauchyComplete` coordinatewise to construct `affine_dyadic_integral`, proves
its convergence and uniqueness, and proves that changing the witnesses for
inverses, Archimedean bounds, uniform continuity or completeness leaves the
value unchanged. No convergence assumption about the sums appears as an input
to this construction. No excluded middle, choice, or new kernel rule is used.

[affine_integral_midpoint](../../web/proofs/affine_integral_midpoint.cubist)
proves that the integral from `a` to `b` is the sum of the integrals over its
two constructed half-intervals, along the same affine curve. It uses the exact
finite join equation from [curve_sample_sums](../../web/proofs/curve_sample_sums.cubist)
and uniqueness of limits; it does not assume additivity of integrals.

[affine_integral_constants](../../web/proofs/affine_integral_constants.cubist)
proves the normalization formula: integrating a constant `c` gives
`c * (curve(b) - curve(a))`. Constant uniform continuity is constructed, and
the finite sums already have exactly this value by telescoping. Uniqueness
identifies their constructed integral with it.

[affine_integral_linearity](../../web/proofs/affine_integral_linearity.cubist)
proves additivity in the integrand, multiplication by a fixed complex scalar,
and equality of integrals when the integrands agree along the curve. The sum
and scaled integrands receive constructed continuity witnesses; those
properties are not extra hypotheses. The proof uses the corresponding
finite identities in [curve_integrand_sums](../../web/proofs/curve_integrand_sums.cubist)
and uniqueness of limits. Equality along the curve needs no equality of the
whole functions and no function-extensionality axiom.

[field_uniform_radii](../../web/proofs/field_uniform_radii.cubist) constructs a
common positive input tolerance without choosing the smaller of two numbers:
for positive `r,s`, choose positive `delta` with `delta*(r+s) < r*s` and cancel
the positive factor `r+s` to bound `delta` by both. This supports
[addition of uniformly continuous curves](../../web/proofs/complex_uniform_operations.cubist).
[Scalar continuity](../../web/proofs/complex_scalar_continuity.cubist) uses
coordinate magnitude bounds and the positive denominator in the existing
scaled-radius construction, so it includes the zero coefficient without
a zero test. It also proves preservation of convergence under fixed complex
scalar multiplication. All these moduli are actual witnesses and introduce
no excluded middle or choice.

This constructs the unique limit of the specified dyadic samples. Comparison
with arbitrary fine partitions, splitting at arbitrary points, reversal,
and homotopy invariance remain to be proved. Actual moduli from the existing
merely existential Archimedean interface still require a separate bridge or
a concrete bound construction, and concrete complete-field models remain
unfinished.

## Relationship to homotopy paths

`Complex(F)` is a set of coordinates. Its identity types alone do not give
the geometric paths around a puncture. Likewise, the interval subtype above
is parameter data, not an assertion that its identity paths form a
contractible interval.

The intended topological targets remain paths and loops in the existing
homotopy types. These continuous functions supply geometric representatives.
We still need to construct their comparison with those paths and prove the
coverage and compatibility properties needed by
[homotopy descent](analysis_limits.md). This development adds no axiom
asserting such a comparison.

Uniform continuity here varies `t` with `z` and `e` fixed. A homotopy of
entire loops needs continuity also in the loop parameter, which remains to
be proved. We also still need convergence and homotopy
estimates for the chosen integrands, and the local integral
calculation in the residue theorem.
