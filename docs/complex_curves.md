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
| [field_affine](../web/proofs/field_affine.proof) | Canonical lattice magnitude bounds, bounds on parameter differences, the affine increment identity, and the resulting closeness estimate. |
| [field_interval](../web/proofs/field_interval.proof) | Closed interval parameters, their bounds, and endpoint constructors. |
| [complex_affine](../web/proofs/complex_affine.proof) | A canonical coordinate box and constructive uniform continuity of `z + t*e`. |
| [complex_curves](../web/proofs/complex_curves.proof) | Restriction to interval curves; uniform continuity and endpoints of `a + t*(-a+b)`; avoidance of zero for `z + t*e` when `normSquared(e) < normSquared(z)`. |

The continuity theorem has no supplied modulus or coordinate bound:
both are constructed. Completeness of the scalars is not needed for these
results. The only axiom dependencies are existing propositional truncation
and its introduction rule. There is no excluded middle, choice, or new
kernel operation.

## Ordered sampling and variation

The checked [variation proof](../web/proofs/complex_curve_variation.proof)
now constructs weights for `gamma(t) = z + t*e` on every finite ordered
sampling of the unit interval. Let `r = max(re(e), -re(e))` and
`s = max(im(e), -im(e))`. For consecutive parameters `u <= v`, the real
and imaginary increments have magnitude bounds `(v-u)*r` and `(v-u)*s`.
Their combined total is at most `r+s`, independently of the number of
samples. Repeated parameters and an empty edge list are included.

[interval_weights](../web/proofs/interval_weights.proof) proves the exact
telescoping identity `sum((v-u)*L) = (last-first)*L` and the upper bound
by a nonnegative `L`. [affine_variation](../web/proofs/affine_variation.proof)
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

[sample_maps](../web/proofs/sample_maps.proof) maps vertices and tags through
a curve and proves that evaluating the mapped samples agrees with evaluating
the pulled-back edge expression. [parameter_contours](../web/proofs/parameter_contours.proof)
defines the latter explicitly as

```text
sum(values(tag) * (curve(next) - curve(previous))).
```

When `values(t) = integrand(curve(t))`, the kernel proves equality with the
original contour sums on the mapped vertices and tags. It also proves the
exact finite change-of-tags identity. These algebraic results are axiom-free.
There is no requirement that the curve be injective: weights remain functions
of the parameters, even if the curve revisits a complex point.

[parameter_contour_bounds](../web/proofs/parameter_contour_bounds.proof),
[parameter_contour_estimates](../web/proofs/parameter_contour_estimates.proof), and
[parameter_contour_limits](../web/proofs/parameter_contour_limits.proof)
prove the coordinate error estimates and transfer of limits for this
parameter domain. [parameter_increment_bounds](../web/proofs/parameter_increment_bounds.proof)
packages the separately proved real and imaginary increment bounds for use
by those estimates.

[curve_contour_estimates](../web/proofs/curve_contour_estimates.proof) connects
`ComplexCurveVariation` to the finite mapped complex sums. The separate
[curve_contour_limits](../web/proofs/curve_contour_limits.proof) then proves
the limit-transfer results. In particular,
`affine_curve_contour_tag_independent_limit` supplies the proved variation
certificate for `z + t*e`, so no extra variation assumption appears in its
statement. If the sampled integrand errors are bounded by nonnegative
`delta(n)` tending to zero, and the sums for the old tags converge to `value`,
then the sums for the new tags converge to that same `value`. Both use the
same sequence of ordered sampled vertices.

This transfers an existing limit; it does not prove that either scheme is
Cauchy in the first place. The admissibility and mesh estimates below now
supply finite integrand bounds; refining partitions and the Cauchy proof
remain to be constructed. The limit
proofs use only existing truncation, introduction, and elimination; they add
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
| [interval_tag_bounds](../web/proofs/interval_tag_bounds.proof) | Two tags in one sufficiently short interval are close. Endpoint bounds are inclusive; the mesh bound is strict. |
| [sample_tagged](../web/proofs/sample_tagged.proof) | Finite tag conditions and explicit endpoint tag lists with their condition proofs. |
| [interval_sampling](../web/proofs/interval_sampling.proof) | Admissibility, mesh conditions, the derived ordering, and admissible endpoint tags. |
| [parameter_tag_sampling](../web/proofs/parameter_tag_sampling.proof) | Lifts local tag estimates to the complete sampled tag-error certificate. |
| [uniform_curve_tags](../web/proofs/uniform_curve_tags.proof) | Uniform continuity of the sampled values produces a positive mesh threshold controlling all admissible tag errors. |
| [curve_tag_stability](../web/proofs/curve_tag_stability.proof) | A positive mesh threshold making any two admissible contour sums on the same vertices epsilon-close, with affine and endpoint-tag specializations. |

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

The two tag schemes still share the same sampled vertices. This does not yet
compare different partitions or prove a Cauchy sequence of sums. We still
need refinements, their geometric bounds, and a construction of the initial
integral limit before proceeding to homotopy invariance and local residues.

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
be proved. We also still need admissible refinements, convergence
estimates for the chosen integrands, and the local integral
calculation in the residue theorem.
