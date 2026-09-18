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
be proved. We also still need admissible sampling, variation and convergence
estimates for the chosen curves and integrands, and the local integral
calculation in the residue theorem.
