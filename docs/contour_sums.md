# Finite contour sums and homotopy paths

These are checked finite approximations for the contour-integral development.
They do not yet construct an integral, prove Cauchy's theorem, or discharge
the analytic premises of the residue theorem. The ring or ordered field is
an explicit parameter; the concrete real-field constructions remain incomplete.

## What the finite data represents

`SampleVertices(C, n)` contains `n+1` vertices, and `SampleTags(C, n)` contains
`n` sample points. `sample_sum` evaluates a supplied edge function on each
successive pair of vertices and its tag, then adds the results. Concatenation
joins two such chains at a common endpoint.

For a commutative ring, `contour_sum` is the usual algebraic expression

\[
  S(f;z,t)=\sum_{j=0}^{n-1} f(t_j)(z_{j+1}-z_j).
\]

The tags are currently arbitrary. A geometric sampling scheme must still
specify an actual curve, a partition, tags on the corresponding subarcs,
and a mesh tending to zero. A vertex list does not itself supply these facts.

Topological paths remain identity paths in a homotopy type. In particular,
the puncture development uses loops in `PunctureGraph(n)`, constructed using
the existing suspension infrastructure. Finite samples provide numerical
approximations on curve representatives. The
[homotopy-descent proofs](analysis_limits.md) explain how their limits can
define periods on those identity loops once the geometric comparison and
analytic estimates are proved. Identity paths in the set of complex
coordinates itself cannot encode the topology of the punctured plane.

## Checked laws

| Module | Results |
| --- | --- |
| [sample_chains](../web/proofs/sample_chains.proof) | Vertices, tags, finite edge sums, and concatenation with endpoint laws. |
| [sample_sum_laws](../web/proofs/sample_sum_laws.proof) | Additivity under matched concatenation, pointwise congruence, addition and additive maps, and telescoping. |
| [contour_samples](../web/proofs/contour_samples.proof) | Contour-sum definitions and oriented-increment identities, available without importing the later sum theorems. |
| [contour_sums](../web/proofs/contour_sums.proof) | Ring-valued contour sums, linearity in the integrand, and the constant-integrand formula `c * (last - first)`. Potential differences telescope; this is an algebraic identity, not a fundamental theorem of calculus. |
| [contour_refinement](../web/proofs/contour_refinement.proof) | Exact changes under replacement of tags and splitting an edge; accumulated tag-error identity. |
| [contour_examples](../web/proofs/contour_examples.proof) | Backtracking cancels with equal tags, and its error is explicit with different tags. A nonzero coarse sum on a closed chain is calculated. |
| [sample_error_bounds](../web/proofs/sample_error_bounds.proof) | Pointwise scalar error bounds at the sampled edges accumulate into a bound on the total sum. |
| [complex_contour_sums](../web/proofs/complex_contour_sums.proof) | Complex specialization: composition, zero for a closed constant-integrand sum, and the nonzero backtracking example. |

Writing `E(a,b,t) = f(t)(b-a)`, the tag-error identity is

\[
 E(a,b,t')=E(a,b,t)+(f(t')-f(t))(b-a).
\]

Splitting at `m` with the same tag preserves the sum exactly. With new tags,
the refined sum equals the coarse sum plus the two corresponding tag errors.
The identity alone does not bound those errors or establish convergence.

`sample_sum_error_bound` requires bounds only at the finitely visited samples.
If each edge error is strictly within its radius, the total is within the
sum of radii plus any positive `epsilon`. That slack also covers an empty
sum: `FieldClose(0, 0, 0)` would require the false strict inequality `0 < 0`.
The result applies separately to real and imaginary coordinates when their
edge bounds are supplied.

## Quantitative variation estimates

`FieldMagnitudeBound(x, r)` means `x <= r` and `-x <= r`. It does not
decide a sign or require an absolute-value operation. The
[field_magnitude](../web/proofs/field_magnitude.proof) proofs show that these
bounds imply `0 <= r`, are preserved by negation, add under addition, and
multiply under multiplication. The product proof is constructive: to refute
a putative violation, a negative factor can first be ruled out, yielding
the weak nonnegativity needed for ordered multiplication. No sign case
split is assumed.

[sample_magnitude_bounds](../web/proofs/sample_magnitude_bounds.proof) proves
that finite magnitude bounds add, including for the empty sum. If sampled
errors have magnitude at most `delta`, the increments have bounds `w_j`,
`delta >= 0`, and `sum w_j <= L`, the weighted error satisfies

\[
 \left|\sum_j e_j d_j\right|\leq\delta L.
\]

The notation here abbreviates the two weak inequalities, not a newly
postulated absolute-value function. Bounds are required only at sampled
edges, using [SampleMagnitudeBounds](../web/proofs/sample_magnitude.proof).

[contour_error_bounds](../web/proofs/contour_error_bounds.proof) applies this
kind of estimate directly to changes of scalar contour tags. Its hypotheses
bound `f(newTag_j)-f(oldTag_j)` by `delta` and each displacement by `w_j`.
It proves that the exact accumulated tag error has magnitude at most
`delta * sum w_j`, and hence at most `delta * L` under the variation bound.

[field_magnitude_close](../web/proofs/field_magnitude_close.proof) connects
weak magnitude bounds to the existing strict `FieldClose` relation when
the radius is strictly smaller than the requested tolerance. It also proves
a squeeze theorem: errors bounded by radii converging to zero themselves
converge to zero, with the same supplied tail indices.

[contour_tag_limits](../web/proofs/contour_tag_limits.proof) proves closeness
of the actual old and new scalar sums whenever `delta * L < epsilon`.
For a sequence of sampling data, it proves convergence of the tag errors
to zero **given convergence of `delta_n * L` to zero** and the corresponding
sample bounds. Over ordered fields, `contour_tag_errors_from_vanishing_values`
now derives this from `delta_n -> 0` and `L >= 0`.

[field_scale_limits](../web/proofs/field_scale_limits.proof) supplies that
scaling result constructively. For each positive tolerance `epsilon`, it
uses the reciprocal of `1+L` to construct a positive `delta` with
`delta*L < epsilon`. This also works at `L=0`. The supplied ordered-field
inverse interface gives the reciprocal from its positive apartness; no
choice of a witness from mere existence is made. Multiplication by any
fixed scalar with a supplied magnitude bound then preserves convergence
to zero.

These results do not yet construct a sampling scheme, deduce its rate from
uniform continuity, or prove convergence of the sums themselves. Those
analytic obligations remain explicit.

[complex_magnitude](../web/proofs/complex_magnitude.proof) supplies the
coordinate estimate needed for the complex version: if both coordinates
of `z` have magnitude at most `delta`, and the coordinates of `w` have
bounds `r, s`, both coordinates of `z*w` have bounds `delta*(r+s)`.
Thus coordinate variation can be used without square roots. This product
estimate feeds the assembled complex results below.

## Complex tag-independent limits

[complex_contour_bounds](../web/proofs/complex_contour_bounds.proof) proves
that both coordinates of the complex tag-error sum are bounded by

\[
 \delta\sum_j(r_j+s_j),
\]

where `r_j, s_j` bound the real and imaginary displacements of the sampled
edge. The condition is checked only at the visited samples. A bound `L`
on this total coordinate variation gives the common radius `delta*L`.

[complex_contour_tag_limits](../web/proofs/complex_contour_tag_limits.proof)
proves closeness of the actual complex sums under that radius bound, and
convergence of the complex tag errors to zero when `delta_n -> 0`.
`complex_contour_tag_independent_limit` then proves that a new choice of
tags converges to the same complex value as the old choice, provided:

- both choices use the same sequence of sampled vertices;
- coordinate variation has a fixed nonnegative bound `L`;
- the sampled changes of the integrand are bounded by nonnegative
  `delta_n` tending to zero;
- the old sums already converge to the stated value.

It proves independence under these estimates, not existence of an integral
or independence between arbitrary partitions. The field and convergence
data remain explicit parameters. The next geometric work must produce
admissible partitions, relate different refinements, and derive the error
moduli from continuity.

The complex convergence definitions live in
[complex_convergence](../web/proofs/complex_convergence.proof), and the finite
complex sum definition lives in
[complex_contour_samples](../web/proofs/complex_contour_samples.proof).
This allows estimates to import their definitions without the later
completeness and example proofs.

## Why the homotopy step comes after the limit

For `f(z)=z`, vertices `0 -> 1 -> 0`, and left-endpoint tags `0, 1`, the
finite sum is

\[
 0(1-0)+1(0-1)=-1.
\]

The kernel checks this value and its nonzeroness in a nontrivial ring,
including complex coordinates. With equal tags, the backtracking sum is zero.
Thus these approximations must not be assigned to a homotopy loop as though
they were already homotopy invariant. We must prove that the appropriate
refinement errors vanish, take limits, and descend the resulting values.

## Dependencies and remaining work

The algebraic results use no axioms. The ordered magnitude and finite error-bound
results depend only on the existing `lib_Trunc` among the kernel's axiom
bindings. Fixed-factor scaling also uses truncation introduction to supply
positive apartness. The complex limit-independence proof inherits truncation
elimination from constructive halving. Their order, inverse, and arithmetic
laws are explicit hypotheses. No excluded middle, choice,
new kernel rule, or new theorem-specific axiom is used.

[Geometric curves](complex_curves.md) now include uniformly continuous
straight segments with checked endpoints and coordinate variation bounds
for ordered interval sampling. These parameter samples now map to the
original complex contour sums, with a checked transfer of an existing limit
under vanishing tag errors. Uniform continuity along the curve now gives a
positive mesh threshold controlling changes between admissible tags, with
explicit left- and right-endpoint schemes. For an affine curve, an arbitrary
finite subdivision of one coarse interval now has a width-scaled error bound,
derived from continuity and tag admissibility. Per-edge subdivisions also
flatten to one actual sample list with a checked sum identity. The global
affine refinement theorem now sums those errors and telescopes their radii
to `delta * outer width * coordinate length`, independent of the number of
samples; see [finite subdivisions](complex_curves.md#finite-subdivisions-of-coarse-intervals).
Still needed are compatible sampling schemes and their vanishing
mesh control, Cauchy and
homotopy estimates for the integrands in question, comparison with
the puncture homotopy type, and the local generator integral `2*pi*i*residue`.
The full residue theorem, algebraic closure, and Great Picard remain open.
