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

The algebraic results use no axioms. The scalar error-bound result depends
only on the existing `lib_Trunc` among the kernel's axiom bindings; its order
and arithmetic laws are explicit hypotheses. No excluded middle, choice,
new kernel rule, or new theorem-specific axiom is used.

Still needed are geometric curves and admissible refinements, quantitative
Cauchy and homotopy estimates for the integrands in question, comparison with
the puncture homotopy type, and the local generator integral `2*pi*i*residue`.
The full residue theorem, algebraic closure, and Great Picard remain open.
