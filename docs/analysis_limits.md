# Limits and homotopy periods

These are checked prerequisites for contour integration, not a construction
of the contour integral or proofs of the residue theorem, algebraic closure,
or Great Picard. The scalar complete ordered field remains a parameter;
concrete real-field constructions are still incomplete.

## Checked limit results

`ordered_halves` constructs a positive halving operator from the ordered-field
laws and the inverse of `1+1`. It never decides the sign of an arbitrary real.
The proof that a half of a positive number is positive uses the constructive
positive-sum law and eliminates its truncated alternative into an order
proposition.

`field_closeness` proves the triangle inequality, addition of error bounds,
and separation for the existing two-sided order balls `FieldClose`.
`field_limits` proves uniqueness of limits, addition of convergent and Cauchy
sequences, and that convergence implies Cauchyness. Bounds are actual natural
numbers and are combined by addition; countable choice is not used.

`cauchy_ordered` uses these results to discharge `CloseComposition` and the
self-closeness premise of the existing Cauchy equivalence relation over a
supplied small ordered field. Rational arithmetic and the quotient's full
field/completeness certificates are still missing.

`complex_limits` uses coordinate balls for complex numbers. It proves that
common-bound convergence and Cauchyness are equivalent to their coordinate
versions, constructs complex limits from scalar Cauchy completeness, and
proves uniqueness and addition. Its completeness theorem uses no axioms:
it applies the supplied scalar completeness function twice and combines the
bounds explicitly. This does not assert that a concrete real model already
satisfies that interface.

The coordinate definitions and operations now live in `complex_numbers`;
`complex_algebra` imports them and proves their ring laws. Analytic arguments
can use the coordinates without checking unrelated multiplication identities.

## Taking limits before passing to homotopy paths

Finite approximations to an integral need not be invariant under a homotopy.
The analytic construction must therefore take limits on representative curves
and then descend those values to the homotopy type's identity paths.

`FieldAsymptotic` asserts arbitrary eventual closeness with **mere** existence
of each eventual bound. `field_asymptotic_limits_equal` proves equality of
limits from this property. It does not extract a function choosing those
bounds. Truncation is eliminated only into propositions.

`surjective_descent` gives the general descent construction. Given a merely
surjective presentation `C -> B` and a set-valued function on `C` constant on
its fibers, it constructs a function on `B` with the required computation
law. The target `B` need not be a set. The unique value over each point forms
a proposition, so it can be obtained from mere coverage without choosing a
representative or using the axiom of choice.

`homotopy_limit_descent` applies this to `B = (point = point)`, the actual loop
space of a homotopy type. Its input is a family of Cauchy approximations on
representatives `C`, with asymptotically equal approximations whenever the
representatives describe equal homotopy paths. The resulting period has the
correct limit on every representative.

`homotopy_limit_period` also proves the unit and concatenation laws from
vanishing constant-loop and concatenation errors on representatives. It
constructs a period satisfying `LoopMapLaws`, the interface consumed by the
[puncture period formula](puncture_homotopy.md). Geometric presentation,
coverage, Cauchy estimates, and homotopy/concatenation error estimates remain
explicit obligations. No contour integral, geometric comparison, or Cauchy
theorem is assumed as an axiom.

The simpler `limit_periods` and `complex_limit_periods` results apply when
approximations are already indexed by homotopy loops. They prove limiting
period laws and independence under asymptotically equivalent schemes; the
complex result combines two scalar periods. They do **not** require finite
concatenation errors to vanish exactly. For general contour approximations,
use the representative-based descent above rather than assuming finite-stage
homotopy invariance.

## Logical dependencies and remaining work

No kernel operations, excluded middle, or choice were added. The order and
limit results use the existing truncation principles where listed in the UI.
Descent also uses existing function extensionality to prove that its
value-certification predicate is a proposition. The Cauchy equivalence
wrapper inherits the earlier quotient development's function-extensionality
and truncation dependencies. No new theorem-specific axiom was declared.

[Finite contour sums](contour_sums.md) now have checked composition,
telescoping, refinement-error identities, and accumulation of scalar error
bounds. The scalar tag-error estimate is `delta * L` for uniform sampled
error `delta` and a bound `L` on the sum of edge magnitudes. Convergence of
these bounds to zero implies convergence of the tag errors to zero.
Fixed-factor scaling now derives this from `delta_n -> 0` when `L >= 0`.
The complex coordinate version proves the same bound and preserves the
limit when changing tags under those estimates; convergence for the
original tags is still an input.
Their Cauchy and deformation estimates still need to be proved,
alongside a justified geometric presentation of the homotopy paths.
Local generator integrals and the normalization `2*pi*i`
still need to be constructed and calculated. These obligations remain part
of the full residue-theorem goal; the real models and the separate algebraic
closure and Great Picard obligations also remain open.
