# Complex analysis: paused development checkpoint

Updated 2026-09-19. Development is paused at the user's request. Resume only
when requested; the three original goals remain unfinished:

1. Algebraic closure of the complex plane (exact roots).
2. The residue theorem, using homotopy types and their paths for the
   topological part of the argument.
3. Great Picard for holomorphic functions near an isolated essential
   singularity.

**None of these three theorems has been proved.** The latest completed work
constructs integrals along affine curves by taking limits of actual dyadic
contour sums and proves their elementary laws. It is conditional on explicit
scalar-field certificates; no concrete complete real-field instance has yet
been constructed.

## Where to start reading

| Document | Scope |
| --- | --- |
| [Complex analysis overview](complex_analysis.md) | Algebra, inverse assumptions, exact algebraic-closure target, winding strategy, Picard strategy. |
| [Geometric curves and integration](complex_curves.md#constructed-affine-dyadic-integrals) | The latest approximation estimates and constructed integral. |
| [Finite contour sums](contour_sums.md) | Sampling data, concatenation, telescoping and error bounds. |
| [Limits and descent](analysis_limits.md) | Passing from limits on geometric representatives to functions on actual homotopy paths. |
| [Puncture homotopy](puncture_homotopy.md) | Loop generation, winding and the abstract period formula. |
| [Real-number development](reals.md) | Shared field interfaces and the unfinished concrete constructions. |

The proof sources are in `web/proofs/`. `web/mathscript/modules.mjs` registers
imports for the browser; `web/proof-library.mjs` registers the proof selector
and its topics. The main regression coverage is in
`tests/mathscript.test.mjs`.

## What is actually checked

### Algebra and the winding obstruction

`complex_algebra` constructs the commutative-ring laws for `Complex(F) = F × F`
from the scalar ring laws. Conjugation, squared norm and conditional inverses
are proved. `complex_inverses` constructs inverses from positive apartness;
`classical_complex_inverses` separately uses excluded middle to obtain an
inverse from ordinary negated equality with zero.

`complex_polynomials` defines monic polynomial evaluation and the exact-root
property `MonicAlgebraicClosure`, and proves the linear case.
`polynomial_difference` proves the polynomial difference/factor identity.
Defining the algebraic-closure property does not prove it for `Complex(F)`.

`circle_degree` proves the degree of abstract circle power maps and that a
positive-degree map cannot extend through a contractible homotopy type.
`complex_deformation` proves zero avoidance of `z + t*q` under strict
squared-norm domination. The geometric circle/disk comparison and the
polynomial leading-term radius estimate are still missing.

### The homotopy portion of the residue argument

The puncture development proves loop generation by signed generator words
and the winding-weighted formula for additive periods. `complex_periods`
specializes that formula to complex addition and supplied local values.
It does not identify those values with integrals or residues.

`surjective_descent`, `homotopy_limit_descent` and `homotopy_limit_period`
provide the route from geometric representatives to the actual identity
paths in the homotopy model. They require coverage, convergence, and the
appropriate vanishing homotopy and concatenation errors. Those analytic
hypotheses have not all been discharged.

**Keep the distinction:** `Complex(F)` is a set of coordinates. Its identity
types express equality, not continuous paths around poles. The continuous
interval curves constructed so far are geometric representatives; their
comparison with paths in the punctured-plane homotopy model is unfinished.
Do not postulate that comparison or assume finite quadrature sums are
homotopy invariant.

### Actual affine integrals

For a curve `γ(t) = z + t*slope` and a uniformly continuous composite
`f ∘ γ`, the construction uses finite tagged samples obtained by recursive
midpoint bisection. At depth `n` there are exactly `2^n` edges. A dyadic
width is the result of halving the original width `n` times.

The proof chain is:

1. Construct the sample data, with endpoint, order, tag and width evidence.
2. Relate the actual sums at levels `n` and `n+k` through refinement
   certificates. These certify equality of sums; they do not infer equality
   of sample lists from equality of sums.
3. Bound the refinement error by the integrand tolerance times the outer
   interval width times the affine coordinate length. The bound has no
   sample-count factor.
4. Use actual Archimedean bounds to construct an index after which the mesh
   is sufficiently small. Compare two levels through a common refinement
   to prove the actual sequence is Cauchy.
5. Apply the supplied scalar Cauchy completeness coordinatewise. This
   constructs the complex limit and proves its uniqueness.

Important source entry points:

| Modules | Checked result |
| --- | --- |
| `interval_midpoint_data`, `dyadic_sampling`, `dyadic_data` | Computational midpoint and sample data, exact edge counts and width bounds. |
| `subdivision_refinement`, `dyadic_refinement`, `dyadic_refinement_mesh` | Actual coarse/fine sum certificates and mesh conditions. |
| `curve_refinement_estimates`, `dyadic_contour_estimates` | Uniform bounds comparing actual contour sums at different levels. |
| `dyadic_convergence`, `complex_refinement_cauchy`, `affine_dyadic_limits` | Width decay with a modulus and Cauchyness of the actual affine sums. |
| `affine_integrals` | `affine_dyadic_integral`, convergence, uniqueness and independence from supplied continuity/completeness/inverse/Archimedean witnesses. |
| `curve_sample_sums`, `affine_integral_midpoint` | Finite concatenation and splitting the constructed integral at its canonical midpoint. |
| `affine_integral_constants` | Integral of a constant `c` is `c * (γ(b) - γ(a))`. |

The independence theorem does **not** yet compare arbitrary sampling schemes,
different halving operations, or every possible choice of field-law evidence.
Midpoint splitting does not yet give splitting at an arbitrary point.

### Latest batch: complex linearity

These five modules are included in this checkpoint and in the web selector:

| Module | Checked result |
| --- | --- |
| [field_uniform_radii](../web/proofs/field_uniform_radii.proof) | Enlarge a closeness radius; construct a common positive radius below two given positive radii without comparing them. |
| [complex_uniform_operations](../web/proofs/complex_uniform_operations.proof) | Add complex error bounds and construct a uniform-continuity witness for a sum of curves. |
| [complex_scalar_continuity](../web/proofs/complex_scalar_continuity.proof) | Fixed complex multiplication preserves closeness, uniform continuity and convergence; the coefficient may be zero. |
| [curve_integrand_sums](../web/proofs/curve_integrand_sums.proof) | Finite contour-sum addition, scaling and equality when integrands agree along the curve. |
| [affine_integral_linearity](../web/proofs/affine_integral_linearity.proof) | `affine_dyadic_integral_add`, `affine_dyadic_integral_scale`, and `affine_dyadic_integral_cong`. |

Continuity witnesses for sums and scalar multiples are constructed from the
input witnesses; they are not extra assumptions. Finite-sum identities and
uniqueness of limits prove the integral laws. Equality along the curve does
not require equality of the entire integrand functions or function
extensionality.

The common-radius construction is constructive: for positive `r,s`, produce
positive `delta` with `delta*(r+s) < r*s`, then derive `delta ≤ r,s`.
Fixed-factor estimates use a positive denominator `1 + length`, so zero
coefficients and zero lengths need no zero test.

## Assumptions that must stay visible

- The scalar carrier is `F : U1`, with explicit ring, strict-order,
  ordered-arithmetic, lattice and inverse certificates. Completeness is
  supplied, not derived for a concrete real-number model.
- `ArchimedeanBounds` supplies an **actual natural witness** for each input.
  The shared `Archimedean` property gives only truncated existence. The
  dyadic Cauchy proof must not silently turn one into the other.
- Uniform continuity, convergence and Cauchyness here carry actual moduli.
  These are stronger data than mere existence of each bound.
- The new integral construction and linearity results use the existing
  truncation principles; they introduce no excluded middle, choice, or
  kernel rule. Their input certificates are part of their assumptions even
  when they do not appear in the axiom list.
- The existing higher-universe `FieldExists` uses the prelude's
  universe-lowering truncation into `U0`. This foundational qualification is
  documented in [reals.md](reals.md#universes-and-foundational-assumptions).
- Keep shared foundations constructive. The user permits explicit
  theorem-specific LEM or choice where needed. Do not introduce target
  theorems as axioms, choose representatives from mere existence, or replace
  exact roots with approximate roots without changing the stated result.

## Remaining work and sensible resumption points

The next proposed task was reversal of sampled contours and its passage to
limits. **No reversal implementation was started before the pause.**
`sample_chains`, `sample_maps`, `sample_sum_laws`, `contour_samples` and
`contour_sums` are useful starting modules. Reversing finite samples must
reverse both vertices and their associated tags. An exact finite reversal
law alone will not identify the canonical dyadic constructions for opposite
parameterizations; that comparison needs its own proof.

For the residue theorem, the outstanding work is substantial:

1. Extend the current integral laws to arbitrary splitting, reversal and
   suitable contours, and prove the required independence of partitions
   and parameterizations.
2. Define complex differentiation and holomorphic functions, then develop
   the analytic estimates and Cauchy theory needed for homotopy invariance.
3. Construct the geometric punctured-plane comparison with our homotopy
   model, including coverage and compatibility with concatenation and
   deformation. Apply the existing descent theorems only after these
   obligations are met.
4. Define the local residue data and prove the generator integral
   `2*pi*i*residue`. The normalization itself still needs construction.
5. Apply the checked winding/period formula to this actual integral.

For algebraic closure, retain the winding route: establish a large-circle
leading-term estimate, compare the resulting geometric loop with the
abstract degree-`n` loop, and show a root-free polynomial would extend that
loop through a contractible disk. Audit the logical step from the resulting
contradiction to **mere exact root existence**. This route need not wait for
the residue theorem. The geometric comparison and real-field construction
remain prerequisites.

For Great Picard, the target is the holomorphic essential-singularity
theorem with **at most one** exceptional complex value and infinitely many
preimages in every punctured neighborhood. Holomorphic functions,
essential singularities, normal families and the required omitted-value
estimates are not yet developed. Loop generation alone does not prove it.
The possible analytic route and references are in
[the overview](complex_analysis.md#great-picard); no complete route is
formalized yet.

Concrete reals are a shared outstanding dependency: even rational ordered
arithmetic is not yet constructed, and none of the constructive Dedekind,
classical Boolean Dedekind or ordinary Cauchy quotient carriers has a full
`CompleteOrderedField` certificate. See the explicit construction tasks in
[reals.md](reals.md#remaining-construction-proofs).

## Validation and restart commands

At this checkpoint:

- The latest linearity module and its imports kernel-check in **3,093,777
  instructions** (90 source imports). This is a compilation measurement,
  not a progress percentage toward the three targets.
- All three focused regressions passed: positive linearity verification;
  rejection when a required positive common-radius input is weakened; and
  rejection when the scalar factor is removed from the finite sum identity.
- The proof-library registration test passed.
- Chromium successfully loaded and verified all five new modules through
  their direct proof URLs, with no page errors and no LEM/choice dependency.
- The full mathematical library was **not** rerun. During development the
  user requests targeted tests; run the full library only at the agreed
  completion checkpoint.

From the repository root:

```sh
# Check one module and its imports.
npm test -- web/proofs/affine_integral_linearity.proof

# Reproduce the latest positive and negative regressions.
npm test -- --test-name-pattern='constructed affine integrals are complex-linear|common input modulus requires|finite contour linearity cannot' tests/mathscript.test.mjs

# Check web proof registration.
node --test tests/proof-library.test.mjs

# If the local server is not already running:
python3 tools/serve.py --port 8088
```

Open `http://127.0.0.1:8088/proof.html?proof=affine_integral_linearity`
to inspect the latest results. The other four module names in the table work
as `proof` query values as well. The browser check used a temporary helper;
the direct URLs and persistent regression tests are the durable entry points.

Useful prior commits are `1675fa3` (actual dyadic refinement), `c2b7299`
(uniform contour refinement estimates, alongside group identity), and
`8cb5658` (constructed affine integrals and their initial laws). The
linearity batch is saved together with this handoff.

## Implementation cautions

- Data-producing recursive constructions that must compute through
  projections should be transparent `def`s. An opaque `theorem` can block
  a needed definitional reduction; this mattered for dyadic sample data.
- `obtain` does not generally rewrite a goal depending on the original
  dependent pair. Use projections or dependent pair induction for such
  goals.
- `coordinate_difference(a,b)` is `b + (-a)`; check orientation carefully
  when transferring error bounds or implementing reversal.
- Do not infer equality of geometric curves, sample data or function
  arguments from equality of sums. Preserve the explicit path transports
  used in the current certificates.
- Register new proof modules in both browser registries, document their
  actual hypotheses, and add focused regression coverage for substantive
  claims. No new kernel feature is currently justified by these unfinished
  analytic obligations.
