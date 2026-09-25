# From RH to the prime-counting error

Status: **roadmap only** (2026-09-23). No proof development is started by this
document. None of the analytic number-theory milestones below is claimed to
have been checked in Cubist. Resume only when requested, after auditing the
current sources and the [real-number](reals-roadmap.md) and
[complex-analysis](complex-analysis-roadmap.md) roadmaps.

## 1. Fix the statement and its scope

The intended result concerns the number of ordinary rational primes up to a
bound, not the location of the nth prime. Define

\[
\pi(x)=\#\{p\leq x:p\text{ is prime}\},\qquad
\operatorname{Li}_2(x)=\int_2^x\frac{dt}{\log t}\quad(x\geq2).
\]

The main target is the standard conditional bound

\[
\mathrm{RH}_{\zeta}\Longrightarrow
\pi(x)-\operatorname{Li}_2(x)=O(\sqrt{x}\log x)
\quad(x\to\infty).
\]

Counts are coerced to the chosen real field. Spell out the conclusion as

\[
\exists C>0\;\exists X\geq2\;\forall x\geq X,\quad
|\pi(x)-\operatorname{Li}_2(x)|\leq C\sqrt{x}\log x.
\]

Use real bounds in the final theorem; the counting interface can start with
natural bounds. The usual principal-value logarithmic integral differs from
\(\operatorname{Li}_2\) by a constant; prove that this does not affect the
bound. No explicit optimal value of \(C\) or \(X\) is required.

This is the standard direct target of the explicit-formula route.
Its relationship with RH is recorded in
[Bombieri's official problem description, p. 4](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf).
The roadmap proves the forward implication only; proving the converse is out
of scope.

The approximation must be the logarithmic integral. Replacing it with
\(x/\log x\) leaves a main-term discrepancy of order \(x/\log^2x\), which
is too large for this error estimate.

The originally requested conclusion is an optional short corollary:

\[
\forall\varepsilon>0,\quad
\pi(n)-\operatorname{Li}_2(n)=o(n^{1/2+\varepsilon})
\quad(n\in\mathbb N,\ n\to\infty).
\]

It follows by dividing the main bound by \(n^{1/2+\varepsilon}\) and using
\(\log n/n^\varepsilon\to0\). This corollary is not required to finish the
main target.

### Specify the hypothesis accurately

Assume RH for the Riemann zeta function alone: **every zero** of its
completed entire function

\[
\xi(s)=\tfrac12 s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)
\]

has real part \(1/2\). Define this function using analytic continuation
through its removable singularities. Prove that its zeros correspond to the
nontrivial zeros of zeta. The hypothesis excludes zeta's trivial zeros and
does not merely assert that some zeros lie on the critical line. Do not
silently discard possible boundary zeros by restricting the hypothesis to
the open critical strip without proving the needed boundary nonvanishing.

State RH as an explicit theorem hypothesis, not a global assumption silently
loaded by unrelated source modules. The required architecture is

```text
RH for zeta
    ↓
psi(x) - x = O(sqrt(x) log²(x))
    ↓
pi(x) - Li₂(x) = O(sqrt(x) log(x))
    ↓ (optional growth-lemma corollary)
error = o(x^(1/2 + epsilon)) for every epsilon > 0
```

No Selberg-class definition or zeta-membership proof is required. A future
GRH corollary could add those and specialize GRH to zeta, but that additional
formalization is outside this roadmap's completion criteria. Arithmetic
progressions, prime ideals, Chebotarev, and generalized coefficient sums are
also separate future targets.

## 2. Existing foundation and missing interfaces

| Existing material to audit | Potential reuse | What it does not yet supply |
| --- | --- | --- |
| [Prime arithmetic](../../archive/first-library/primes.cubist) and [finite counting](../tactical/finite_counting.md) | Prime predicates, finite sums, finite collections | A complete analytic prime-counting interface; audit unique factorization rather than assuming Euclid's theorem supplies it |
| [Real-number roadmap](reals-roadmap.md) | Ordered-field and completeness interfaces | A completed concrete real model with all required certificates |
| [Limits](../tactical/analysis_limits.md), [field asymptotics](../../archive/first-library/field_asymptotics.cubist) | Convergence, eventual closeness, limit uniqueness | General relative big-O/little-o calculus, exp/log, or real powers |
| [Complex-analysis checkpoint](../tactical/complex_analysis_handoff.md) | Complex algebra, curves, finite contour sums, affine integral results | Holomorphic/meromorphic function theory, general contour integration, residues, or quantitative contour-shift estimates |
| [Circle](../tactical/circle_fundamental_group.md) and [puncture homotopy](../tactical/puncture_homotopy.md) | Integer winding and abstract loop/period algebra | A proved bridge from geometric complex contours to those homotopy types |
| [Formal series](../../archive/first-library/formal_series.cubist) | Coefficient manipulation | Convergence, analytic evaluation, or Dirichlet-series differentiation |

This is a substantial analytic development. Completing finite Galois theory,
Great Picard, or the fundamental theorem of algebra is not a dependency of
this proof. Share the needed real and complex analysis without making the
entire complex-analysis roadmap a prerequisite.

## 3. Develop in independently checkable stages

### A. Counting and asymptotic statements

Define prime counting on natural bounds first. Develop prime-power
factorization, the von Mangoldt function \(\Lambda\), and

\[
\theta(x)=\sum_{p\leq x}\log p,\qquad
\psi(x)=\sum_{m\leq x}\Lambda(m).
\]

Record endpoint conventions explicitly: ordinary sums include the endpoint;
the symmetric explicit formula uses a half-weight at a jump. Add finite-sum
lemmas connecting the two, including the bound on an endpoint correction.

Define big-O and little-o with explicit quantifiers and prove their elementary
closure laws. An interface for absolute error must not be confused with the
existing eventual-closeness relation. Any intermediate theorem assuming an
error bound remains conditional until that assumption is discharged.

### B. Real and complex analytic foundations

Finish one adequate concrete real construction first; the three proposed real
models need not all be finished. Construct complex numbers over it, positive
real logarithms, exponentials, square roots/norms, and
\(x^a=\exp(a\log x)\) for \(x>0\).

Prove the growth lemma \((\log x)^k/x^\eta\to0\) for fixed natural \(k\)
and every \(\eta>0\). Establish the integration and partial-summation rules
needed for step functions. For complex analysis, develop locally uniform
convergence, differentiation of suitable series, isolated zeros with finite
multiplicity, meromorphic functions, Cauchy's theorem, and residues on bounded
piecewise smooth contours. Include integral norm bounds and limiting estimates.

Proofs may initially be parameterized over a certified analytic field, but a
concrete instance must discharge that parameter before claiming the final
ordinary-prime theorem. Audit LEM and choice where classical zero enumeration,
real comparisons, or selections enter; do not infer an actual sequence of
witnesses from merely existential bounds.

### C. Zeta and its analytic continuation

Construct \(\zeta(s)=\sum_{m\geq1}m^{-s}\) on \(\Re s>1\). Prove its
Euler product and logarithmic derivative there:

\[
-\frac{\zeta'(s)}{\zeta(s)}
=\sum_{m\geq1}\frac{\Lambda(m)}{m^s}.
\]

Prove convergence and justify each product/series/differentiation interchange.
Then construct continuation, the simple pole of residue one at \(s=1\),
the functional equation, and the analytic properties of \(\xi\).
Choose a single route: a Mellin transform of the theta function with Poisson
summation for the Gaussian is a reusable candidate. This adds concrete
Gaussian, gamma, and Mellin lemmas, not a requirement to build an unrestricted
Fourier-analysis library first. Obtain the gamma growth estimates needed later.

[Perelli, §1.1](https://arxiv.org/pdf/1605.02354) is a reference for
the zeta-to-primes connection. Its statements are specifications to prove, not certificates
that can replace Cubist derivations.

### D. Zero counting and admissible contours

Prove local finiteness of the zeros and a multiplicity-aware zero-count bound
\(N(T)=O(T\log T)\). Separately establish a local count bound sufficient to
choose horizontal contour edges away from zeros, and bound \(\zeta'/\zeta\)
on those edges. The global count alone does not provide that local control.

Use finite zero collections below each height rather than immediately choosing
a global enumeration. A full Riemann–von Mangoldt asymptotic is optional if
the weaker bounds suffice. Treat bounded-height zeros separately, and retain
multiplicity in every sum and contour-crossing identity.

### E. A truncated explicit formula with a proved remainder

Prove a finite-height Perron formula, then shift its contour across the pole
at one and the enclosed zeros. Track the pole at zero introduced by the
factor \(1/s\), and any trivial zeros crossed. Derive a finite zero sum with
an explicit remainder; do not manipulate an unordered infinite zero sum as
if it converged absolutely.

A convenient target interface is: for sufficiently large half-integer
\(x=m+1/2\), an admissible height \(T\in[x,2x]\) exists such that

\[
\psi(x)=x-\sum_{|\Im\rho|<T}\frac{x^\rho}{\rho}+R(x,T),
\qquad |R(x,T)|\leq C(\log x)^2,
\]

where the sum is over nontrivial zeros with multiplicity, and the constant is
uniform in these choices. This is a **planned lemma**, not a new assumption.
Half-integer inputs avoid the near-integer singularity in the Perron error.
Account for fixed and trivial-zero terms inside the proved remainder.

### F. Insert RH and bound the zero contribution

Derive the reciprocal-zero estimate from the zero count. Under RH, each
\(|x^\rho|=\sqrt{x}\), giving the standard route

\[
\sum_{|\Im\rho|<T}|\rho|^{-1}=O((\log T)^2),\qquad
\psi(x)-x=O(\sqrt{x}(\log x)^2).
\]

Use monotonicity and neighboring half-integers to pass to ordinary endpoint
sums, with all correction terms bounded. This is where the assumed location
of zeros enters; the explicit-formula infrastructure is proved independently.
[Kedlaya's error-bound notes](https://kskedlaya.org/18.785/errorbounds.pdf)
give the reference route through a truncated formula and a zero-count bound.

### G. Remove the prime-power weights

Prove the adequate elementary bound
\(0\leq\psi(x)-\theta(x)=O(\sqrt{x}(\log x)^2)\), without using the
prime number theorem. Thus \(\theta(x)-x\) has the same error scale.

Prove Abel partial summation in the needed form:

\[
\pi(x)=\frac{\theta(x)}{\log x}
+\int_2^x\frac{\theta(t)}{t(\log t)^2}\,dt.
\]

Subtract the corresponding identity for \(\operatorname{Li}_2\), keeping
its lower-endpoint constant. The endpoint error is
\(O(\sqrt{x}\log x)\); the integral error is bounded by a constant multiple
of \(\int_2^x t^{-1/2}\,dt\). Obtain the stronger prime-counting estimate,
which completes the main target. Optionally apply stage B's growth lemma
to obtain the little-o corollary.
Do not mistake a same-exponent big-O estimate for little-o.

## 4. Where homotopy interpretations could help

These are proposed uses of the existing HoTT development. Each geometric-to-
homotopy comparison is an additional proof obligation.

### Winding and the argument principle

A meromorphic function with no zeros or poles on a closed contour sends that
contour into the geometric punctured complex plane. Its winding number is the
number of enclosed zeros minus poles, counted with multiplicity, when the
contour is positively oriented and simple. For general contours, use the
appropriate winding weights.

The existing \(\pi_1(S^1)\cong\mathbb Z\) development suggests a reusable
integer-valued interpretation of this image loop. Build the geometric
comparison and prove the analytic compatibility

\[
\operatorname{wind}(f\circ\gamma,0)
=\frac{1}{2\pi i}\int_\gamma\frac{f'(z)}{f(z)}\,dz.
\]

That interface could supply the topological part of zero counting in stage D.
The remaining estimate of the argument variation still requires analytic
bounds; a winding integer alone does not bound \(N(T)\).

### Multiplicity as local degree

Prove a local factorization \(f(z)=(z-a)^m u(z)\), with \(u\) nonvanishing
on a small disk. Its boundary loop has winding \(m\): the power factor gives
\(m\) turns and the unit factor extends across the disk, hence contributes
zero. Poles contribute negative degree. This can connect analytic orders,
residues of \(f'/f\), and multiplicities in finite zero sums through one
checked interface. Local analytic factorization is required first.

### Contour deformation and crossing singularities

For stage E, formalize a deformation of contours in the complement of the
integrand's singularities. Integrals of the holomorphic differential are
invariant under an admissible deformation. When the deformation crosses
isolated singularities, the difference is expressed using small boundary
loops and their residues. The current puncture/period machinery may help
organize this decomposition after its geometric comparison is proved.

The integrand here is weighted by \(x^s/s\). A zero's contribution is
\(-m_\rho x^\rho/\rho\), not just its integer winding. Homotopy organizes
which local contributions occur and with what orientation; analytic residue
calculation determines their values. Bounds on long contour edges and the
limit as their height grows remain analytic tasks.

### Independence of representations and choices

Univalence may transport results between equivalent presentations of real
and complex analytic structures, provided the equivalence preserves order,
norm, operations, convergence, and the functions used. A bare carrier
equivalence does not preserve estimates. Likewise, homotopies between
admissible contour deformations could prove independence of deformation
choices. Introduce higher coherence only if an actual composition or reuse
obligation needs it.

**Important boundary:** \(\mathbb C\), viewed simply as a set of coordinate
pairs, has equality paths, not all continuous geometric paths. Its nonzero
subtype is not automatically the homotopy type of the punctured plane. Build
a suitable topological realization or an explicit contour-homotopy interface;
do not identify ordinary equality with continuous deformation. See the
[existing puncture notes](../tactical/puncture_homotopy.md).

Homotopy can make winding, multiplicity, and contour bookkeeping reusable.
It supplies neither RH nor the logarithmic-derivative and growth estimates
responsible for the square-root error. A direct analytic contour proof remains
an acceptable first route if the geometric comparison would delay the target.

## 5. Suggested order and acceptance criteria

1. Audit the existing arithmetic and analytic interfaces; fix all definitions
   and conventions in stage A.
2. Prove the partial-summation implication from a supplied theta/psi estimate
   to the prime-counting big-O bound. Label it conditional, with no claim that
   RH has yet supplied the estimate.
3. Build stages B–C and the bounded-contour analytic tools. Share completed
   lemmas with the reals and complex-analysis roadmaps.
4. Complete the zero-count and truncated-explicit-formula obligations D–E.
   Add the homotopy interfaces where they remove repeated contour arguments.
5. Complete F–G under an explicit RH hypothesis, discharging every analytic
   certificate for the concrete prime-counting function. This finishes the
   main big-O target.
6. Optionally derive the little-o corollary using the logarithmic growth lemma.

For each future implementation increment, add focused positive checks and
tests rejecting missing convergence, boundary avoidance, or multiplicity
hypotheses where applicable. Verify both endpoints and jumps in counting
identities. Use the declaration benchmark to find oversized proof terms;
factor reusable lemmas rather than weakening the checker.

Completion means the big-O theorem depends on the stated RH hypothesis and
explicitly recorded foundational assumptions only. It must not retain an
unproved explicit formula, zero-count estimate, or residue theorem as a
hidden parameter. Update this roadmap and create a tactical handoff when
implementation is actually requested.
