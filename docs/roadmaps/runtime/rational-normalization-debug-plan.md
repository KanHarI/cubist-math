# Rational normalization: debugging plan

Planned on 2026-10-21 against main `6d1bd75b` (kernel sources
`ee8b2f32f6f15020809eec1457acbc3c0801adb18d78bb936cb9987400f22ce4`). This
plan covers the cluster of full-normalization failures around binary
rationals: the small inverse that exhausts the 10M diagnostic budget, the
wide inverse that reaches the native recursion guard in #283's contract, the
100,000-tick `SameRatio` observation in the
[selected literal diagnosis](../../reports/rational-literal-normalization.md),
and the 3.5M-tick cost of every rational value and open ring operation, which
is treated as part of the same cluster and not as an acceptable floor. It
supplements the [inverse normalization report](../../reports/rational-normalization.md)
and the roadmap's [completion path](runtime-evaluation-roadmap.md#rational-full-normalization-completion-path);
it does not close any of their gates.

Every measurement below was taken with the retained
[probe](rational-normalization-debug-plan/probe.mjs): a fresh checked program
per query, main's library only, a fixed query budget, a 600-second deadline,
no automatic budget increase, and graph metrics of the completed normal form
(reachable handles including annotations, exact sharing preserved). Numbers
from different queries are separate measurements, never an additive
breakdown. Run it from the repository root after `make wasm`:

```sh
node docs/roadmaps/runtime/rational-normalization-debug-plan/probe.mjs normalize small_inverse
node docs/roadmaps/runtime/rational-normalization-debug-plan/probe.mjs ladder q_inv_open 10000000,100000000
node docs/roadmaps/runtime/rational-normalization-debug-plan/probe.mjs survey multiplication,setness
```

## 1. What is established

### 1.1 The main-only reproduction

The inverse failure reproduces without #283. The probe builds the literal as
#283's parser does, with a compact zero decision on the denominator, and
inverts it with the generic `q_inv`:

```cubist
computable def two_thirds : BQ := match bint_decide_zero(bint_of_nat(3)) return BQ {
    left same => binary_rationals.zero;
    right nonzero => class((bint_of_nat(2), bint_of_nat(3), nonzero));
  };

computable def small_inverse : BQ := q_inv{{U0}}(
  binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one, two_thirds
);
```

| Query | Budget | Outcome | Query ticks | Allocated nodes | Output nodes / depth |
| --- | ---: | --- | ---: | ---: | ---: |
| `SameRatio` relation (the #300 probe) | 10M | normal form | 3,497,060 | 889,760 | 96,679 / 250 |
| `bint_mul` | 10M | normal form | 3,693,916 | 888,214 | 96,657 / 245 |
| `bint_add` | 10M | normal form | 2,948,884 | 757,197 | 76,616 / 221 |
| `fraction_field(binary_integers, …).one` | 10M | normal form | 3,533,831 | 898,213 | not measured |
| `two_thirds` | 10M | normal form | 3,525,534 | 896,433 | 97,457 / 255 |
| `minus_two_thirds` | 10M | normal form | 3,540,603 | 899,291 | not measured |
| `small_inverse` | 10M | budget exhausted | 10,000,000 | 2,569,631 | — |
| `small_inverse` | 100M | normal form | 71,457,148 | 18,020,244 | 1,149,838 / 434 |
| `small_inverse_neg` | 100M | normal form | 72,961,223 | 18,023,127 | not measured |
| `q_inv_open` (the open inverse function) | 100M | resource: syntax depth 512 | 79,536,046 | 18,623,322 | — |
| `wide_inverse` (−(2¹²⁸−1)/(2⁶⁴−1)) | 400M | budget exhausted | 400,000,000 | 28,514,701 | — |

Consequences:

- The 100,000-tick `SameRatio` failure in #300 is a budget-scale
  observation: the relation completes at 3.5M ticks, the same cost as
  `bint_mul`, the field's `one` and every rational literal. Their normal
  forms are about 97,000 nodes; a literal's numerator alone normalizes in
  1,719 ticks (#300). The 3.5M is the retained **sort annotation**: a
  constructor's only child is its sort instance
  (`cubical_kernel.h`, the declared-type comment), `ck_normal` normalizes
  every child of every weak head (`term_normalize.c`, the `NORMAL_CHILDREN`
  phase), and the sort `Quotient(U0, Fraction(…), SameRatio(…))` carries the
  relation as a lambda whose body applies `difference_mul` to bound
  variables.
- The small inverse reproduces the historical 82,049,378-tick reference
  (18,023,587 nodes) on main alone, at 71.5M ticks and 18.0M nodes. Its
  completed normal form has **1,149,838 reachable nodes**, 537,717 of them
  `Comp` and 506,504 `Tube`. About 62 ticks and 16 allocations are spent per
  output node: even an evaluator that spent one tick per node would still
  produce a million-node answer. The output size is the primary problem;
  intermediate waste is secondary.
- The open inverse reaches the 512 syntax-depth guard at `ck_make`
  (`term_store.c:242`), the same resource class as the wide inverse's K336
  (`ck_whnf`, `term_normalize.c:310`, recursion above 1024). The wide inverse
  needs more than 400M ticks on main; the historical 116M-step deadline stop
  after 309 seconds is not reproduced here (400M ticks took 16 seconds), so
  that delay was a host condition, not kernel work per tick.

### 1.2 Where the 71.5M goes

| Query (fresh program each) | Query ticks | Output nodes / depth |
| --- | ---: | ---: |
| `prop_type_is_set(U0)` | 67,629,078 | 1,034,925 / 233 |
| `related_to(U0, BNat and BNat, BIntSameDifference, …, (2, 0))` | 72,502,824 | 1,055,190 / 423 |
| `quotient_effective(U0, …, (2, 0), (0, 0))` | 67,658,852 | 1,055,202 / 427 |
| `bint_decide(bint_of_nat(2), bint_zero)` | 67,675,558 | 1,055,231 / 432 |
| `bint_decide_zero(bint_of_nat(2))` | 74,970 | 2,742 / 135 |
| `bnat_decide(2, 0)` | 3,196 | 64 / 24 |

The inverse's cost is its nonzero certificate. `frac_inv` decides
`decide(f.1, zero)` with the section's `decide`, which is `bint_decide`,
whose negative branch returns
`fun same => no(quotient_effective(…, p, q, same))` (`differences.cubist`,
`difference_decide`). `quotient_effective` composes along
`related_to(…, p @ i).1`, and `related_to` descends into `Prop(U)` with
`prop_type_is_set(U)` as its setness evidence (`quotients.cubist:157-186`).
Under the `same` binder that eliminator is stuck, so its clauses, including
the setness proof, are normalized in full: a single closed library proof with
a 1,034,925-node normal form accounts for 67.6M of the 71.5M. The compact
zero decision, written for exactly this reason
(`difference_decide_zero`: "a zero decision with a compact negative
certificate"), is about 900 times cheaper.

### 1.3 Why one proof has a million-node normal form

Each lemma on the setness path is small on its own:

| Lemma, open in its arguments | Query ticks | Output nodes / depth |
| --- | ---: | ---: |
| `path_into_prop_is_prop(U0, A, P, h)` | 2,261,348 | 66,614 / 140 |
| `prop_path(U0, x, y, f, g)` | 33,307 | 682 / 65 |
| `equiv_into_prop_is_prop(U0, A, P, h)` | 21,841 | 1,022 / 77 |
| `prop_ext(U0, …)` | 10,742 | 177 / 39 |
| `glue_path_idtoequiv(U0, A, B, p)` | 9,612 | 395 / 42 |
| `pathp_has_level(U1, 0, …)` as used by `prop_type_is_set` | 7,487 | 334 / 39 |
| `idtoequiv(U0, A, B, p)` | 3,726 | 156 / 33 |
| `prop_is_set(U1, IsProp(U0, X), …)` | 2,309 | 102 / 31 |
| `sigma_has_level(U1, 0)` | 1,365 | 56 / 18 |
| `is_prop_is_prop(U0, X)` | 776 | 41 / 18 |
| `retract_has_level(U1, 0)` | 602 | 52 / 20 |

`prop_type_is_set` applies `retract_has_level` to a `sigma_has_level`
argument that itself contains `path_into_prop_is_prop` and
`pathp_has_level`. Full normalization unfolds every definition reference it
meets (`weak`, `term_normalize.c:41-45`, unfolds every `CC_DEFREF`), and beta
reduction substitutes each proof argument into every position its binder
occurs. After substitution the copies have different arguments, so syntax
interning (`CC_SHARE_SYNTAX`) and the exact-handle normal cache
(`k->normal_cache`, `term_normalize.c:389` and `:511`) share none of them,
and each copy is normalized and retained separately. The normal form of a
proof *combinator* applied to proof *arguments* is a tree whose size
multiplies the fan-outs; the 1,034,925 nodes are about fifteen copies' worth
of the largest lemma.

### 1.4 The 3.5M cluster has the same mechanism

| Lemma, open in its arguments | Query ticks | Output nodes / depth |
| --- | ---: | ---: |
| `difference_mul_pairs_left{{U0}}(…, p, s, q, r)` | 174,725 | 6,666 / 145 |
| `difference_add_pairs_left{{U0}}(…, p, s, q, r)` | 88,181 | 3,210 / 121 |
| `difference_mul_pairs_comm{{U0}}(…, p, q)` | 69,416 | 2,917 / 123 |
| `bint_neg` | 58,248 | 2,188 / 112 |
| `difference_path{{U0}}(…, p, q, r)` | 6,101 | 104 / 42 |
| `difference_is_set{{U0}}(…)` | 5,447 | 104 / 42 |
| `difference_mul_pairs{{U0}}(…, p, q)` | 5,275 | 138 / 51 |

The ring proofs are not the cost. `bint_add` and `bint_mul` carry an
identical residue of 21,973 `Trans` and 11,242 `HComp` nodes, while `bint_neg`,
a one-argument `descend`, has a 2,188-node normal form with at most a few
dozen of them. The shared part is the two-argument
descent: `descend2` descends into the function set with `pi_is_set`, and
proves its outer respects obligation with `maps_agreeing_on_classes`, which
is `ext` plus `quotient_induction_prop` on a dependent motive `g(z) = h(z)`.
That induction's generated squash clause is the composition and transport
machinery whose cost the [nondependent descent report](../../reports/nondependent-quotient-descent.md)
removed from one-argument `descend` and which the `moved_setness` and
`moved_path` fixtures isolate. The rational literal pays it through the
annotation; the integer operations pay it directly.

### 1.5 What the residue is

The survey mode classifies every `Comp`, `Trans` and `HComp` node in a
completed normal form by whether its family mentions its own dimension
(shadowing ignored, so constant counts are lower bounds) and whether its
system is empty:

| Normal form | Kind | Total | Constant family | Empty system | Family heads | Notes |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `bint_mul` | `Trans` | 21,973 | 21,973 | 0 | `Sort` | faces: 12,391 bottom, 9,582 other, none top; values: 21,662 `Trans`, 260 `App`, 51 `PApp` |
| `bint_mul` | `HComp` | 11,242 | 11,242 | 5,602 | `Sort` | empty-system values: 2,900 `HComp`, 2,702 `Trans` |
| `bint_mul` | `Comp` | 2,537 | 2,294 | 375 | `Sort` | |
| `prop_type_is_set(U0)` | `Comp` | 532,172 | 445,772 | 208,842 | `Fst` | 143,133 both constant and empty |

Every stuck family head is neutral: a declared sort applied to the quotient's
parameters, or the first projection of a bound proposition. The kernel's
rules are consistent with the project's contract: a composition over a
neutral family stays neutral (`ck_reduce_composition`,
`composition_compute.c:261-262`), transport of a neutral value at a declared
higher sort stays as written (`sort_transport`, `hit_composition.c`, when
`ck_constructor_application` finds no constructor), and
[path-algebra.md](../../cubical/path-algebra.md) states that transport in a
neutral type is not assumed to reduce definitionally. No `Trans` face is
top, so no `transp` at face 1 is left unreduced. Two things are worth a
decision rather than a fix: `ck_hit_reduce` drops a homogeneous
composition's empty faces but keeps the `HComp` node itself (5,602 of them
in `bint_mul`), and composition over a constant neutral family with an
empty system (143,133 in the setness proof) is exactly the
`transportConstant` lemma that the contract keeps propositional.

### 1.6 Caches do not survive a declaration

Both `cc_kernel_rollback` and the compacting commit clear the weak-head,
normal-form, syntax and alpha memos (`checkpoint.c:31-34` and `:97-100`),
because cached reductions can point at handles that compaction moves. Every
declaration therefore renormalizes the 3.5M-tick annotation of every
rational value it evaluates, and a contract file with several rational
`evaluate` lines pays it per line.

## 2. Targets and gates

| Target | Today | Gate |
| --- | ---: | --- |
| T1 small inverse, `q_inv(2/3)` and `q_inv(-2/3)`, fresh program | 71.5M ticks, 1.15M output nodes | full normal form under the fixed 10M diagnostic budget; the retained `rational-literal-normalization/probe.mjs` unchanged |
| T2 open inverse `q_inv_open` and the wide inverse | depth 512 at 79.5M; budget at 400M | both complete under the default growing budget without K336, K337 or the syntax guard; `binary_rationals.normalize_wide_inverse` passes in #283's contract within CI's time |
| T3 rational value, `bint_mul`, `bint_add`, the field's `one` | 3.5M ticks, 97k nodes | provisional: under 1M ticks and 20k nodes each, to be re-based from B2's first measurement; alpha-equal output wherever only the kernel changed |
| T4 evaluator gates `moved_setness`, `moved_path` | 10M exhausted | unchanged from the roadmap; a library fix does not claim them |
| T5 host | historical 309 s against a 30 s deadline | either reproduced and attributed, or recorded as not reproducible on `6d1bd75b` with the evidence in 1.1 |

Non-negotiable throughout: no new axiom, proof irrelevance or transport
regularity rule; no raised depth guard, recursion guard, budget or memory
limit; closed assumption-free results keep computing to canonical values;
fixtures stay fixed through the changes they measure.

## 3. Work plan

### Phase A: retain the reproduction and finish attribution (one PR, docs and tools only)

1. Retain the probe and its inline source as this directory's artifacts,
   record the table in 1.1 as `results.json` with source, kernel and probe
   hashes, and link this plan from the inverse report and the roadmap. The
   source stays inline so no indexed Cubist file is added.
2. Add a regression that pins today's behavior without passing judgement on
   it: a test that fully normalizes `two_thirds` and `bint_mul` under a
   fixed 10M budget and asserts their output node counts and depths exactly.
   Any change to the cluster then shows up as a number, in either direction.
3. Measure alpha-duplication of the two large outputs: canonical hashing of
   the normal form modulo bound names (de Bruijn indices for term, level and
   dimension binders, annotations included), counting distinct canonical
   nodes against exact reachable nodes for `small_inverse` and
   `prop_type_is_set(U0)`. This decides B4 before any kernel change.
4. Attribute ticks, not only output: a temporary, unapplied instrumentation
   patch in the style of
   [quotient-normalization-trace](../../reports/quotient-normalization-trace.md)
   that counts, per definition unfolded in `weak`, the ticks charged while its
   value is on the normal stack, and reports the top twenty for
   `small_inverse` and `bint_mul`. Keep the patch out of the build.
5. Triage the uncommitted local experiments left in kept worktrees
   (`runtime-composition-stacks`, `runtime-dimension-analysis`,
   `runtime-fraction-normalization-probe`, `runtime-cubical-readback`,
   `runtime-depth-probe`, `runtime-path-level-witness`,
   `runtime-rational-current-gate`, `runtime-closure-evaluation`): read each
   diff, retain anything that bears on B1 to B7 as a documented patch under
   `docs/reports`, and discard the rest.

### Phase B: one experiment per hypothesis, each measured against its gate

Each experiment states its hypothesis, the smallest change that tests it, the
measurement, and what result would refute it. Library experiments change what
a certificate computes to, never what a statement means.

**B1. Compact negative certificates for integer equality (library).**
Hypothesis: T1 is the `quotient_effective` certificate, and the inverse
completes under 10M once `bint_decide`'s negative branch is compact.
Change: decide `x = y` in `differences` through a tag into a fixed set, as
`difference_decide_zero` already does for `x = zero`: decide
`difference_zero_tag(x - y) = 0` and derive `x = y` from `x - y = zero` by a
closed ring lemma, so no proposition-valued descent appears in the
certificate. `fraction_field` takes `decide` as a parameter, so `frac_inv`,
`q_decide` and `q_mul_inv` inherit the change. Measure: `small_inverse`,
`small_inverse_neg`, `decision` and `q_decide` on two distinct literals, each
fresh. Refuted if `small_inverse` stays above 10M or `decision` above about
200k. Expected: roughly 3.6M for the inverse, which also makes T2's open and
wide cases measurable at their next bottleneck.

**B2. Two-argument descent without quotient induction (library).**
Hypothesis: T3's 33,000-node `Trans`/`HComp` residue is
`maps_agreeing_on_classes` inside `descend2`. Change: prove the outer
respects obligation by congruence rather than induction. Both functions being
compared are `descend(U, V, A, R, B, set_, f(a), respects_second(a))` and
`descend(…, f(c), respects_second(c))`; a path between the two descents
follows from a path between their data in `exists g : A -> B. Respects(g)`,
built from `ext` on `respects_first` and from `Respects` being a proposition
(`pi_is_prop` over `set_`), applied by `cong` to `descend`. No squash clause
and no `pi_is_set` are generated. Measure: `multiplication`, `addition`,
`relation`, `two_thirds`, with the output kind tally. Refuted if the
`Trans`/`HComp` counts persist; then the residue is in the generated
`relate` obligation of `descend` itself and the next step is the
elaborator's clause generation. Keep `tests/quotient-descent.test.mjs`
and the `binary_fraction_one` and `integer_multiplication` cases of
`tests/normalization-sharing.test.mjs` passing with unchanged outcomes.

**B3. Reduction caches that survive a commit (kernel).**
Hypothesis: the per-declaration 3.5M in 1.6 is avoidable without any rule
change. Change: on a compacting commit, relocate `weak_cache` and
`normal_cache` entries whose key and value both survive through the existing
relocation map (`cc_kernel_relocated`), instead of clearing them; keep
clearing on rollback, where definitions are truncated. Isolation must hold
exactly as `kernel/tests/test_isolation.c` states it: a cached reduction is
computation, not a judgement, and never changes whether an instruction is
accepted. Measure: a program with two rational `evaluate` lines, the second
one's query ticks; the evaluation baseline's warm samples. Refuted if the
baseline digests or any native test change.

**B4. Sharing modulo bound names (kernel), only if A.3 shows duplication.**
Hypothesis: a large fraction of the 1.15M nodes are alpha-equal copies
differing only in binder symbols. Change options, in order of intrusiveness:
canonical binder symbols in `ck_make` for closed binders; a normal-form cache
keyed by an annotation-aware canonical hash alongside the exact-handle one.
The earlier "stable local binder names" experiment was measured only against
the old 10M gate on the pre-descend fixture and did not count duplicates; do
not repeat it without A.3's number. Refuted if canonical distinct nodes are
within a small factor of exact nodes: then the size is genuine instantiation,
and only B1, B2 and the contract decision D1 can reduce it.

**B5. The remaining depth of the open and wide inverses (kernel, EVAL4).**
After B1, re-run `q_inv_open` and `wide_inverse` at 100M and 400M. If the
open function still reaches the syntax guard, measure its required output
depth with a temporary guard-free diagnostic as the
[normalization-stack report](../../reports/normalization-stack.md) did, and
separate output depth from intermediate depth. If the wide inverse still
exceeds the budget, isolate the wide decision alone
(`bint_decide_zero(bint_of_nat(18446744073709551615))` and
`bnat_decide(340282366920938463463374607431768211455, 0)`) and attribute to
the BNat lemma that expands, as the
[open BNat baseline](../../reports/open-bnat-normalization-baseline.md)
does. Raising 512 or 1024 is not an outcome of this experiment.

**B6. The deadline anomaly (host).**
Run the wide inverse at the normal 1.28B allowance with a 30-second
deadline, recording wall time inside `_cb_normalize` against the JavaScript
clock, the number of `ck_deadline` checks (one per 1,024 ticks, `ck_tick`,
`term_store.c:49-55`), and WebAssembly memory growth events. Today's 16
seconds for 400M ticks predicts no kernel-side cause; refuted if the kernel
clock and the host clock disagree by more than the memory-growth time.

**B7. Empty-system homogeneous compositions (kernel rule, needs D2).**
Hypothesis: `hcomp^h A [] v` on a declared sort is a canonical form the
kernel could compute to `v` soundly. Do not implement before D2 is decided;
prepare the analysis against the H1 specification 3.4 and 3.5 and CHM
§3.3.5, and measure how many of `bint_mul`'s 5,602 would disappear and
whether any instruction (`Step`, `Eta`, the Glue step) would change its
acceptance.

### Phase C: fixes, in this order, one PR each

1. Phase A artifacts.
2. B1, with the inverse gate T1 and all 32 binary-rational contracts of #283
   re-run on top of it; #283 stays draft until T2 also passes.
3. B2, with T3 re-based from its measurement and the quotient regressions.
4. B3, with the baseline digests and native suites.
5. B5 and B6 on the wide inverse; then #283's `normalize_wide_inverse`.
6. B4 and B7 only after their decision points.

Each PR gets an exhaustive first review over named risk areas (certificate
soundness and computation for library changes; isolation, cache lifecycle,
rollback and compaction for kernel changes; fixtures that still measure what
they claim), CI dispatched once after local verification, and a report under
`docs/reports` with source, kernel and probe hashes, fresh-session fixed
budgets, and graph metrics.

## 4. Decisions needed

**D1. What a full normal form unfolds.** Today `weak` unfolds every
definition reference, so an `expecting _` answer contains the normal form of
every lemma body a stuck proof mentions, instantiated at every use. B1 to B4
reduce that within the contract. The alternative, keeping a definition
application folded when its unfolding is stuck on a neutral argument, is the
EVAL5 typed-readback direction; it changes printed normal forms and pattern
matching, and the roadmap's stage 4 currently says the opposite. Decide
whether the contract stays, because it bounds what the kernel levers can
achieve: with it, a stuck h-level proof's normal form is as large as its
instantiation tree.

**D2. Rules for empty-system compositions on declared sorts (B7).** A
computation rule, not a regularity rule for `Path`, but still a change to
what the kernel equates; it needs the semantic argument first.

**D3. Library certificate shapes (B1, B2).** Public statements do not
change; the certificates that `bint_decide`, `q_decide` and `descend2`
compute to do. Confirm that this is acceptable for the computability
contract: closed decisions still return `left` or `right` with a checked
proof, only a smaller one.

## 5. What this plan does not do

It does not claim the evaluator gates `moved_setness` and `moved_path`,
which keep measuring the quotient-free transport workload for EVAL3 to EVAL8.
It does not change the `expecting _` contract unless D1 does. It does not
compare warm-cache numbers with fresh ones, and it does not count a budget
exhaustion as evidence of divergence.
