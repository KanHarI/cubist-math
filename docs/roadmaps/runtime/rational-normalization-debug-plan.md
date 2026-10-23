# Rational normalization: debugging plan

Planned on 2026-10-21 against main `6d1bd75b`, and re-measured on 2026-10-23
against main `41d507a0`, after the evaluation demand marks (#304 to #306);
the kernel sources are
`ee8b2f32f6f15020809eec1457acbc3c0801adb18d78bb936cb9987400f22ce4` in both.
This plan covers the cluster of full-normalization failures around
rationals: the small inverse that exhausts the 10M diagnostic budget, the
wide inverse that reaches the native recursion guard in #283's contract, the
100,000-tick `SameRatio` observation in the
[selected literal diagnosis](../../reports/rational-literal-normalization.md),
the 3.5M-tick cost of every binary rational value and open ring operation,
and the 70M-tick cost of every literal of main's public rationals and of the
integers' additive group (1.7), all treated as one cluster and not as an
acceptable floor. It
supplements the [inverse normalization report](../../reports/rational-normalization.md)
and the roadmap's [completion path](runtime-evaluation-roadmap.md#rational-full-normalization-completion-path);
it does not close any of their gates.

Every measurement below was taken with the retained
[probe](rational-normalization-debug-plan/probe.mjs): a fresh checked program
per query, main's library only, a fixed query budget, a 600-second deadline,
no automatic budget increase, and graph metrics of the completed normal form
(reachable handles including annotations, exact sharing preserved). Numbers
from different queries are separate measurements, never an additive
breakdown. The probe's two fixtures are inline, `binary` (the demand marks'
`rational` source with this plan's further queries) and `unary` (main's
public rationals and integers); a query checks the whole fixture that
defines its name. Every record of 2026-10-23 is in
[`results.jsonl`](rational-normalization-debug-plan/results.jsonl) with its
kernel and fixture hashes. Run the probe from the repository root after
`make wasm`:

```sh
node docs/roadmaps/runtime/rational-normalization-debug-plan/probe.mjs normalize small_inverse
node docs/roadmaps/runtime/rational-normalization-debug-plan/probe.mjs ladder q_inv_open 10000000,100000000
node docs/roadmaps/runtime/rational-normalization-debug-plan/probe.mjs survey multiplication,setness
node docs/roadmaps/runtime/rational-normalization-debug-plan/probe.mjs canonical small_inverse
```

**Ticks are a margin, not a count.** A query's normal form is exact: every
node count and depth below reproduced on 2026-10-23 to the node. Its ticks
depend on the rest of the fixture it is checked in: at the plan's base
commit, with one build, `small_inverse` took 71,457,148 ticks in the first
fixture, 70,725,782 in the retained one, and 72.9M in the fixture cut to
its first definitions, with identical outputs each time. The cause is not
attributed; the kernel and the build were the same. Compare ticks only
between runs of one fixture, and read a tick target as a margin.

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
| `SameRatio` relation (the #300 probe) | 10M | normal form | 3,495,561 | 889,749 | 96,679 / 250 |
| `bint_mul` | 10M | normal form | 3,694,818 | 888,210 | 96,657 / 245 |
| `bint_add` | 10M | normal form | 2,948,932 | 757,197 | 76,616 / 221 |
| `fraction_field(binary_integers, …).one` | 10M | normal form | 3,532,061 | 898,176 | 97,453 / 255 |
| `two_thirds` | 10M | normal form | 3,522,837 | 896,429 | 97,457 / 255 |
| `minus_two_thirds` | 10M | normal form | 3,537,450 | 899,287 | 97,457 / 255 |
| `small_inverse` | 10M | budget exhausted | 10,000,000 | 2,587,098 | — |
| `small_inverse` | 100M | normal form | 70,725,782 | 18,020,193 | 1,149,838 / 434 |
| `small_inverse_neg` | 100M | normal form | 71,036,466 | 18,023,076 | 1,149,910 / 437 |
| `q_inv_open` (the open inverse function) | 100M | resource: syntax depth 512 (`K344`) | 80,182,616 | 18,623,271 | — |
| `wide_inverse` (−(2¹²⁸−1)/(2⁶⁴−1)) | 400M | resource: normal-form depth (`K337`) | 393,274,446 | 30,959,540 | — |

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
  (18,023,587 nodes) on main alone, at about 71M ticks and 18.0M nodes. Its
  completed normal form has **1,149,838 reachable nodes**, 537,717 of them
  `Comp` and 506,504 `Tube`. About 62 ticks and 16 allocations are spent per
  output node: even an evaluator that spent one tick per node would still
  produce a million-node answer. The output size is the primary problem;
  intermediate waste is secondary.
- The open inverse reaches the 512 syntax-depth guard at `ck_make`
  (`term_store.c:243`, `K344`), the same resource class as the wide inverse's
  `K336` in #283's contract (`ck_whnf`, `term_normalize.c:312`, recursion
  above 1024). The wide inverse exhausted its 400M budget on 2026-10-21 and
  reached the normal-form depth guard (`K337`: `normal_push`,
  `term_normalize.c:343`, 16,384 frames) at 393M ticks on 2026-10-23, with
  the same kernel and library and a fixture that differs in other
  definitions: the two limits are within its tick margin of each other, and
  which comes first is not a finding. The historical 116M-step deadline stop
  after 309 seconds is not reproduced here (393M ticks took 17 seconds), so
  that delay was a host condition, not kernel work per tick.

### 1.2 Where the 71M goes

| Query (fresh program each) | Query ticks | Output nodes / depth |
| --- | ---: | ---: |
| `prop_type_is_set(U0)` | 68,490,929 | 1,034,925 / 233 |
| `related_to(U0, BNat and BNat, BIntSameDifference, …, (2, 0))` | 73,879,288 | 1,055,190 / 423 |
| `quotient_effective(U0, …, (2, 0), (0, 0))` | 67,097,974 | 1,055,202 / 427 |
| `bint_decide(bint_of_nat(2), bint_zero)` | 67,202,775 | 1,055,231 / 432 |
| `bint_decide_zero(bint_of_nat(2))` | 74,728 | 2,742 / 135 |
| `bnat_decide(2, 0)` | 3,121 | 64 / 24 |

The inverse's cost is its nonzero certificate. `frac_inv` decides
`decide(f.1, zero)` with the section's `decide`, which is `bint_decide`,
whose negative branch returns
`fun same => no(quotient_effective(…, p, q, same))` (`differences.cubist`,
`difference_decide`). `quotient_effective` composes along
`related_to(…, p @ i).1`, and `related_to` descends into `Prop(U)` with
`prop_type_is_set(U)` as its setness evidence (`quotients.cubist:157-186`).
Under the `same` binder that eliminator is stuck, so its clauses, including
the setness proof, are normalized in full: a single closed library proof with
a 1,034,925-node normal form costs 68.5M on its own, against the inverse's
70.7M. The compact
zero decision, written for exactly this reason
(`difference_decide_zero`: "a zero decision with a compact negative
certificate"), is about 900 times cheaper.

### 1.3 Why one proof has a million-node normal form

Each lemma on the setness path is small on its own:

| Lemma, open in its arguments | Query ticks | Output nodes / depth |
| --- | ---: | ---: |
| `path_into_prop_is_prop(U0, A, P, h)` | 2,270,397 | 66,614 / 140 |
| `prop_path(U0, x, y, f, g)` | 33,337 | 682 / 65 |
| `equiv_into_prop_is_prop(U0, A, P, h)` | 21,904 | 1,022 / 77 |
| `prop_ext(U0, …)` | 10,687 | 177 / 39 |
| `glue_path_idtoequiv(U0, A, B, p)` | 9,633 | 395 / 42 |
| `pathp_has_level(U1, 0, …)` as used by `prop_type_is_set` | 7,430 | 334 / 39 |
| `idtoequiv(U0, A, B, p)` | 3,751 | 156 / 33 |
| `prop_is_set(U1, IsProp(U0, X), …)` | 2,324 | 102 / 31 |
| `sigma_has_level(U1, 0)` | 1,366 | 56 / 18 |
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
| `difference_mul_pairs_left{{U0}}(…, p, s, q, r)` | 175,427 | 6,666 / 145 |
| `difference_add_pairs_left{{U0}}(…, p, s, q, r)` | 88,078 | 3,210 / 121 |
| `difference_mul_pairs_comm{{U0}}(…, p, q)` | 69,208 | 2,917 / 123 |
| `bint_neg` | 58,286 | 2,188 / 112 |
| `difference_path{{U0}}(…, p, q, r)` | 6,098 | 104 / 42 |
| `difference_is_set{{U0}}(…)` | 5,449 | 104 / 42 |
| `difference_mul_pairs{{U0}}(…, p, q)` | 5,278 | 138 / 51 |

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
| `bint_mul` | `HComp` | 11,242 | 11,242 | 5,602 | `Sort` | 5,602 both constant and empty; values: 5,736 `HComp`, 5,442 `Trans`, 55 `PApp`, 9 `App` |
| `bint_mul` | `Comp` | 2,537 | 2,294 | 375 | `Sort` 2,294, `App` 243 | 132 both constant and empty |
| `prop_type_is_set(U0)` | `Comp` | 532,172 | 445,772 | 208,842 | `Fst` | 143,133 both constant and empty |

Every stuck family head is neutral: a declared sort applied to the quotient's
parameters, the first projection of a bound proposition, or an application
left stuck on one. The kernel's
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

### 1.7 Main's public rationals pay the same certificate

Main's `rationals` are the fraction field of the unary integers. A literal
is `rat(a, k)`, which is `class((a, int(succ(k), 0), int_succ_nonzero(k)))`
(`rationals.cubist:14-26`), and `int_succ_nonzero` refutes
`int(succ(k), 0) = int_zero` with `quotient_effective` directly, so every
literal carries the certificate of 1.2, without any decision:

| Query (fresh program each) | Query ticks | Output nodes / depth |
| --- | ---: | ---: |
| `rationals.(2/3)` | 70,301,825 | 1,116,794 / 251 |
| `rationals.(0.5)` | 70,471,677 | 1,118,334 / 267 |
| `rationals.one` | 2,772,762 | 72,159 / 194 |
| `int_succ_nonzero(2)`, open in its equation | 67,085,557 | 1,045,246 / 248 |
| `quotient_effective(U0, …, (succ(2), 0), (0, 0))` | 67,060,247 | 1,045,216 / 245 |
| `int_decide(int(2, 0), int_zero)` | 69,185,916 | 1,045,010 / 249 |
| `integers.additive_` | 73,159,138 | 1,799,676 / 261 |
| `integers.add` | 2,620,671 | 65,201 / 150 |
| `integers.zero_add` | 2,465,595 | 62,310 / 128 |
| `integers.neg_add` | 5,035,013 | 114,355 / 226 |
| `integers.add_comm` | 13,114,858 | 294,322 / 247 |
| `integers.add_assoc` | 57,719,427 | 1,460,386 / 249 |

The demand marks' [acceptance report](evaluation-demand-marks/report.md)
measures `rationals.(2/3) expecting !!_;` at 71,001,788 ticks in the REPL:
this is that cost. The data of the literal is a few dozen nodes; the
certificate is 1,045,246 of its 1,116,794, and the sort annotation the rest.
`rationals.one` takes `int_zero_ne_one` instead and costs the annotation
alone, as the binary field's `one` does. So the 3.5M "floor" of 1.1 is the
binary rationals' only because #283's literal decides its denominator with
`bint_decide_zero`; B1 must reach `int_succ_nonzero` too, and T6 holds it to
that.

The integers' additive group costs 73M for another reason. Its operations
are cheap (`add` is 65k nodes), but its laws are proofs by quotient
induction, stuck when open: `zero_add` and `neg_add` are one
`difference_equation` (one `quotient_induction_prop`), `add_comm` two
(`difference_equation2`) and `add_assoc` three (`difference_equation3`,
`differences.cubist:207-253`). Each stuck induction's normal form holds the
inner proof once as its clause `f` and twice more instantiated at the
endpoints of the relation, `f(a)` and `f(b)`, in the generated squash clause
`prop_over(…, f(a), f(b))` (`quotients.cubist:69-80`), with the setness
evidence beside them: about 5× per level, 62k, 294k and 1,460,386 nodes.
`add_assoc` is 1.46M of the group's 1.8M. This is the mechanism of 1.4 one
level up, and it is not a defect of the lemma: a relate clause holds both
endpoints by its type, so under D1's contract the copies are the normal
form's shape. B2's congruence removes the induction from `descend2`, not
from these laws; B2 measures what a direct prop-valued `match` saves them,
and the factor between levels waits on D1.

### 1.8 How much of the output is duplication up to bound names

The `canonical` mode decodes the completed normal form as the REPL reads it
and counts its parts with `sharedNormalDigest`
(`tools/evaluation-baseline.mjs`), the comparison the demand marks' report
uses: an object counts once for each distinct digest it gets, and objects
alike up to the names of bound variables and dimensions count once.
Decoding gives one object per kernel node and dimension context, adds arrays
for formulas and systems, and drops a path application's annotation, a level
binder's bound and a transport descriptor's term, so the counts are of the
decoding, not of the kernel's nodes:

| Normal form | Kernel nodes | Decoded objects | Distinct up to bound names | Duplication, objects / nodes |
| --- | ---: | ---: | ---: | ---: |
| `small_inverse` | 1,149,838 | 2,898,283 | 471,081 | 6.2× / 2.4× |
| `prop_type_is_set(U0)` | 1,034,925 | 2,710,021 | 341,833 | 7.9× / 3.0× |
| `bint_mul` | 96,657 | 151,353 | 71,854 | 2.1× / 1.3× |
| `two_thirds` | 97,457 | 152,446 | 72,428 | 2.1× / 1.3× |

Between a quarter and a sixth of the large proofs, and half of an operation,
is distinct up to bound names; the rest are alpha-equal copies the kernel's
exact-symbol interning cannot share. This is A.3's first answer, and it
bounds B4: sharing modulo binders can cut these outputs by a factor between
2.4 and 8, which is less than T1 needs in ticks (7×) and does not touch
what is genuinely instantiated. The count over kernel nodes with every
annotation, if B4 is pursued, is the rest of A.3.

## 2. Targets and gates

| Target | Today | Gate |
| --- | ---: | --- |
| T1 small inverse, `q_inv(2/3)` and `q_inv(-2/3)`, fresh program | about 71M ticks, 1.15M output nodes | full normal form under the fixed 10M diagnostic budget; the retained `rational-literal-normalization/probe.mjs` unchanged |
| T2 open inverse `q_inv_open` and the wide inverse | `K344` at 80M; `K337` at 393M or the 400M budget | both complete under the default growing budget without K336, K337 or the syntax guard; `binary_rationals.normalize_wide_inverse` passes in #283's contract within CI's time |
| T3 rational value, `bint_mul`, `bint_add`, the field's `one` | 3.5M ticks, 97k nodes | provisional: under 1M ticks and 20k nodes each, to be re-based from B2's first measurement; alpha-equal output wherever only the kernel changed |
| T4 evaluator gates `moved_setness`, `moved_path` | 10M exhausted | unchanged from the roadmap; a library fix does not claim them |
| T5 host | historical 309 s against a 30 s deadline | either reproduced and attributed, or recorded as not reproducible on `6d1bd75b` with the evidence in 1.1 |
| T6 main's rationals: `rationals.(2/3)`, `rationals.(0.5)`, `integers.additive_` | 70M ticks, 1.12M nodes for a literal; 73M, 1.8M for the group | the literals under the fixed 10M diagnostic budget by B1, `rationals.one` no larger than today; the group under 10M, which 1.7 expects to need D1 |

Non-negotiable throughout: no new axiom, proof irrelevance or transport
regularity rule; no raised depth guard, recursion guard, budget or memory
limit; closed assumption-free results keep computing to canonical values;
fixtures stay fixed through the changes they measure.

## 3. Work plan

### Phase A: retain the reproduction and finish attribution (one PR, docs and tools only)

1. Retain the probe and its two inline fixtures as this directory's
   artifacts, record every measurement of section 1 in
   [`results.jsonl`](rational-normalization-debug-plan/results.jsonl) with
   its kernel and fixture hashes, and link this plan from the inverse report
   and the roadmap. Done in this plan's PR. The fixtures stay inline, so no
   indexed Cubist file is added.
2. Add a regression that pins today's behavior without passing judgement on
   it: a test that fully normalizes `two_thirds`, `bint_mul`, `rationals.one`
   and `integers.zero_add` under a fixed 10M budget, and `rationals.(2/3)`
   under 100M, and asserts their output node counts and depths exactly.
   Any change to the cluster then shows up as a number, in either direction.
3. Measure alpha-duplication of the two large outputs: canonical hashing of
   the normal form modulo bound names (de Bruijn indices for term, level and
   dimension binders, annotations included), counting distinct canonical
   nodes against exact reachable nodes for `small_inverse` and
   `prop_type_is_set(U0)`. This decides B4 before any kernel change. A first
   answer, over decodings, is in 1.8. What remains is a count over kernel
   nodes with every annotation, needed only if B4 is pursued.
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
Hypothesis: T1 is the `quotient_effective` certificate, and both the
inverse and main's literals complete under 10M once their certificates
avoid it. Change, in two parts:

- Decide `x = y` in `differences` through a tag into a fixed set, as
  `difference_decide_zero` already does for `x = zero`: decide
  `difference_zero_tag(x - y) = 0` and derive `x = y` from `x - y = zero` by
  a closed ring lemma, so no proposition-valued descent appears in the
  certificate. `fraction_field` takes `decide` as a parameter, so
  `frac_inv`, `q_decide` and `q_mul_inv` inherit the change.
- Refute `int(succ(k), 0) = int_zero` in `int_succ_nonzero` through the
  same zero decision, instantiated for the unary integers, as #283's
  literal does with `bint_decide_zero`, so that `rat` carries no
  `quotient_effective`.

Measure: `small_inverse`, `small_inverse_neg`, `decision`, `q_decide` on
two distinct literals, `q_two_thirds` and `q_half`, each fresh. Refuted if
`small_inverse` or `q_two_thirds` stays above 10M, or `decision` above about
200k. Expected: roughly 3.6M for the inverse and 3M for a literal of main's
rationals, which also makes T2's open and wide cases measurable at their
next bottleneck. The first part changes the `differences` section, so
`int_decide` and `bint_decide` both lose the evidence; `quotient_effective`,
`related_to` and their other users keep it.

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
Congruence does not reach the integers' laws (1.7): they nest
`quotient_induction_prop` itself, and a relate clause of type
`PathP(…, f(a), f(b))` holds both endpoints in any form, so their three
copies a level are the shape of the normal form under D1's contract, not of
the lemma. What a library change can take from them is each level's other
material, `props` in the relate and squash clauses and `prop_over`'s two
compositions, by a direct `match` with a prop-valued motive, as the
[nondependent descent report](../../reports/nondependent-quotient-descent.md)
did for `descend`'s constant motive. Measure `z_zero_add`, `z_add_comm` and
`z_add_assoc` with the same tally, before and after; the factor between
levels is D1's to change.

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
   re-run on top of it; #283 stays draft until T2 also passes. #283 predates
   the demand marks: its three bare `expecting _;` lines are `E485` on main.
   Rebase them as `expecting !!_;`, so that they keep measuring full
   normalization, before re-running.
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
definition reference, so the normal form computed by `expecting !!_`, by an
exact expected value or by `witness` contains the normal form of every lemma
body a stuck proof mentions, instantiated at every use. B1 to B4 reduce
that within the contract. The
[evaluation demand marks](evaluation-demand-marks.md) took full
normalization out of display, inspection and patterns, and left `!!` naming
the kernel's full normal form unchanged; they do not decide D1. The
alternative, keeping a definition application folded when its unfolding is
stuck on a neutral argument, would now change only what `!!_`, exact checks
and `witness` compute and print, and the roadmap's stage 4 still says to
force every surviving proof and annotation. Decide whether the contract
stays, because it bounds what the kernel levers can achieve: with it, a
stuck h-level proof's normal form is as large as its instantiation tree,
which 1.8 measures at 2.4 to 3 times its distinct parts.

**D2. Rules for empty-system compositions on declared sorts (B7).** A
computation rule, not a regularity rule for `Path`, but still a change to
what the kernel equates; it needs the semantic argument first. It now has a
visible effect as well: since #304 a constructor pattern does not read
through a formal composition and shows it as `<composition>` (the demand
marks note, decision 6), and with such a rule those patterns would match
with no rule of their own.

**D3. Library certificate shapes (B1, B2).** Public statements do not
change; the certificates that `bint_decide`, `q_decide`, `int_succ_nonzero`
and `descend2` compute to do. Confirm that this is acceptable for the computability
contract: closed decisions still return `left` or `right` with a checked
proof, only a smaller one.

## 5. What this plan does not do

It does not claim the evaluator gates `moved_setness` and `moved_path`,
which keep measuring the quotient-free transport workload for EVAL3 to EVAL8.
It does not change the `expecting !!_` contract unless D1 does; a bare
`expecting _` has been `E485` since #304. It does not
compare warm-cache numbers with fresh ones, and it does not count a budget
exhaustion as evidence of divergence.
