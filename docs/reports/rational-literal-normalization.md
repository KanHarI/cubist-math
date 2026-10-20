# Rational literal normalization: current diagnosis

Status on 2026-10-21: full normalization of the selected `2/3` occurrence
exhausts the workbench's 100,000-tick budget. This is a bounded performance
failure, not evidence of divergence or an incorrect reduction rule. The
expense can also be reproduced without a rational literal or the pending
binary-rational library changes.

This supplements the [inverse normalization report](rational-normalization.md)
and its [counted quotient rewrites](quotient-normalization-trace.md). It does
not replace their historical measurements or the runtime roadmap's
[completion criteria](../roadmaps/runtime/runtime-evaluation-roadmap.md#rational-full-normalization-completion-path).

## Reproduce using only main's library

The retained [probe](rational-literal-normalization/probe.mjs) checks this
inline source:

```cubist
import fractions;
import binary_integers;

def relation := SameRatio{{U0}}(binary_integers, bint_decide, bint_mul_nonzero, bint_zero_ne_one);
```

From the repository root:

```sh
make wasm
node docs/reports/rational-literal-normalization/probe.mjs
```

The [probe](rational-literal-normalization/probe.mjs) checks this source in a
fresh program, derives a checked reference to `relation`, and requests its
full normal form. The normalizer receives a fixed 100,000-tick budget and a
30-second deadline, with no automatic budget increase. Checking and obtaining
the reference precede the measured query; their caches remain available.
There are no `binary_rationals` imports, source overlays or unchecked
replacement definitions. The probe asserts no expected normal form.

Using the kernel and library of main
`6262df5a97a0f6f8096ae88af1ffae116b10257f`, the source checks and the
query exhausts exactly **100,000 ticks**, allocating **23,604 nodes**.
[results.json](rational-literal-normalization/results.json) records the
documentation checkout revision, actual checked-source hashes, probe hash,
kernel source hash, arena counters and host environment. The recorded revision
is the checkout base; the probe included uncommitted corrections identified
by `probeSha256`. The stamped WASM build was verified against the checkout.
A controlled resource stop is printed as `status: "limited"` and
does not make this diagnostic command exit unsuccessfully; read the JSON
outcome. Unexpected errors still fail the command. A successful future
normalization will be reported as `status: "normalized"`.

The earlier local main-library probe recorded 24,369 allocations. Its entry
was an inspected expression passed directly to `cb_normalize`, whereas the
retained probe derives a definition reference. Those are separate runs with
different query preparation; the difference is not a performance improvement
claim. Both reproduce exhaustion at the same budget. This is a small isolated
reproduction, not a claim of syntactic minimality.

## What the selected `2/3` contains

The 2026-10-20 workbench investigation used the kernel at `4132c05a` and the
pending #283 `fractions` and `binary_rationals` source overlays, with other
library imports from main. The kernel sources are unchanged at `6262df5a`:
the recorded build hashes are both `ee8b2f32f6f15020809eec1457acbc3c0801adb18d78bb936cb9987400f22ce4`.
Its checked definition was `computable def small_inverse := bq_inv(-2/3);`.

Selecting the positive `2/3` beneath negation gives native occurrence path
`[1, 1]` from the expression root. Both a checked native **Normalize** step
at that path and a direct `cb_normalize` query on the selected expression
exhausted 100,000 ticks and allocated 23,699 nodes. The surrounding inverse
does not have to normalize to reproduce this cost; selecting the wrong
occurrence in the UI does not explain it.

In a fresh checked session, **WHNF** exposes the quotient `class` constructor
in **297 ticks**, allocating **61 nodes**. WHNF exposes the outer constructor
without recursively normalizing its arguments and type parameters. The
result has the schematic shape:

```text
constructor sort: Quotient(Fraction(binary_integers, ...), SameRatio(binary_integers, ...))
class((numerator, (denominator, nonzero_evidence)))
```

The constructor retains the fraction carrier and its equivalence relation.
Full normalization traverses this retained syntax as well as the concrete
numerator, denominator and proof. The pretty-printed `2/3` hides it.

Independent component queries after exposing the constructor recorded:

| Selected component | Outcome | Work ticks | Newly allocated nodes |
| --- | --- | ---: | ---: |
| Constructor, including its type parameters | Budget exhausted | 100,000 | 23,739 |
| Pair type | Full normal form | 7,216 | 1,553 |
| Numerator | Full normal form | 1,719 | 347 |
| Denominator | Full normal form | 977 | 188 |
| Nonzero evidence | Full normal form | 64,781 | 14,441 |

These are historical per-component queries in fresh checked sessions after
WHNF, not an additive breakdown of one full-normalization query. Allocation
counts are arena growth during the query, not reachable normal-form sizes.
The [historical observations](rational-literal-normalization/observations.json)
retain the raw component and relation records. The initial native Step log
measured only query ticks and therefore printed zero: checked steps charge
instruction ticks. Its tick field is not used as a cost measurement. The
later copied-trace cost summary in the same artifact records the instruction
cost and independently confirms the 100,000-tick failure.

## Where full normalization spends work

Exposing `SameRatio` gives two bound fraction representatives `f` and `g`
and the relation, schematically:

```text
f.numerator * g.denominator = g.numerator * f.denominator
```

The operation is generic ring multiplication (`CommRing.mul`) instantiated
at `binary_integers`; projecting it from `difference_ring` gives
`difference_mul` on the `Difference` quotient, the same operation `bint_mul`
names. Its operands remain projections from **bound variables**,
even though the enclosing literal is closed. Normalizing `SameRatio` itself
exhausted 100,000 ticks. Later queries on each open multiplication also
exhausted that budget. Those later queries shared warmed caches; their
allocation counts must not be compared as independent cold measurements.

This identifies expensive retained relation syntax and reproduces its cost
without the BQ parser. It rules out a literal-parser failure as a necessary
cause of this budget exhaustion. It does not establish that every parser
operation is optimal, identify all remaining costs inside ring multiplication
instantiated at `binary_integers`, or prove nontermination.

There is already positive completion evidence on main. The
[open quotient normalization report](open-quotient-normalization.md) records
the earlier fix for open `bint_mul`. The `binary_fraction_one` regression in
[normalization-sharing.test.mjs](../../tests/normalization-sharing.test.mjs)
fully normalizes `fraction_field(binary_integers, bint_decide,
bint_mul_nonzero, bint_zero_ne_one).one` with a 40M per-query cap. Its class
constructor carries this same `SameRatio` instance, which the normalizer
traverses. That test also fully normalizes `bint_mul`. The 100,000-tick
failure is therefore a cost-scale observation; this report has not measured
the relation's own completion cost in an isolated larger-budget query.

The nonzero proof in this literal also has a substantial measured cost, but
it completed within the 100,000-tick budget (64,781 ticks) in isolation. It
is different from the inverse result's nonzero proof discussed in the older
report.

## Relation to the unresolved inverse failure

The [nondependent quotient descent report](nondependent-quotient-descent.md#rational-release-remains-open)
already records a completed `bq_inv(-2/3)` reference at **82,049,378 ticks**
on the historical `bf543532`-based diagnostic branch with the #283 library
diff and nondependent descent change (kernel source hash `58bc1cca…`). That
reference has not been rerun on `6262df5a`. It used the normal maximum
allowance and still exceeded the stricter 10M diagnostic budget. Failure to
normalize the selected literal at 100,000
ticks does not contradict that result. The wide inverse and the fixed
quotient-free transport gates remain unresolved in the recorded work.

The next investigation is to profile the remaining cost of ring multiplication
instantiated at `binary_integers`, including retained proof/type normalization,
alongside the existing completed controls. Compare its reduction checkpoints
with the expected rules and preserve the main-only reproduction when measuring
changes. Passing this 100,000-tick diagnostic alone will not close NUM2 or
the existing small/wide inverse and transport acceptance gates.

For further manual investigation, use the AST workbench's **Copy trace**
after selecting a subtree and applying operations. It records paths, budgets,
outcomes, native excerpts and costs since page load, retaining at most 100
entries and 250,000 stored characters; dropped entries are counted. The
failed Normalize warmed caches in the retained manual sequence: its
subsequent WHNF reused the same constructor handle and took only two
instruction ticks, which is not the fresh-session 297-query-tick measurement.
These traces record manual operations, not every internal normalizer rewrite.
