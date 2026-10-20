# Nondependent quotient descent and the remaining normalization cost

The unchanged [generic quotient fixture](../../tests/fixtures/generic-prop-normalization.cubist)
now completes within its fixed 10,000,000-step full-normalization gate.
`descend` builds its own match with a constant motive, so the elaborator
uses the supplied setness evidence directly in the generated squash clause.
Previously it instantiated `quotient_induction`, whose genuinely dependent
squash clause had already been generated with transports.

This changes a general library computation, not the kernel's equality rules.
It applies to every carrier, relation, target set and respecting map accepted
by `descend`. Class and relation computation are preserved. The generated
squash proof, and hence definitional unfolding along that constructor,
changes. Dependent `quotient_induction` retains its existing construction.
No representative selection, proof erasure or constant-transport rule is
introduced.

## Fixed gate

Run `node tools/quotient-normalization-probe.mjs` after `make wasm`. Each
function is derived in a fresh program and fully normalized, including
surviving annotations, under a fixed 10M budget and 30-second deadline.

| Case | Before: steps / new nodes | After: steps / new nodes |
| --- | ---: | ---: |
| `to_unit` | 5,117 / 1,156 | 2,699 / 587 |
| `to_prop`, assumed setness | budget exhausted: 10,000,000 / 2,028,800 | 2,272 / 459 |

Both measurements use main `ea92c7cb`; only the after measurement includes
this library change. The before probe was rerun on that base and reproduced
the earlier recorded counters exactly. No kernel limits
or reproduction definitions change. The regression in
`tests/quotient-descent.test.mjs` fails with budget exhaustion when the old
library definition is restored and passes with the new definition. Separate
checked `refl` proofs test class and relation computation for arbitrary
universe levels and parameters.

The returned Unit function has 70 reachable nodes and depth 27; the Prop
function has 62 nodes and depth 20. Both fresh programs report 1,836,544 bytes
of arena allocation after normalization and finish before the 30-second
deadline. These counts include annotations.

All 23 targeted JavaScript tests pass, including every library module and its
declared assumptions, quotient groups/universality, h-level generation and
the prior open-normalization regressions. One test run had unusually long
wall times. A subsequent serial comparison of the four original quotient
workloads gives the following deterministic totals (instruction plus query
work, including checking and retries):

| Workload | Before work | After work | Before / after arena nodes |
| --- | ---: | ---: | ---: |
| Small binary quotient | 8,568,657 | 2,956,985 | 1,779,704 / 656,411 |
| Unary quotient, syntax interning off | 750,283 | 700,296 | 22,138 / 10,297 |
| `bint_mul` | 16,400,433 | 9,482,649 | 2,070,139 / 946,836 |
| Binary fraction field's one | 16,637,410 | 9,988,243 | 2,101,578 / 976,040 |

All four evaluations complete on both versions. Final arena node counts
include checking state and are not cumulative allocation counts. Elapsed
totals were 16.66s before and 12.72s after; this single pair supplies no
portable timing claim. The quotient workload's large wall-time outlier did
not recur; the unusually slow h-level test was not rerun in this comparison.

## A completed reference for the old computation

The architectural audit requested a completed output, rather than inferring
its size from a failed fixed-budget query. On `bf543532` (main plus #291/#292),
the original generic definition and a quotient-free transport both complete
when queried once at the existing maximum work allowance of 1.28B steps,
with a 30-second deadline. No syntax-depth, stack or memory limit was raised.
These are diagnostic reference runs, not passes of the 10M gate.

| Original computation | Work | New nodes | Reachable output nodes | Output depth |
| --- | ---: | ---: | ---: | ---: |
| Constant Prop setness transport | 15,383,091 | 3,825,456 | 308,411 | 170 |
| Generic quotient to Prop, assumed setness | 138,143,368 | 19,083,242 | 1,235,756 | 322 |

Reachable counts include annotations and preserve exact handle sharing;
they are not alpha-minimal sizes. The arena reports about 303MB and 2.15GB
respectively after these queries. These are arena allocations, not process
peak resident memory. The reference source combined a direct-match control,
the generic map and the witness transport; its names and checking history
differ from the fixed two-function fixture above and the five-case transport
fixture below. Those fixtures also use the earlier `ea92c7cb` kernel, so the
reference counters are not interchangeable with their counters.

A direct nondependent match into Prop with assumed setness completed in
1,253 steps, allocated 208 nodes and returned 62 reachable nodes of depth 20.
That comparison motivated the general `descend` change. It does not prove
that every dependent squash construction admits the same simplification.

## The evaluator reproduction remains

The [constant-transport fixture](../../tests/fixtures/constant-setness-transport.cubist)
retains the underlying evaluator workload without a quotient, arithmetic or
the concrete `prop_type_is_set` theorem. Run:

```sh
node tools/transport-normalization-probe.mjs
```

The tool checks the fixture in a fresh program for each case, fixes the query
budget at 10M and deadline at 30 seconds, and records source/kernel/dependency hashes,
work, allocation, arena size and completed graph size. Controlled resource
stops are JSON outcomes, not a successful-normalization assertion.
Graph inspection has a separate work/deadline bound. The setness and path
cases remain evaluator workloads even though quotient descent now avoids
generating them for constant motives.

Baseline on `ea92c7cb` plus this library change, in fresh checked programs:

| Case | Outcome | Work | New nodes | Output nodes / depth | Arena bytes |
| --- | --- | ---: | ---: | ---: | ---: |
| `moved_value` | normalized | 2,914 | 958 | 89 / 26 | 1,836,544 |
| `moved_function` | normalized | 5,723 | 1,913 | 171 / 52 | 1,836,544 |
| `moved_neutral` | normalized | 768 | 184 | 64 / 20 | 1,836,544 |
| `moved_setness` | budget exhausted | 10,000,000 | 2,526,247 | — | 269,092,352 |
| `moved_path` | budget exhausted | 10,000,000 | 2,602,450 | — | 269,092,352 |

All five queries returned before their 30-second deadline. SHA-256 identities
reported by the probe are:

- Fixture: `7b38505e74db872424dfa1559e9729133af63b6828417a3bb9d9a21b8123cee0`.
- WASM kernel: `ebe45dfee79c351d2602961d51963b0ce34c00d4118cba00c3165ccb5f42f60b`.
- Sorted imported source entries: `d75003c1095b033752415ec72ff518d208ee1e14f6f0d2c55ca9d5f0b9703af6`.

The completed references show both output growth and intermediate allocation.
Reachable output nodes are 8.1% of allocated nodes for the setness transport
and 6.5% for the generic map, with approximately 50 and 112 work ticks per
output node respectively. These measurements neither establish nor rule out
enough savings from shared evaluation and readback to pass the retained
transport gates. They do not prove that a different representation can
produce a tiny full normal form under the existing rules.

## Rational release remains open

With the unchanged #283 library diff on `bf543532`, the complete
`bq_inv(-2/3)` previously reached the 512 syntax-depth guard after
133,240,191 steps. Applying this `descend` change lets it fully normalize in
82,049,378 steps, allocating 18,023,587 nodes (about 2.42GB reported arena).
Both measurements used fresh checked programs, one query at the normal
maximum allowance, and a 30-second deadline. The changed small inverse still
exhausts the stricter diagnostic 10M budget.

The unchanged wide inverse has not passed. With this change it also exceeds
10M; a query at the normal maximum stopped at its deadline after 116,531,200
steps and 27,272,443 allocations. Observed elapsed time was about 309 seconds,
well beyond the requested deadline; the cause of that delay was not isolated,
so this run supplies no portable timing comparison. No partial result is
reported as a normal form. Mixed open/closed BNat law proofs and the remaining
depth-sensitive traversals still require their own work.

TODO: isolate the wide query's 309-second elapsed time against its requested
30-second deadline, distinguishing time spent inside the kernel from host
pauses or allocation delays. The current measurement does not identify a
deadline-enforcement defect.

This is a completed generic-quotient gate and a completed small rational
reference, not completion of NUM2, EVAL3/EVAL4/EVAL8, or the default Z/Q
migration. The [original normalization report](rational-normalization.md)
and [runtime roadmap](../roadmaps/runtime/runtime-evaluation-roadmap.md#rational-full-normalization-completion-path)
retain those end-to-end requirements.
