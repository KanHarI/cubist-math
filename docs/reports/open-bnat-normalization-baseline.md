# Open binary-natural normalization baseline

Measured on 2026-10-19 in checkout `eb81c10d`, whose kernel is unchanged
from main `89f73ea1`. These are the fixed
32/64/128-bit inputs required before the runtime roadmap's depth-independent
traversal work. This change records fixtures and evidence; no kernel guard,
reduction rule, library definition or default numeric type changes.

## Exact inputs and method

The [addition fixture](../../tests/fixtures/open-bnat-addition.cubist) contains
both functions `x => bnat_add(N, x)` and `x => bnat_add(x, N)` at each width:

| Width | Literal `N = 2^width - 1` |
| ---: | ---: |
| 32 | 4294967295 |
| 64 | 18446744073709551615 |
| 128 | 340282366920938463463374607431768211455 |

The [proof fixture](../../tests/fixtures/open-bnat-bitwise-proof.cubist)
contains a local structural bitwise proof of addition commutativity, then
specializes its first operand to each same literal while leaving `x` bound.
It recurses on `BPositive` bits and uses congruence/symmetry, with no conversion
to unary naturals. These local diagnostic definitions do not replace the
library's arithmetic laws and do not work around a failing test: the larger
proofs still fail the current full normalizer.

Every function is independently checked in its fixture. Each normalization
case uses a fresh Node process, loads the entire relevant fixture, obtains
an instruction-derived definition expression, and requests its full normal
form under the ordinary query API. Thus "open" refers to the bound operand
inside a closed function, not to an unchecked free variable. The normalizer
includes annotations and proof bodies. Declaration commits clear the reduction
caches. The literal remains
a checked decimal-parsing call, so the query includes decoding `N` using binary
multiplication and addition as part of normalizing the requested function. These
are end-to-end normalization counts, not isolated addition or proof costs.
The tool does not manually clear caches after deriving the definition handle.

```sh
make wasm
node tools/open-bnat-normalization-probe.mjs
# Or one exact case:
node tools/open-bnat-normalization-probe.mjs add_comm_64
```

The [probe](../../tools/open-bnat-normalization-probe.mjs) fixes normalization
at ten million kernel query-work ticks and a 30-second deadline, with no
larger-budget retry. It preserves the normal 512 syntax-depth and 1024 native
recursion guards. A controlled resource stop is a recorded outcome, not a
successful normalization. Other errors or incomplete checking fail the tool.
Complete output graphs are measured with an explicit stack and an independent
inspection bound; failed queries report `normalForm: null`.

## Current-kernel results

| Case | Outcome | Query work | New arena nodes | Distinct shared NF nodes / depth |
| --- | --- | ---: | ---: | ---: |
| Left addition, 32 bits | Normalized | 53,930 | 13,650 | 494 / 293 |
| Right addition, 32 bits | Normalized | 45,088 | 11,475 | 106 / 39 |
| Bitwise commutativity, 32 bits | Normalized | 78,387 | 18,891 | 1,476 / 380 |
| Left addition, 64 bits | Syntax depth > 512 | 206,706 | 45,305 | — |
| Right addition, 64 bits | Normalized | 188,908 | 40,913 | 138 / 71 |
| Bitwise commutativity, 64 bits | Syntax depth > 512 | 212,143 | 45,357 | — |
| Left addition, 128 bits | Syntax depth > 512 | 1,562,194 | 163,524 | — |
| Right addition, 128 bits | Normalized | 1,466,360 | 155,524 | 202 / 135 |
| Bitwise commutativity, 128 bits | Syntax depth > 512 | 1,560,793 | 163,576 | — |

All nine outcomes, work counts, allocations, complete graph metrics, arena
sizes and source hashes matched on a second full run. The
[raw measurements](open-bnat-normalization-baseline.json) record fixture and
kernel hashes, base revision, modified-tree status and paths, Node/platform, arena
bytes before/after, normalization time and process RSS. The measured source
checkout included the uncommitted fixture/probe additions; its kernel was
unchanged from `89f73ea1`.

Arena bytes describe the native arena's allocated capacity, not exact live
term bytes. Process RSS and maximum RSS include checking, the native kernel,
JavaScript and output inspection. Wall times and process memory are exploratory
single samples on Node 24.13.0 / macOS arm64, not performance guarantees.
Query work and new-node counters end before output inspection.

## Output depth versus traversal depth

A separate disposable diagnostic changed only `ck_make`'s syntax-depth guard
from 512 to 2048 and its error text. The raw artifact includes that exact patch
and the changed kernel hash. The 1024 native recursion guard, work budget,
deadline and all reduction rules stayed unchanged. The patch was then reverted
and the ordinary WASM kernel rebuilt. Other traversals, including substitution,
still depend on this syntax-depth bound to limit their native recursion. No overflow was detected in these diagnostic
runs; that does not establish that the enlarged depth is safe.

| Previously failing case | Diagnostic outcome | Query work | New arena nodes | Distinct shared NF nodes / depth |
| --- | --- | ---: | ---: | ---: |
| Left addition, 64 bits | Normalized | 209,897 | 45,432 | 974 / 581 |
| Left addition, 128 bits | Normalized | 1,573,119 | 164,739 | 1,934 / 1,157 |
| Bitwise commutativity, 64 bits | Normalized | 266,772 | 55,824 | 2,852 / 732 |
| Bitwise commutativity, 128 bits | Native reduction recursion limit | 1,635,475 | 177,846 | — |

The five cases that already completed retained their original work counts,
allocations and complete graph sizes. The larger addition outputs and 64-bit
proof are compact shared graphs whose depth exceeds 512. The 128-bit proof
exposes a second limit once the syntax guard is lifted. Its 177,846 allocations
are **not** a completed normal-form size, and this measurement does not establish
its eventual output size or termination within the fixed budget.

This distinguishes excessive output depth from unary expansion for these
specific addition cases and the completed 64-bit proof. It does not make a
claim about all BNat proofs, the separate mixed unary-law problem, or rational
Glue/composition normalization. Increasing the guard is only a measurement:
it leaves recursive traversal and other protected APIs unresolved.

## Gate for the structural change

Keep these source fixtures fixed while replacing the relevant recursive
traversals and readback. All nine complete-function requests must normalize
within the probe's fixed ten-million-work / 30-second bounds, without a
native or host recursion failure. Retain the WASM build's
`MAXIMUM_MEMORY=4294967296` (4 GiB), `STACK_SIZE=2097152` (2 MiB), and Node's
default stack; increasing any memory/stack limit or either the 512 syntax
guard or 1024 native recursion guard does not count as a fix.
Record complete output sizes and compare them with this baseline;
explain changes in sharing or representation without changing the conversion
rules. Remove a guard only after the traversals it protects have bounded
replacements. These fixtures measure kernel normalization; JavaScript decoding,
printing, expectation matching and driver comparison need separate EVAL4 checks.

If the evaluator changes the work unit or output representation, publish a
comparable baseline and explicit limits for both addition directions and
the proof cases before claiming this gate is met. The 128-bit proof's complete
size remains to be measured. The independent arithmetic-free quotient and
full rational-normalization gates remain required.
