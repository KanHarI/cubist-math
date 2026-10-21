# Iterative weak-head tail reduction

This EVAL4 change follows the [full-normalization stack](normalization-stack.md).
A chain of 4,096 separately checked, closed definitions, each naming the
previous Unit value, still failed at the native recursion guard: a weak-head
query stopped after 1,025 work ticks, and full normalization after 1,024.
The output is a single point; neither syntax depth nor mathematical work
requires thousands of pending native calls.

## Change and remaining limits

Tail requests in `weak` now schedule their next term in a loop. This covers
definition unfolding, ordinary/level/path beta, path endpoints, eliminator
results, pair projections and the existing eta/Glue contractions. It preserves
the rules, their prerequisites and their order. Path substitution finishes
before its copied interval formula is freed and the next head is requested.

The loop retains the syntax handles whose completed head will be cached.
The first 32 use local storage; further handles use geometric heap growth,
up to 16,384 retained handles per invocation (64 KiB of handle storage). At that
bound reduction continues without retaining further intermediate handles for
caching. The work budget and deadline still bound execution; cache capacity
does not impose another reduction-depth limit. Allocation failure uses K369.
All exits release the buffer. Failed or interrupted chains publish no pending
cache entries; completed prerequisite queries retain their results.
Every tail advance still charges the same query tick and checks the exact
weak-head cache. A warm query still costs one tick.
Total pending storage across nested requests is bounded by the budgeted tail
advances; each retained handle follows a reduction step.

Prerequisite head queries and composition helpers remain native calls under
the unchanged 1,024 recursion guard. The 512 syntax-depth guard, WASM stack
and memory ceilings also remain. Thus this removes tail-chain recursion; it
does not make all weak-head reduction iterative, permit removing the guards,
or complete EVAL4. Buffer storage is transient and is not included in the
retained arena counter. No overall memory reduction is claimed.

A divergent raw, unchecked beta term now stops at its query budget instead of
the former tail-recursion guard. JavaScript's existing growing-budget wrapper
can retry up to its configured ceiling; callers needing a shorter bound must
set a smaller maximum query budget or a deadline. This does not make such syntax a checked
term or produce evidence from a query.

## Validation

- With syntax sharing both on and off, the 4,096-alias chain now reaches the
  point in 4,097 ticks. Interruption at 200 ticks leaves the unfinished chain
  uncached; retry succeeds, and an intermediate alias then takes one tick.
  A checked chain alternating 2,000 definition and beta reductions also fully
  normalizes.
- A 21,000-definition chain finishes after exceeding the memo capacity;
  omitted intermediates compute correctly on a later query. Interruption
  after memo saturation leaves no unfinished result cached. A fresh beta
  redex succeeds afterwards. Test-only allocator failures cover
  initial allocation and reallocation, followed by successful retry. The
  budget test verifies that heap growth happened before interruption.
  An unchecked self-applying beta term also stops at its fixed work budget,
  leaves no cyclic result cached and permits the next checked query.
- Replacing only the new reducer with its parent version makes the alias
  regression fail at its successful-head assertion. Restoring the reducer
  passes all native suites and undefined-behavior sanitization.
- The WASM regression checks the same alias chain in both sharing modes,
  including budget recovery, cold and warm head counts, and a fresh-kernel
  full-normalization instruction deriving an assumption-free equality.
  It uses the ordinary 2 MiB WASM stack and default Node stack.
  A separate 1,100-level chain of nested Unit eliminators reaches the retained
  native recursion diagnostic in both sharing modes, with successful recovery
  and no host stack overflow.
- The existing JavaScript normalization and diagnostic suites pass (14
  tests). Three alternating, serial runs of the exact normalization test file
  on parent `841ad02d` and this change pass all seven tests in every run.
  Median process elapsed time is 21.00 seconds before and 20.92 seconds after
  (Node 24.13.0, macOS arm64). The samples overlap; no portable speedup is
  claimed. The command in each checkout is
  `node --test tests/normalization-sharing.test.mjs` after building its kernel.

The unchanged nine-case [open BNat baseline](https://github.com/KanHarI/cubist-math/pull/290)
was copied into this worktree for measurement. All nine outcomes, work counts,
new-node allocations and completed normal-form sizes/depths match exactly.
The production syntax-depth failures remain failures. The arithmetic-free
quotient probe likewise remains unchanged: Unit completes in 5,117 ticks and
1,156 new nodes; Prop exhausts 10,000,000 ticks with 2,028,800 new nodes.
The generic quotient/rational full-normalization failure remains open.
