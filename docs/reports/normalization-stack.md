# Explicit continuations for full normalization

This EVAL4 change replaces the native full normalizer's recursive traversal
with an explicit continuation stack. It preserves child order, weak-head
reduction, annotation/proof normalization, partial-face restriction, eta side
conditions and exact-handle caching. It changes no mathematical definitions
or computation rules. The rational full-normalization failure remains open.

## Behavior and limits

The old full normalizer kept a native frame for every pending child, every
new reduct needing another full pass, and normalization of restricted Glue
eta boundaries. A long chain of individually shallow, checked definitions
could therefore exhaust native recursion before rebuilding its output.

`ck_normal` now schedules all three kinds of work in one loop. Frames retain
node copies and arena handles, not borrowed pointers. Glue eta resumes each
face clause after fully normalizing the restricted value; it never substitutes
weak-head equality or conversion for that syntactic side condition. Face
clauses are copied before restriction, and the face is looked up again after
resuming because formula storage may move.

The first 32 frames use local storage. Further frames use geometrically grown
heap storage, capped at 16,384 frames and released on every exit. The existing
K337 resource error covers exhausting that explicit depth bound; K369 reports
allocation failure. This adds bounded transient storage within the unchanged
WASM memory ceiling. The arena counter measures retained native capacity and
does not include this temporary stack; no peak-memory improvement is claimed.

A node enters the completed-normal-form cache only after all children,
applicable Glue side conditions and any new reduct finish. Completed siblings
remain usable after an interrupted parent. Budget/deadline accounting remains
at the same reduction, cache-hit and syntax operations; bookkeeping does not
invent a new work unit. The loop cannot accumulate frames without traversing
budgeted work. Native re-entry through other reducer APIs remains guarded.

The 512 syntax-depth bound and 1024 native recursion guard in other reducers
remain. Substitution, weak-head reduction, comparison and frontend decoding or
printing still need their own bounded traversal work. This is one prerequisite
for that replacement, not completion of EVAL4 or permission to raise either
guard. In particular, the fixed 64/128-bit left-addition and proof cases still
fail the syntax guard.

## Validation

- A chain of 2,200 closed sum-type definitions, each derived through ordinary
  instructions, now reaches the retained output syntax-depth guard. With the
  old normalizer the same regression instead reaches native normal-form depth.
  A completed 400-layer prefix remains cached with the expected sum graph.
- Interruption after heap growth leaves the unfinished parent uncached and
  allows retry. A 17,000-definition chain reaches the explicit frame bound
  without poisoning a subsequent query: a new uncached 400-layer graph then
  fully normalizes. No guard is raised for these tests.
- Test-only allocator injection covers both initial allocation and later
  reallocation failure, followed by successful normalization on the same
  kernel. Allocation-call counts also verify that budget interruption occurs
  after heap growth. Production allocators are unchanged.
- Glue boundary regressions require endpoint normalization on both clauses of
  a disjunctive face, and refuse candidates mismatching either clause or a
  later piece. Mutants checking only the first or only the last clause both
  fail the regression. Both syntax-sharing modes are exercised. Existing tests cover normalized new reducts, capture,
  restriction scope, deadlines, rollback/compaction and failed-parent caches.
- All native suites pass normally and with undefined-behavior sanitization.
  The existing JavaScript normalization and diagnostic suites pass (12 tests).

The fixed nine-case baseline from PR #290 was copied unchanged into the
measurement checkout. Every outcome, query-work count, new-node allocation and
completed graph size/depth matches its baseline. Decimal parsing remains part
of those counts. The independent arithmetic-free quotient probe is unchanged:
Unit completes in 5,117 query-work ticks with 1,156 new nodes; Prop exhausts
10,000,000 ticks with 2,028,800 new nodes. Explicit continuations alone do not
resolve that expansion.

A separate disposable diagnostic repeated PR #290's temporary syntax guard
change from 512 to 2048, using this PR's normalizer. All nine cases then
completed under the same ten-million-work budget and 30-second deadline.
The previously failing 128-bit bitwise proof completed in 1,689,761 work ticks,
with 185,436 new arena nodes and a final shared graph of **5,604 nodes at depth
1,436**. Its old diagnostic stopped at native recursion without a completed
normal form. The other eight diagnostic cases retain their work, allocations
and normal-form sizes exactly. This isolates the removed full-normalization
frames as the cause of that particular recursion failure.

The [raw diagnostic measurements](normalization-stack-depth.json) record the
kernel/fixture hashes and exact temporary guard patch. Both changed kernel
files were restored in the disposable checkout and its original WASM rebuilt.
The production syntax guard remains 512. Other traversals still rely on it;
completion in this diagnostic does not establish that lifting it is safe or
close the production EVAL4 acceptance gate.

The first local run of the existing four-case quotient regression took about
16 minutes. The same test file was then run serially on PR #288's `eb81c10d`
checkout (kernel identical to main `89f73ea1`) and this implementation on the same machine (Node 24.13.0, macOS arm64): all seven
tests passed in 19.85 seconds before and 19.83 seconds after. A direct comparison
of the four quotient cases, preserving the test's shared WASM-module lifecycle,
also kept all instruction/query counters and arena counts identical:

| Case | Before | After |
| --- | ---: | ---: |
| Small quotient | 2.22 s | 2.18 s |
| Unary quotient, syntax sharing disabled | 0.62 s | 0.54 s |
| Open integer multiplication | 8.03 s | 7.74 s |
| Binary fraction field's one | 8.77 s | 8.74 s |

These are individual observations, not benchmark medians or a portable speedup
claim. The earlier long run remains an unexplained outlier; it did not repeat
in the paired checks. The exact test-runner command in either checkout is
`node --test tests/normalization-sharing.test.mjs` after building its kernel.
