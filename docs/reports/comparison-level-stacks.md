# Explicit comparison and universe-level traversals

This EVAL4 change replaces recursive syntactic comparison, comparison of
composition tube lists, cumulative-type descent, universe-level arithmetic,
and canonicalization of levels inside syntax. It builds on the
[substitution worklists](substitution-stack.md). It preserves comparison and
level rules, exact cache keys, traversal order and the 512 syntax-depth guard.
It does not close the remaining open-normalization or rational gates.

## Comparison scopes survive allocation

The recursive comparator kept a binder mapping in each native frame. A
heap-backed frame array can move, so simply moving those mappings into the
array would leave dangling pointers after growth. The new frames own their
bindings and refer to ancestors by indices. A binding's previous index
always identifies a live ancestor. Cache keys still use the existing
unique scope identifiers, not temporary frame indices.

Nearest-binding lookup and independent term/dimension scope pruning retain
the same behavior. Domains use the outer term scope; binder bodies use the
extended scope. Composition tube faces use the outer dimension scope and
bodies the extended scope. HComp's type and Path endpoints remain outside
their direction binders. Tube comparisons use the same worklist, including
their tails.

Universes and level applications still compare arithmetic level normal
forms. Bound level names are mapped through the same scope lookup. Declared
sort instances compare their recorded level lists arithmetically; PApp keeps
the existing comparison of its interval and path, without adding a new
comparison of its annotation. Definition references remain syntactic
references: this operation does not unfold definitions or reduce terms.

Completed equal and different answers retain full syntax/scope keys.
Failures publish neither answer. Cached, identical and leaf comparisons
return before pushing a frame. Cumulativity follows the old tail call in a
loop, comparing equal domains and then bodies instantiated with one fresh
variable, while preserving the direction of the universe inequality.

## Level normal forms have explicit owners

Successor chains remain iterative. A maximum now records its pending
operands in a worklist. After its first operand completes, the frame owns
that arithmetic normal form while the second is evaluated. Joining and
adding successors finish the parent; ownership transfers without retaining
pointers into the movable frame array. All pending forms are released on
failure. The existing query-local, 256-slot memo still owns separate copies
and retains exact completed syntax keys.

A separate syntax worklist canonicalizes universe levels and the level
argument of LApp, preserving other children and returning unchanged handles
where possible. Its completed results use the existing tag-4 memo. A failed
canonicalization returns zero, including failures while publishing an
immediate result to the memo.

Both comparison and level worklists start with 32 local frames, grow
geometrically, and stop at 16,384 frames. K374 and K375 report their
allocation failures. Existing conversion/level resource diagnostics cover
the explicit frame bounds; native-entry guards remain for calls from other
kernel operations. The syntax guard keeps these input traversals below the
explicit caps today, so tests exercise allocation and interruption paths,
not unreachable frame-cap branches.
Comparison and canonicalization now charge the shared native recursion
counter once per call, rather than once per syntax node. A traversal reached
from a deep caller can therefore complete where the old implementation
returned a native-recursion resource error; the computation rules are unchanged.

The WASM 2 MiB stack and 4 GiB memory limit, query budgets, deadlines and
mathematical definitions are unchanged. Worklist storage is temporary heap
storage and is not included in reported arena capacity.

## Validation

The existing native suites and undefined-behavior sanitization pass, including
the level arithmetic properties and comparison scope/cache tests. New native
tests run with syntax sharing both enabled and disabled:

- Two hundred nested binders retain an outer use, uses in domains and a
  distinct innermost use through repeated frame-array growth. A mismatched
  inner reference remains unequal.
- A 450-cell composition tube list compares under a renamed direction.
  A mismatch in its last face, or applying the inner renaming to outer faces,
  is rejected.
- Two hundred nested maximum/successor operations produce the expected
  constant and offsets for both variables. Both operand orders are tested:
  right descent retains allocated left normal forms in ancestor frames
  through spill, growth, budget interruption and memo-allocation failure.
- Level canonicalization beneath 450 syntax nodes preserves the other
  children, produces the expected level variable and reuses its completed
  result.
- Two hundred Pi binders preserve upward cumulativity and reject its reverse.
- Allocator injection interrupts the first spill and later reallocation.
  Arithmetic and canonicalization also stop on budget exhaustion after
  heap growth. A level-memo allocation fails after normal forms have been
  produced. Each failed operation is retried on the same kernel.
- An immediate canonicalization also returns failure when allocation of its
  shared memo fails, then succeeds on retry.

Ninety-seven targeted JavaScript tests pass: diagnostic discovery, quotient
descent, normalization sharing, universe-generic definitions, cumulativity,
the instruction driver, WASM kernel behavior and resource limits. The full
local JavaScript suite passes all 1,622 tests. At `cbe28bc7`,
[CI](https://github.com/KanHarI/cubist-math/actions/runs/39375754378) passed all
seven jobs, including four native compiler/OS combinations, ASan and UBSan,
the 1,622 JavaScript tests, browser checks and mutation contracts. That run
includes the immediate memo-publication failure case. CI's ASan supplies
the failure-path memory-safety checks; local UBSan alone does not check leaks
or double frees. The review follow-up reruns the full native and UBSan suites
with the mirrored arithmetic case and immediate memo-publication failure
in both sharing modes. Both pass. It changes tests and documentation only;
the executable kernel sources remain identical to the measured implementation.

## Fixed measurements

[Raw results](comparison-level-stacks-baseline.json) compare the source at
`44c47c49` with this implementation. Kernel source hashes are:

- Before: `4c97694183f1aaa48bfdd19c91b26b2bd2ce0e38a654d3f84eaaa51c6752bec5`.
- After: `ee8b2f32f6f15020809eec1457acbc3c0801adb18d78bb936cb9987400f22ce4`.

The fixed nine BNat cases and five quotient-free transport cases have identical
outcomes, work counts, allocations, reported arena sizes and completed graph
sizes/depths. Their input and dependency hashes match. Both generic quotient
cases retain identical outcomes, work and allocations; that probe does not
record input hashes, arena capacities or completed graph sizes. Run the
existing tools after building each checkout:

```sh
node tools/open-bnat-normalization-probe.mjs
node tools/transport-normalization-probe.mjs
node tools/quotient-normalization-probe.mjs
```

Five BNat cases complete and four still stop at the syntax guard. The three
cheap transports complete; `moved_setness` and `moved_path` still exhaust
10M work ticks. Both generic quotient cases continue to pass. These results
preserve the gates; they do not close the remaining failures.

Three serial before/after pairs also run the existing end-to-end controls:
set the working directory to each checkout, using the probe from the after
checkout in both runs.

```sh
node /path/to/after/tools/substitution-cost-probe.mjs
```

Every instruction/query counter, failure counter and reported final arena
count/capacity is identical across the two variants in every run. This
includes F4's 31,076,352-byte capacity inherited from the substitution
change. Temporary worklist memory is excluded, so this is not a claim about
identical peak memory or total allocation.

| Control | Median before (ms) | Median after (ms) |
| --- | ---: | ---: |
| F4 checking | 3,200.4 | 3,142.7 |
| Small quotient | 1,060.3 | 1,041.2 |
| Unshared quotient | 551.0 | 555.3 |
| Integer multiplication | 6,188.0 | 6,243.9 |
| Binary fraction field one | 6,891.1 | 7,021.1 |

Total-run medians are 17,894.5 ms before and 17,972.1 ms after (+0.4%).
The sample ranges overlap. These macOS arm64 observations establish neither
a portable speedup nor a regression bound.

### Investigating full-suite timing

The local full-suite run recorded fixture shard 1 at 287.9 seconds, compared
with 78.6 seconds in the earlier substitution run, and a free-generator test
at 52.1 versus 28.4 seconds. A separate serial before/after run checks those
observations on the same two kernels. The [probe](comparison-level-stacks-timing/probe.mjs)
retains shard 1's module order, assertions and shared-WASM lifecycle, and
records each program's work and arena after its observations, before disposal.
Run it from each built checkout; [raw results](comparison-level-stacks-timing/results.json)
also include the isolated free-generator test logs.

All 54 modules retain identical input hashes, instruction/query/failure
counters and reported arena counts/capacities. The summed module times are
82.0 seconds before and 72.8 seconds after. The isolated free-generator test
passes in both checkouts, at 28.6 and 26.3 seconds:

```sh
node --test --test-concurrency=1 \
  --test-name-pattern='free generators are independent of the new type and its generated namespace' \
  tests/initial-models.test.mjs
```

The large slowdown was not reproduced. This single matched pair does not
identify the cause of the earlier wall-clock observations or establish a
general speedup; no kernel change was made in response to those timings.

## Remaining protected traversals

The 512 syntax guard remains necessary. Recursive composition helpers
(`ck_append_tube`, `ck_clause_tubes`, `remove_empty_tubes`, `map_tubes`,
`substitute_tubes`), Glue's `projected_tubes`, HIT's `rename_tubes`,
the Glue-step reduction comparison (`normal_agree`/`parts_agree`),
prerequisite weak-head calls, and frontend decoding, printing, matching and
driver comparison still need bounded traversal work. The Glue-step comparison
uses weak heads and still recurses under its 1,024 guard. Comparing tube lists
here does not change those construction helpers.

This still evaluates and compares materialized syntax. Shared cubical
execution and complete typed readback remain subject to the unchanged
transport and full-rational gates. No equality rule, proof irrelevance or
constant-transport regularity is added.
