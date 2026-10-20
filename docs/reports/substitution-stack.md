# Bounded substitution and dependency traversals

This EVAL4 change replaces native recursion in term substitution, dimension
substitution, composition-tube traversal and free-variable/dimension analysis.
It preserves the existing substitution rules and keeps the 512 syntax-depth
guard. It does not complete EVAL4 or rational full normalization.

## One substitution work loop

Term substitution can require renaming a term binder or a dimension binder.
Dimension renaming can traverse composition tubes, whose bodies and faces
have different scopes. Moving only the ordinary child walk to a loop would
leave recursion through those capture-avoidance operations.

All three operations now use one continuation stack. Cached, unchanged and
variable-only requests return before allocating a frame, including child
requests. A frame keeps the
original term and substitution key, a copy of the node being rebuilt, and
the next operation. Renaming, ordinary children and tube tails are scheduled
on this same stack. The frame waits for its child before continuing, retaining
the previous traversal order:

- A term binder scopes over its body, not its domain.
- A path direction scopes over the family, not its endpoints.
- A composition direction scopes over the family and tube bodies, not tube
  faces or the starting lid. A homogeneous composition's type is unbound.
- Renaming a dimension visits only those bound positions. The requested
  substitution subsequently visits every position where its name is free.

Frames contain node copies and formula descriptors whose immutable clause
storage remains alive for the query. They do not retain pointers into the
node or formula arrays that can move during allocation. A replacement term's
free dimensions are still considered when avoiding capture.

The first 32 frames are local. Heap growth is geometric, with an explicit
16,384-frame bound. Every exit frees the temporary stack. K372 reports a
failed allocation; K373 reports the frame bound. Successful children can
remain memoized after a parent fails; incomplete parents are not published.
The operation, original term, substituted name and replacement remain the
complete substitution memo key.

## Dependency analysis

Free-term-variable analysis uses an explicit depth-first stack and retains
its existing per-name memo, conservative symbol mask and short-circuiting.
Free-dimension analysis uses a postorder stack and records the completed
exact mask on the immutable syntax node. An unfinished scan leaves the
conservative mask intact. This prevents ordinary substitution-memo eviction
from forcing the same dimension analysis repeatedly.

The completion flag fits existing node padding: native syntax nodes remain
48 bytes on the measured platform. New nodes initialize the flag, rollback
reuses no stale result, and compaction preserves the exact mask. Scan stacks
spill after 32 frames and use the input graph's recorded depth as their
allocation bound. K370 and K371 report dimension- and variable-scan allocation
failure respectively.

These stacks add temporary storage under the existing WASM memory limit;
arena counters do not include that storage. Work and deadlines still apply
to the visited syntax operations. Fewer dimension scans can permit more
syntax allocation before a fixed work budget is exhausted, so lower work is
not by itself a memory improvement.

## Recorded regression controls

[Raw measurements](substitution-stack-baseline.json) compare the merged #293
sources with this change. The before checkout is `c6ed71e5`, whose sources
are identical to merge commit `694882af`. The measured kernel source hashes
are:

- Before: `58bc1ccacb5e75c531c3145038da2a40acc3b10270b856566aeef4692259e9db`.
- After: `99fde6aea96a719687de0895eecbf5b5f37f44d3dc493c268eba196f93fa2443`.

The unchanged fixed probes use 10M work ticks and a 30-second deadline:

```sh
node tools/open-bnat-normalization-probe.mjs
node tools/transport-normalization-probe.mjs
node tools/quotient-normalization-probe.mjs
```

All nine BNat outcomes remain unchanged: five complete with identical graph
sizes and allocation counts, and four stop at the unchanged syntax-depth
guard. Generic quotient `to_unit` work falls from 2,699 to 2,686 ticks and
`to_prop` from 2,272 to 2,240; allocations remain 587 and 459. The completed
transport controls retain their graph sizes and allocations too.
`moved_setness` still exhausts 10M ticks, allocating 2,765,343 nodes versus
2,526,247 before; `moved_path` also exhausts 10M, allocating 2,807,511 versus
2,602,450. Both retain the same 269,092,352-byte reported arena capacity.
These are failures at different progress points, not completed normal forms
or a memory improvement.

The separate end-to-end controls use their existing 40M per-query maximum.
Run the same script from each checkout, after building that checkout:

```sh
node /path/to/after/tools/substitution-cost-probe.mjs
```

Three serial before/after pairs include module imports, checking and the
requested full normalizations. All five controls pass in every run, with
identical deterministic counters within each variant and matching input and
dependency hashes across variants. F4 is an import/check control; it does not
request a separate evaluation.

| Control | Work before | Work after | Median before (ms) | Median after (ms) |
| --- | ---: | ---: | ---: | ---: |
| F4 checking | 5,759,889 | 5,553,440 | 3,138.6 | 3,224.4 |
| Small quotient | 2,956,985 | 2,586,579 | 1,086.2 | 1,081.9 |
| Unshared quotient | 700,296 | 696,230 | 553.0 | 567.5 |
| Integer multiplication | 9,482,649 | 8,567,376 | 6,312.7 | 6,347.8 |
| Binary fraction field one | 9,988,243 | 9,284,415 | 7,054.4 | 7,144.8 |

Work is instruction work plus query work, including internal retries. Lower
work counts do not establish a throughput improvement. Total timing medians
are 18,135.9 ms before and 18,352.0 ms after (+1.2%); the three total samples
overlap. F4's median is 2.7% higher. These macOS arm64 observations expose a
small measured cost of this stack-safety change, not a portable regression
bound. Four controls retain identical final arena node counts; the unshared
quotient retains 10,320 instead of 10,297 (+23). The script records arena
capacity, which excludes temporary continuation storage.

## Validation and remaining gates

The native tests cover all 64 dimension names, annotation dependencies,
Path/PLam/Comp/HComp/Trans scopes, term and level binders, nested shadowing,
cross-namespace capture and long tube lists. Both syntax-sharing modes are
tested. Allocator injection interrupts the initial stack spill and later
reallocation, then retries on the same kernel. Budget interruption, memo
pressure, rollback and checked-definition compaction are also covered.

The full native suites and undefined-behavior sanitization pass. Targeted
JavaScript runs cover quotient normalization, generated h-level evidence,
capture/refusal contracts and dimension-slot assignment. Diagnostic discovery
retains the three existing formula-substitution messages after their code
was consolidated into a helper.

The fixed 32/64/128-bit addition and bitwise-proof fixtures retain all nine
outcomes, allocation counts and completed graph sizes. Larger left-addition
and proof cases still reach the syntax-depth guard. The generic quotient
regression added in #293 remains passing. The three cheap quotient-free
transport controls retain their completed graphs; `moved_setness` and
`moved_path` still exhaust the fixed 10M budget.

The existing WASM 2 MiB stack and 4 GiB memory ceiling, Node's default stack,
normalization budgets and mathematical definitions are unchanged. Recursive
alpha comparison, universe-level analysis, prerequisite weak-head queries
and frontend decoding/printing remain separate traversal work. This change
does not introduce closures or delayed substitution values: substitution
still produces syntax. Shared cubical evaluation and full typed readback
remain subject to the unchanged transport and complete-rational gates.
