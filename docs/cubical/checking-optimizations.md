# Native checking performance

## September 23: polynomial and extension checks

The expanded corpus has 3,573 concrete declarations and 44 universe templates.
Before this pass, the 100 ms run checked 3,446 declarations, timed out on six,
and blocked 121 dependents. A diagnostic run at one second checked everything;
the slowest declaration took 480 ms.

Conversion now reuses successful equality comparisons as well as folded syntax
comparisons. The exact key contains both term handles and both binder-renaming
scopes. Success is valid independently of the unfolding strategy; a cached
failure applies only to folded syntax. Failures from reduction or hint passes
are not cached. Directed universe cumulativity is not stored as equality.

Renaming scopes are interned by the exact triple (parent scope, left name, right
name). A collision evicts an entry; its identity is never assigned to another
chain. Identity renamings use the empty scope for comparison lookup, since they
preserve precisely the same name equalities. Their complete parent chains are
still retained when extending a renaming. Hashing mixes high bits of sequential
handles and names to reduce collisions in the fixed-size tables. The extra
scope table is bounded at 192 KiB per kernel session; allocation failure simply
disables scope interning. Existing rollback and compaction invalidate all cached
comparisons before handles are reused. The scope table contains only names and
chain identities, so it does not retain arena handles.

Two existing proof blocks also prioritize the small wrappers `FieldTower` and
`EmbeddingTowerFiber`. These hints expose the expected type without expanding
the constructed residue field. Statements, proof premises, and axioms are
unchanged; every resulting conversion still goes through the C checker.

The complete 100 ms Node run now checks all 3,573 declarations, with zero slow,
blocked, or failed entries, in 10.14 s. Observed timings on Apple M3 Pro / Node
24.13.0 (the before column uses the one-second diagnostic):

| Declaration | Before (ms) | After (ms) |
| --- | ---: | ---: |
| `finite_separable_count_step` | 479.6 | 93.1 |
| `finite_embedding_extension_step` | 292.2 | 76.6 |
| `generated_algebraic_finite_step` | 335.4 | 65.3 |

Regression coverage includes free versus bound names, shadowing, term and
interval renamings, repeated beta-convertible DAGs, changing hints, arena handle
reuse after rollback, and rejection of downward universe conversion.
Validation passed: all 283 automated tests, the native C regression suite,
undefined-behavior sanitizer checks for conversion/hints/checkpoints/check
caches, and all 348 source-format checks. The browser proof/workbench tests
also passed; its live corpus worker independently checked all 3,573 concrete
declarations within 100 ms, with no slow, blocked, or failed entries.

## September 21 baseline

The 100 ms performance pass starts from the completed native migration:
2,484 concrete declarations, 16 universe templates, and no rejected proofs.
Twenty-six declarations exceeded 100 ms in the saved one-second scan. The
slowest was `group_objects_iso_total_path` at 574 ms; the whole scan took 17.43 s.
This is a wall-clock target, not a kernel rule or a portable timing guarantee.

## Exact syntax sharing

`ck_make` validates every constructor and child before looking in a bounded
interning table. A hit requires equal constructor, payload, and all four child
handles. Hash collisions only evict entries. A syntax handle is still inert:
sharing it does not establish a typing judgement. The table is cleared on
rollback and compaction, because arena handles may then be reused or relocated.
Allocation failure simply disables this optional cache.

Term binders retain their names when fresh for the checked context. A shadowing
binder is renamed with capture-avoiding substitution as before. This avoids
copying the entire body at every check and preserves useful sharing. Folded
conversion may immediately accept an identical handle under identical binder
renamings; a nonidentity renaming still requires the scoped comparison. Term
and dimension renamings are both considered.

## Reuse of successful native judgements

`check_cache.c` stores successful inference results only. Its exact key is the
raw term handle, the context identity, and the full 64-bit interval scope.
The reconstructed checked expression is also a valid cache key for that same
judgement. Expected-type checking still checks the expected type and performs
the usual directed conversion; an inference hit cannot approve an arbitrary
expected type.

Contexts are interned by the exact triple (parent identity, variable name,
checked type handle). Their identities increase monotonically and never refer
to stack addresses. A hash collision receives a different identity; it cannot
alias a different telescope. Face restriction builds new context identities
using the restricted types. Both context and judgement caches are discarded
on rollback and compaction. Failed checks never enter the cache. A valid
subjudgement discovered while checking a subsequently rejected parent remains
valid in its original scope, just as it would if checked independently.

These caches do not add a logical rule or trust the JavaScript elaborator.
The native tests exercise changed assumptions, wrong expected types, unbound
variables, missing interval dimensions, shadowing, context hash collisions,
and arena rollback with both switches independently on and off.

## Compact path signatures

The elaborator gives `sym(p)`, `trans(p,q)`, and `cong(f,p)` the endpoints
specified by their mathematical operations. It expresses each signature as
application of a typed identity function to the ordinary cubical proof term.
The C checker verifies both that term and conversion to the stated signature.
This prevents later inference from rebuilding enormous composition expressions
merely to recover their endpoints. Local `have` lemmas also retain their declared signatures through the same
checked identity application. No custom conversion hint, axiom, or trusted
annotation is involved. The inspector can still expose the underlying term.

The free-assumption collector and hygienic equivalence-term name selection
also visit shared syntax as a DAG rather than repeatedly traversing each copy.
The former computes free variables per subtree, removes a binder from its body
only, and then closes over dependencies in assumption types. This preserves
the explicit axiom inventory.

## Reuse of generic computational univalence

The closed derivations of `ua` and `UnivalenceBeta` are checked and named once
per concrete universe. Subsequent uses apply these ordinary definitions to the
carrier types, equivalence, and element, checking every argument. This uses the
same specialization mechanism as universe-polymorphic library definitions and
is controlled by **Reuse checked terms**. It avoids rebuilding the Glue
construction at every occurrence; it does not introduce a univalence axiom.

## Proof simplification

`polynomial_difference_step` previously expanded and cancelled many ring terms
in over 400 lines. Its new proof first writes `x = r + (x-r)`, distributes once,
moves `x` past `(x-r)`, and factors `(x-r)` back out. The theorem statement and
ring assumptions are unchanged. Both the original Id/J kernel and cubical C
check this source.

The benchmark and proof viewer expose independent **Share identical syntax**,
**Reuse checked terms**, and **Keep compact path types** switches, enabled by
default. CLI equivalents and measurement methodology are documented in
[benchmark.md](benchmark.md). Persistent tables use bounded memory; they do not
grow with the number of successful rechecks.

## Measured result

The final complete Node scan checked all 2,484 concrete declarations below
100 ms: zero slow, blocked, or failed entries, plus 16 universe templates.
Elapsed time fell from 17.43 s to 4.81 s (about 3.6× faster). The new maximum
was 47.234 ms. The browser run also checked all concrete declarations within
100 ms. Both runs used all three optimizations; Node was 24.13.0 on Apple M3 Pro.

| Declaration | Before (ms) | After (ms) |
| --- | ---: | ---: |
| `group_objects_iso_total_path` | 574.083 | 17.072 |
| `polynomial_difference_step` | 513.667 | 10.519 |
| `complex_coordinate_norm_product` | 393.717 | 12.600 |
| `f4_symmetry_add` | 375.412 | 31.096 |
| `radix_nat_equiv` | 326.153 | 31.701 |

Validation: native kernel regression suite; undefined-behavior sanitizer runs
for inference-cache, conversion, and checkpoint regressions; 50 focused JS
checks; original-kernel validation of the shortened polynomial proof; browser
proof/inspector/workbench flows, optimization controls, and live corpus runner.
The saved benchmark records its source revision, working-tree state, settings,
and timing environment.
