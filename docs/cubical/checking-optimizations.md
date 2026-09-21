# Native checking performance

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
