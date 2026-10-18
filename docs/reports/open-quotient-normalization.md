# Open quotient normalization and kernel API audit

Full normalization of `bint_mul` on main after #280 repeatedly expanded the
proofs used to lift multiplication through the quotient. The pair operation
`(a,b) * (c,d) = (ac+bd, ad+bc)` was not the expensive part: its open function
normalized in about 5 ms in the diagnostic run. The quotient's relation and
squash clauses generated compositions and transports whose normalization
grew until the arena or diagnostic deadline was exhausted.

Two interacting causes were found:

- Full normalization visited composition walls outside their face conditions.
  Generated walls can still contain coordinates fixed by their face. Expanding
  those off-face values computes irrelevant transport corrections.
- Dimension substitution, used by path beta and restrictions, traversed shared
  syntax repeatedly. Ordinary term substitution already had a memo, but its
  dimension counterpart did not.

The fix restricts a partial body by the endpoint conditions common to every
clause of its face before normalizing it. It keeps the original face and piece
order, including for disjunctions; splitting into ordered clauses would make
normal forms sensitive to dimension renaming. Only the restricted term's
normalization is cached, so the restriction does not affect an unrestricted
use of the original body. The same rule applies to Glue's partial types and
equivalences. A newly exposed constructor can enable composition or an
enclosing eliminator to reduce; that result must itself be fully normalized.
Opus's first review identified this missing final pass, and a sum-composition
regression now requires idempotence and a fully reduced constructor argument.
No constant-transport regularity rule is introduced.

Dimension substitution now memoizes the complete operation: source handle,
dimension and exact interned interval formula. The formula descriptor is kept
by value across recursive formula interning, which can move the formula arena.
Capture avoidance, composition's different scopes for faces and wall bodies,
and the existing rollback/compaction invalidation remain in force.

## Related failures found in the API scan

The scan covered normalization, weak-head reduction, term/dimension renaming,
endpoint restriction, alpha comparison, universe-level operations, partial
systems, and their cache/error lifecycles.

- **Shared universe levels:** the old level normalizer expanded a compact DAG
  as a tree; its test explicitly expected exhaustion. A bounded, query-local
  cache now owns copies of completed arithmetic normal forms. It does not
  convert them into canonical syntax, so equality/order acquire no extra term
  depth limit. Both successful and failed queries release the cache.
- **Warm term renaming:** a memo hit could bypass the deadline and take no
  budget step. Hits now charge a step, as normalization and comparison do.
- **Interrupted free-variable scans:** substitution could return the original
  term while the scan had recorded an error. Term and dimension substitution
  now return failure; no incomplete result is published in the memo. Retrying
  with sufficient budget computes the actual substitution.
- **Borrowed formula descriptors in checking instructions:** `SystemTube`,
  `Trans`, `GluePiece` and `GlueTermPiece` could read a descriptor after
  restriction moved its arena. Context extraction now accepts a stable formula
  ID and looks it up at use; `Trans` retains its loop's descriptor by value.
  An actual `SystemTube` regression forces arena growth during restriction.
- **Recursion-counter recovery:** normalization resets the query's recursion
  counter, and rebuilding a selected subterm restores it on depth overflow.

These are changes to computation and error handling. Instructions still check
their premises independently; syntax queries do not certify typing. No library
proofs, arithmetic definitions, arena/depth limits or production budgets change.

## Regression coverage

`kernel/tests/test_normalize.c` exercises shared path substitution with syntax
interning on and off, capture avoidance, formula-arena growth during recursion,
rollback handle reuse, warm deadlines,
interrupted-query recovery, disjunctive faces and independent Glue pieces.
`kernel/tests/test_levels.c` checks repeated and diamond-shaped shared levels,
interruption/recovery, and a 1,024-variable arithmetic normal form whose
canonical term would exceed the syntax depth bound. Its existing 1,500 random
level-pair comparisons against independent arithmetic evaluation remain.

`tests/fixtures/quotient-normalization.cubist` reproduces the quotient issue
using only `Unit`, with no integer arithmetic. The WebAssembly regression
fully normalizes that operation, `bint_mul`, and the binary fraction field's
`one` under a fixed test work budget.
The `_` expectation still requires a full normal form.

## Initial validation and measurements

The measurements below precede the first review's final-pass and instruction
formula-lifetime fixes; they describe `5fab7771`, not the final reviewed head.

All native suites pass, including UBSan. The local full suite passed 1,516 of
1,517 tests; its sole failure was two unregistered error messages. Those now
reuse existing diagnostics, and all 12 diagnostic/normalization tests pass.
All seven CI jobs, including the full workbench suite, pass at `0f442893`.
The additional formula-arena regression passes the full UBSan suite too.

The existing evaluation-baseline tests retain their exact outcomes and normal
form digests within the unchanged work/allocation bounds. A second normalization
of both the minimal quotient and `bint_mul` is alpha-equal to the first.
Using #281's integer-domain source overlay with this kernel, the binary fraction
field's `one` also fully normalizes: about 668 ms for normalization and 1.90 s
for the entry in the final diagnostic run, with 2.10 million live arena nodes.
These figures are local observations, not portable performance thresholds.

The [F4 comparison](open-quotient-f4-comparison.json) repeats three alternating
before/after pairs. All declarations and the selected Galois-group theorem
derive in every run. Median module checking stays at 3.7 s; the selected
derivation changes from 14.6 ms to 15.0 ms, with overlapping sample ranges.
Its counted instruction/query work increases from 200,349 to 227,322 steps
(13.5%); cache hits now count as work. No general speedup or exact timing
equality is claimed. The regression baselines and production budgets are unchanged.
