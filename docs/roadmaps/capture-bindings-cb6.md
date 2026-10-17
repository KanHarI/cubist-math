# CB6: contextual REPL

Status: complete and merged in #239, following CB5 #238. Final validation and
the eighth Claude review were clean on `cb1cdc2c`. Reconciled on 2026-10-17
against main `e729c2d5`: CB7 retirement/release (#240) and the separate cleanup
(#241) are also merged. The evidence below remains pinned to the CB6 checkpoint.

## Implemented behavior

Source and Generated Cubist views open an explicit picker for exact retained
scope instances. Source-qualified ranges, declaration identities, parent paths
and instance numbers distinguish copied and multiply elaborated occurrences.
The inspector also offers **Open REPL in this context** beside Context, including
embedded views. It opens the exact inspected occurrence; a binder introduction
can have a different context from a later use. If collection is off, it checks
the unchanged source with collection enabled, preserves the inspection, and opens
its new scope. Dirty source, changed inspection and delayed replies invalidate
the request. Generated coherence obligations have their own goal entry.

Reference observations consume existing semantic scope entries. They never
create IDs or recover an entry by nearby range or label. The synchronous active
stack matches the actual scope object and retains only its point ID in a view.
Binder introduction and automatic coherence elaboration establish semantic
entries independently of optional reference collection.

Discarded speculative attempts have no selectable context. Inductive signatures
expose the provisional self type and earlier constructors before final admission,
including initial/free generated declarations; later constructors stay absent.

The existing console supports expressions, `typeof`, `evaluate`, inspection,
closed witness readout, scratch lets, `/locals`, `/goal` and `/prove { ... }`.
Queries preserve visible and shadowed bindings, branch refinements, dimensions,
model evidence, notation, section applications and structural recursion rules.
Experiments are conditional on the selected context and never publish into or
edit source. Failed entries preserve accepted scratch history. The module REPL
retains its separate behavior and history.

Each request replays the full ordered declaration prefix and imports in a fresh
native kernel handle, then runs synchronously at the exact scope callback. It
compares the inert scope description and independently checks the reconstructed
context. Scratch history replays with binding correspondence. No live scope or
native handle survives the callback; failed replay reports its actual fuel,
kernel-budget or deadline reason. Budgets and retry caps are unchanged.

Copied query graphs preserve lazy operand caller scopes and mutable recursion
permission sharing, without compiler match continuations. Operand forcing spends
the query's fuel and uses its fresh-name supply. Listing an operand never forces
it. The exact invocation's notation context grants visibility; identity receipts
alone grant none. Model numerals retain authored definition and view links.

Private receipts preserve hidden values and their refinement behavior. The
semantic-local inventory separately tracks source shadowing. A foreign notation
body starts its own lexical-local inventory and inherits caller definitions as
implicit proof evidence; both proof-search consumers use the same enumeration.
Refinement, faces, isolated copying and replay descriptions preserve those terms.
No separate resolver, registry or namespace framework was introduced.

The worker uses one FIFO for checks and queries, with immediate capability
revocation on edits and submitted rechecks. Stale checks cannot publish selectable
contexts. Closing, disposal and compiler replacement revoke sessions; epoch and
selection checks discard delayed opening, index and query responses. Queries use
the existing finite watchdog without changing compiler resource policy.

Scope collection is opt-in. Historical name-based notation contexts remain
explicitly unavailable because their selection descriptions are incomplete;
observation preserves their existing source checking. Current-language contexts
have no migration guard. CB7 audits the historical adapter separately.

## Contract coverage and final gates

All ten original contextual TODO placeholders now have executable coverage:

| Original contract | Distinguishing coverage |
| --- | --- |
| Nested induction | Distinct hypotheses, branch contexts and scratch history |
| Branch instance set | Different wildcard refinements/verdicts; explicit browser picker |
| Discarded path body | Discarded attempt has no selectable instance |
| Proof goal | Goal display, proof success/refusal, unchanged source/history |
| Two-session isolation | Separate native sessions and scratch bindings |
| Source/import revisions | Pinned inputs, new IDs and immediate revocation |
| Ordered prefix/accounting | Complete imports/prefix, failed directives and original resource policy |
| Fuel/budget/deadline exhaustion | Distinct stopping reasons, no fallback context or query execution |
| Failed scratch-history replay | Failed entry reported, history preserved, later replay succeeds |
| Cancellation/disposal | Revocation during loading, closure/replacement and delayed replies |

The source controls also distinguish hidden evidence from saved aliases, foreign
notation names from caller shadowing, exact generated instances, recursive calls
from invalid recursion, and provisional constructors from unavailable later ones.
Observation on/off preserves verdicts, links, deterministic fuel and kernel work
on the covered fixtures. All 367 canonical `notation_literals` links match CB5.

At `cb1cdc2c`, `npm test` passes 1,332/1,332 tests, zero failures, skips or TODOs,
including all 3,857 canonical checks. Both contextual and inspector browser suites
pass; the contextual suite has seven groups including on-demand and embedded
inspector entry. All four production mutations are killed at the same clean
revision. The focused completion gate passes 38 tests, including generated
coherence queries and cold/warm aggregate description limits.

Earlier failures remain recorded: missing diagnostic registration, a browser
predicate race, and a UI completion path that skipped control refresh. They are
not represented as passing runs. The final gates above include their corrections.
Native tests and the static-site browser suite pass at the earlier `3b9a0845`;
CB7 must record final release validation after retirement.

## External review

Before each correction, shared causes were compared with earlier rounds in the
[review-root record](../reports/capture-bindings-review-roots.md).

| Round | Result and correction |
| --- | --- |
| 1 | Four findings: observation aliases granted search visibility, lazy refinement used an optional registry, numeral origins lost authored links, and inductive labels reused a definition-only diagnostic. Fix the corresponding shared ownership/introduction boundaries. Full validation also exposed inconsistent pilot registries and stale recursive alias remapping; those were corrected. |
| 2 | Hidden compound definitions did not refine. Existing receipts now retain introduction/refinement metadata independently of visibility. |
| 3 | Clean on `280b4592`: 137 targeted tests and nine probes. An independent audit then exposed source/query shadowing differences from distinct retained execution keys. Shared introduction and alias transitions now revoke visibility by source label. |
| 4 | Two old adapter fixtures had inconsistent identity tables; they now share the compilation registry. A foreign rule's names hid caller evidence, including ordinary rule binders; rule entry now separates lexical locals from inherited proof definitions. |
| 5 | No product findings on `3b9a0845`: 189 tests and nine probes verify the shared abstraction and judge it minimal. Its sole finding is the first inspector browser failure; the passing rerun was not named in the original review brief. |
| 6 | Clean verification of the test-only navigation predicate and passing isolated browser gate. The user subsequently requests the inspector entry. |
| 7 | Inspector behavior, lifetime and receipt sharing hold up. Register its new diagnostic as E249. Preserve the old aggregate text cap after sharing receipts; add the single missing generated coherence entry at its semantic elaboration boundary. |
| 8 | Clean on `cb1cdc2c`: exact receipt costs verified on 7,108 records; generated and recovery coherence contexts, attempt ownership, catalogue and final gates verified. No outstanding findings. |

Review stops clean at the eight-round limit. The 120-application notation
comparison in round 5 takes about 2.1 seconds at both revisions; five mutually
accepted controls have identical kernel work. The saved-alias fuel difference
matches the behavior before the shadowing regression.

## Measured costs and limits

Pre-review checkpoint `9187cadf`, Node v24.13.0, separate processes per fixture:

| Fixture | Check off/on (ms) | Heap growth off/on (MB) | Available/collected points |
| --- | ---: | ---: | ---: |
| Nested function | 263 / 405 | 9.98 / 63.58 | 1,626 / 1,626 |
| Nested induction | 152 / 356 | 9.99 / 63.50 | 1,624 / 1,624 |
| Nested lazy notation | 16.3 / 7.8 | 1.42 / 1.19 | 13 / 13 |
| Inherited generated helper | 28.0 / 14.8 | 2.72 / 1.15 | 60 / 60 |
| Theory sections | 396 / 1,009 | 24.64 / 206.17 | 5,182 / 5,182 |

| Fixture | Median prefix / validation / history / query (ms) |
| --- | ---: |
| Nested function | 78.16 / 0.145 / 0.300 / 0.292 |
| Nested induction | 95.03 / 0.287 / 0.002 / 0.713 |
| Nested lazy notation | 2.174 / 0.256 / 0.136 / 0.390 |
| Inherited generated helper | 5.531 / 0.123 / 0.106 / 0.260 |
| Theory sections | 250.51 / 0.278 / 0.327 / 0.706 |

Each fixture runs its session three times with a fresh native handle per request.
The WASM instance and process stay warm; there is no explicit JIT warm-up. Memory
samples follow GC, before serialization/queries, and measure process totals,
not marginal collection cost. Collection off/on has identical kernel work.

Separating mutable per-point permissions from shared immutable descriptions
reduced nested-function heap growth from 129.51 to 63.58 MB and sections from
273.88 to 206.17 MB. Collection remains substantially more expensive than normal
checking. Unshared JSON of the sections index is 288 MB; the browser transports
only a lightweight index. Replay input is 99 KB. These are measurements of the
pre-review checkpoint, not guarantees for arbitrary modules. CB7 must complete
collection-mode measurements and justify its release budget from evidence.

The full screenshot example, `library/universe_smallness.cubist`, measured at
`d48fa919` after inspector entry and receipt sharing: check off/on 319 / 692 ms,
GC heap growth 20.31 / 108.88 MB, 5,360 collected points. The inspected `ih` is
available; three sessions check `ih`, `m`, and saved scratch values without
changing the source program's kernel work. Median prefix / validation / history /
query times are 214.17 / 0.320 / 0.0018 / 0.569 ms. Most requests have no accepted
history yet. Cache and GC conditions are as described above; this checkpoint
precedes the final coherence-entry and aggregate-text-cap corrections.

Immutable core binding receipts are shared by term and binding ID. Mutable
compiler values and caller permissions remain point-specific. Cache hits charge
the same visit and text costs as fresh descriptions; the existing 500,000-visit
and 4,000,000-character environment limits are unchanged. The browser continues
to transport a small index, without copying the complete retained graph.
