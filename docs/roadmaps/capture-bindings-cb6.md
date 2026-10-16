# CB6: contextual REPL

Status: implementation in `cb6-contextual-repl`, stacked on ready CB5 #238
(`4c2b4f3a`, clean fourth Claude review). CB6 and CB7 are not complete.

## Required result

- Source and generated-view entry points select exact, retained scope instances,
  with source-qualified ranges, parent paths and explicit selection when one
  occurrence has several elaborated instances. Discarded attempts stay absent.
- Queries preserve visible and shadowed bindings, checked local types, branch
  refinements, dimensions, evidence, notation and structural recursion. They
  use the existing full-prefix replay callback and independent kernel session.
- Reuse the existing console for expressions, `typeof`, `evaluate`, inspection,
  scratch lets, `/locals`, `/goal` and proof experiments. Results are conditional
  on the selected context; experiments never edit or publish into the source.
- Rechecks, source/import changes and disposal invalidate contextual sessions.
  Worker requests have a defined order. Failed entries preserve accepted
  history, and replay reports the actual fuel/budget/deadline stopping reason.
- Scope collection stays optional. Measure retained descriptions and the
  existing prefix/history/query costs separately. Preserve module REPL behavior.
- Exercise all ten remaining contextual contracts, source distinguishing
  controls, browser entry points, the full suite, corpus and mutation gates.
  Use the same Claude review strategy, up to eight rounds with real findings,
  comparing roots before fixes and stopping clean.

## Diagnosis before implementation

The CB1 pilot is reusable, but broadening its guard alone is insufficient.
Independent probes found three boundaries requiring work:

1. Query copying includes the recursive match's compiler continuation syntax,
   which may contain callbacks after multi-match compilation. Copy only query
   values and private permissions, and omit `Recursive.site`. Keep parameter
   tokens and internal sharing: new query tokens must not acquire ownership of
   the original declaration's parameters. Positive and negative recursive calls,
   query lambdas, wildcard refinements and scratch-history rollback distinguish
   this boundary from simply discarding recursion state.
2. Runtime values do not describe lexical visibility. Opened fields are checked
   projections, not declarations discoverable through `ofValue`; notation also
   needs its exact checked activation. Preserve an optional lexical description
   at actual binding/effect transitions, alongside the live ID-to-value mapping.
   Reuse `LexicalContext`, slot outcomes and notation-context receipts. Do not
   restore full source environments on retained members or infer visibility from
   destination spellings, source offsets or equality of core values.
3. The worker's two mutable promise chains can form a cycle: a queued REPL reads
   a newer `checking` promise which itself waits for that REPL. Two concurrent
   checks can also publish in reverse order. Both defects violate submission
   order. One FIFO around the existing handler resolves both in isolated probes;
   a separate contextual scheduler would preserve the underlying problem.

These are the earlier identity/visibility and live-state ownership roots at new
consumers. The implementation must preserve existing checking when collection is
on or off, rather than hide unsupported state behind a nominal fallback.

## Backend checkpoint

Query copying now preserves recursive permission sharing without retaining the
compiler's match continuation. Nested induction, overlapping wildcard instances,
new query lambdas, scratch-history rollback and recursion refusals are exercised.
The worker uses one submission queue; two actual-worker regressions reproduce the
previous deadlock and reverse publication, and pass after the change.

Optional scope tracking records actual local introductions and selection effects
using the existing lexical context and binding adapter. Private aliases retain
shadowed values without making them visible. Queries cover expression, statement
and file openings, later shadowing, standalone and attached notation, and exact
generated/inherited helper instances with foreign source origins.

Section application introduces a local identity for each earlier definition
applied to the current parameters. The section cache retains checked opening
effects; their application assigns fresh activation identities. It does not cache
a previous declaration's observation metadata or repeat projection checking.
The canonical `theory_sections` fixture has identical outputs, reference links
and kernel work to CB5, with collection off and with 5,182 scopes collected.

This checkpoint does not complete CB6. Notation-expansion and model-numeral
observation guards still need migration; lazy source operands must preserve their
caller context without retaining live scopes. Browser selection/lifetime wiring,
cost measurements and retirement of all ten contextual contracts remain, followed
by final validation and Claude review. No CB6 Claude review has run yet.

Historical name-based sections deliberately have incomplete notation selections.
They continue to check identically with observation enabled, but contextual
queries currently report unavailable; they must not inherit current-language
selection semantics silently. This compatibility limitation is still open.

Checkpoint validation: 74 focused scope, replay, worker, build-harness and theory
tests pass, with zero failures. This is not the final full-suite, corpus, mutation
or browser gate for CB6.

## Commands and worker lifetime

The backend implements `/locals`, `/goal`, `/prove { ... }`, inspection and witness
readout through the existing resolver, proof-block elaborator and checker.
Local listings distinguish visible and shadowed identities with checked types and
source-qualified origins. Expected expression types remain distinct from active
proof goals. Successful or failed proof experiments do not extend scratch history
or change the source program. Witness readout still requires a closed term.

A query through archived declarations exposed another identity-consumer gap:
published references with explicit logical assumptions are applications, not bare
definition references. The existing publication writer now records the exact
declaration receipt in the compilation registry. Structurally equal copies gain
no identity, and the registry still grants no availability. This follows the
earlier publication/identity design rather than inspecting application heads or
adding a spelling fallback to contextual queries.

The worker supports optional scope collection, lightweight context descriptions,
exact-ID session opening, queries, closure and invalidation. Edits and submitted
rechecks revoke contextual capabilities immediately without disposing a live
query's kernel. A check that finishes after an edit cannot publish selectable old
contexts. The module REPL retains its existing behavior. Generated-view links and
scope descriptions carry the same declaration identity for later UI selection.

Validation: 57 command, replay, scope, module-REPL and identity tests pass; all six
actual-worker tests pass. A full Node run executed 1,292 tests: 1,281 passed, ten
CB6 contracts remain TODO, and one catalogue check found three new messages
without codes. All 3,857 canonical checks passed. After adding E245–E247 and their
reference entries, all 25 focused command/worker/identity/catalogue tests pass.
The full run has not been repeated after that catalogue-only correction.

## Browser checkpoint

The optional local-context checkbox rechecks the source with scope collection.
Read and Generated Cubist views expose REPL entry buttons. Opening an entry
starts with an empty picker; every query requires an explicit scope instance.
Generated declarations select by their retained declaration ID, while copied
source ranges preserve their authored module and offset. The picker shows source
locations, phases and parent paths. Equal displayed labels get distinct instance
numbers even when their hidden expansion provenance differs. `/locals` now shows
checked values as well as types, exposing different branch refinements.

The contextual console reuses the existing console component, with a separate
scratch history from the module console. Editing, failed rechecks, closure and
compiler replacement revoke its selected capability. Epoch/selection checks
discard late opening, query and index responses. Restart participates in the
console's existing busy state and reports failures instead of leaving an
unhandled rejection.

The lifecycle audit found the same ownership boundary at two UI consumers:
queued control acknowledgements could expire behind a long check, and closing
a context after worker termination could leave a dead request in the replacement
worker's pending map. Revocation now acknowledges on receipt without touching
native handles. The request boundary rejects calls while its worker is unavailable.
Compiler refresh precedes context closure so a close acknowledgement cannot
suppress the version check. Contextual queries use the same finite watchdog as
module queries; compiler fuel and kernel budgets are unchanged.

Validation: all 60 focused command/replay/worker/generated-view/watchdog tests
pass, as does the diagnostic catalogue check (new worker message E248). The
contextual browser suite exercises selection, proof experiments, scratch
isolation, edits and failed rechecks, wildcard refinements, generated/copy ranges,
compiler replacement and deliberately delayed replies. The existing inspector
browser suite also passes. These are checkpoint gates, not final CB6 validation.

Remaining: notation-expansion and model-numeral observation migration, lazy
operand caller contexts, the historical notation limitation, cost measurements,
retirement of the remaining contextual TODO contracts, and final suite/corpus/
mutation/browser validation. Claude review has not started; CB6 stays draft.

## Notation contexts and contract coverage

Source entry now supplies a complete lexical context. Retained named rules use
their source context; runtime values supply exact receipts without granting
visibility. In particular, a caller's public notation can shadow a label without
removing the source notation's private receipt. This removes a redundant lookup
through the caller's notation namespace, following the earlier identity versus
visibility diagnosis.

Lazy operands retain inert descriptions of their caller contexts. During the
isolated callback, the query copies the caller scope graph and its mutable
permissions using the query's fuel and fresh-name supply. Native handles and
compiler continuations never become retained descriptions. Listing operands does
not force them: `/locals` marks them deferred, and a constructor expression still
needs an expected type when used. Model numerals and literal readers receive
source origins at syntax production, without an observer-only expansion helper.

All nine notation tests pass: source/caller shadowing, unused invalid operands,
nested rules, operand recipes, interval and universe arguments, structural
recursion, query resource ownership, model numerals and literal-reader instances.
Collection preserves their source results, reference links and kernel work.

The ten original TODO placeholders now have executable coverage. Keep the
independent source controls; remove only the placeholders and their unused list.

| Original contract | Executable coverage |
| --- | --- |
| Nested induction | `contextual-replay`: distinct inner/outer hypotheses and scratch history |
| Branch instance set | `contextual-replay`: different wildcard refinements/verdicts; contextual browser picker |
| Discarded path body | `scope-points`: discarded body has no selectable instance |
| Proof goal | `contextual-commands`: `/goal`, proof success/refusal, unchanged source/history |
| Two-session isolation | `contextual-replay` and `cubical-worker`: concurrent sessions and separate scratch bindings |
| Source/import revisions | `contextual-replay`, `scope-points`, worker and browser: pinned imports, new IDs, immediate revocation |
| Ordered prefix/accounting | `contextual-replay`: full imported prefix, failed directives and original resource policy; observation tests retain attempt accounting |
| Fuel/budget/deadline exhaustion | `contextual-replay`: each stopping reason, no nearby fallback or query execution |
| Failed scratch-history replay | `contextual-replay`: failed entry reported, history preserved and later replay succeeds |
| Cancellation/disposal | Worker and browser tests: revocation during import loading, closure, replacement and discarded late replies |

Historical name-based sections remain explicitly unavailable for contextual
queries. Their incomplete selections predate current-language resolution;
observation cannot silently change their semantics. The compatibility boundary
is covered by on/off source parity and unavailable-query tests, and remains part
of CB7's historical-adapter audit.

The measurement tool now accepts `nested-function`, `nested-induction`,
`lazy-notation`, `generated-helper` and `theory-sections`. Initial measurements
expose substantial retained-description cost; investigation and final gates are
still pending. One inductive-self context remains unavailable in the measured
corpus. CB6 is still draft and has not had its first Claude review.

The notation checkpoint passes the full Node suite: 1,292 tests, zero failures,
zero TODOs, including all 3,857 canonical checks. All five cost-tool fixtures
complete their three session repetitions. The source/tests were frozen through
the full run; the subsequent changes correct the benchmark's scope-phase field
and a trailing blank line. The earlier browser gate remains at `66153e54`;
browser and mutation gates still need to run on the completed implementation.

## Complete context coverage and measured costs

Lazy caller permissions now join the immediate scope's per-point recursion
description. Immutable operand/environment descriptions are shared again.
The traversal follows nested operands and explicit scoped syntax, with the
existing syntax budget; its temporary scope references never enter retained
data. Controls change permissions through all three paths and verify that the
new point differs while the old description is unchanged. No cache of live
scopes or additional serialization framework was introduced.

Inductive declarations now describe their provisional self type and earlier
constructors, introducing their reserved identities at the actual signature
telescope transition. A query checks under those local variables, before native
admission. It cannot use a later constructor or change uniform parameters.
Constructor scopes also carry their declaration ID, including initial/free
generated declarations. A later rejected signature does not erase its usable
prefix. Source on/off parity, exact generated-instance queries and positive/
negative uniform-parameter controls pass.

Final cost probe before review, Node v24.13.0, separate processes per fixture:

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

Each fixture runs its session three times. Imports and every earlier declaration
replay for each request in a new native handle. The WASM instance and process
remain warm; there is no explicit JIT warm-up. Memory samples follow GC, before
serialization or queries, and are process observations rather than estimates of
marginal collection cost. Collection off/on has identical kernel work. Budget
and deadline policies are unchanged.

Separating permissions reduced nested-function heap growth from 129.51 MB to
63.58 MB, and sections from 273.88 MB to 206.17 MB. Collection remains optional
and substantially more expensive than normal checking. Naive JSON of the entire
sections index repeats shared data (288 MB); the browser transports only its
lightweight index. The source/replay input snapshot is 99 KB. A request retains
no execution session after its callback. These measurements are not latency or
memory guarantees for arbitrary modules.

Focused gates pass 67 scope/replay/notation tests and 25 scope/worker/generated
retention tests. Final full-suite, browser and mutation gates, followed by the
first Claude review, are pending. The historical compatibility restriction above
remains explicit; current-language contexts have no migration guard.
