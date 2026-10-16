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
