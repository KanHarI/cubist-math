# Refactoring and source-level tests

Status: agreed implementation is present in the PR stack, after CB0–CB7 and their cleanup.
Final review and validation are in progress; the stack remains unmerged.
This is the current implementation plan for the remaining ideas from
[#224](https://github.com/KanHarI/cubist-math/pull/224), whose pinned
`1fdc68a5` roadmap describes the earlier compiler. The
[binding roadmap](capture-bindings.md) and its completion records own the
implemented binding, generation, inspection and contextual REPL contracts.

The stack follows [#242](https://github.com/KanHarI/cubist-math/pull/242),
merged as `165ac956`, which adds the existing frontend mutation runner to CI
and preserves its evidence. It is separate from this cleanup. No PR in this plan is merged by
recording its completion here.

## Scope and order

Each row is a review boundary, not a requirement to create exactly one PR.
Split a row when its changes have independent validation. Delete each replaced
path in the same PR as its replacement; do not retain parallel frameworks.

| Slice | Work | Dependencies and evidence | Status |
| --- | --- | --- | --- |
| RC0 | Nontrivial archive formatter round trips; redundant test and dead-code removal; documentation reconciliation | Preserve tokens, comments and syntax after actual reformatting; kill a meaning-changing formatter mutation; existing suite | Implemented; Opus 5.5 round 2 clean |
| RC8 | Complete development-version inputs and compilation-local inference placeholders | Editing worker dependencies changes the version; repeated compilation is deterministic | Names and development version implemented; Opus 5.5 reviews clean |
| RC7 | One worker request transport for proof, standalone REPL and reference examples | Preserve independent program/session ownership, cancellation and stale-response rejection; worker startup errors settle pending requests | Implemented; Opus 5.5 round 6 clean |
| RC9 | Shared diagnostic-comment reader and test-host helpers | Preserve own-line/end-of-line comments and continuation rules; remove migrated copies before adding pragma readers | Reader and shared Node/browser hosts implemented; Opus 5.5 reviews recorded in their PRs |
| RC5 | Producer-assigned lint codes and structured source positions | Preserve diagnostic codes, spans and selected message snapshots; remove corresponding English classifiers and position reparsing | Lint codes and source-qualified parse/duplicate/worker diagnostics implemented; Opus 5.5 reviews clean |
| RC10 | Verification commands shared by CI and release evidence; additional partial-failure mutation probes | Record deliberate command differences; baseline passes and assertion failures distinguish semantic kills from infrastructure failures | Shared verification commands and 16 mutation probes implemented; Opus 5.5 reviews clean |
| RC1 | Parsed test pragmas, one case observer and first actual Cubist test migrations | After RC9; reject malformed, ignored, missing and duplicate contracts; preserve mutation selectors and benchmark refusal accounting | Implemented; final review in progress |
| RC2 | Source/work observations and module scenarios needed by further test migrations | Extend RC1 only for concrete migrations; retain host fault injection, DOM and malformed-kernel tests | Implemented; module migrations reviewed clean, source/work review in progress |
| RC3 | One publication lifecycle owner and explicit module context | Preserve partial-family publication, rollback, import repair, observer failures, rechecks and accounting on every exit | Explicit definition context and publication owner implemented; Opus 5.5 context round 2 found no behavioral issue, publication round 3 clean |
| RC6 | Shared browser setup, module inventories and corpus tools | Preserve curated order, membership, titles, scenarios and report contents; validate both file-to-list and list-to-file membership | Inventories, browser fixtures and corpus execution implemented; Opus 5.5 reviews clean |
| RC11a | Shared source scanner and lexical rules | Parser/highlighter token boundaries agree, including comments, incomplete input, numerals and operators | Implemented; Opus 5.5 round 3 clean |
| RC11b | Shared term child/binder metadata and free-name traversal where semantics agree | Preserve binder scope, substitution and display-only terms; keep native codec independent unless parity is verified | Implemented; Opus 5.5 round 2 clean |
| RC11c | Builtin dispatch and reserved-name correspondence | Every reserved builtin has an intentional handler; existing argument errors and elaboration results survive | Implemented; Opus 5.5 round 2 clean |
| RC11d | WASM enum parity and step-budget wrapper | Compare C/JS encodings; preserve exact 64-bit budgets and independent native admission checks | Implemented; Opus 5.5 round 1 clean |
| RC11e | Development/published-site layout agreement | Published roots and versioned imports agree under both servers; existing browser/site scenarios | Implemented; Opus 5.5 round 3 clean |
| Final cleanup | Review the completed stack for redundant state, wrappers and superseded documentation | All agreed slices accounted for; independent semantic controls retained | Audit complete; final validation in progress |

RC4's complete telescopes and artifact builder are already implemented by
CB2/CB4. Binding-related RC5 work and #224's fixture/observer improvements
were adopted by CB0–CB5. Do not build another binding representation or
reintroduce the old nominal repair path. The old recursive-only fallback
expectation was superseded by CB3's checked eligible fallback contract.

The instruction driver's organization is **deferred**. It already exposes a
replaceable policy, separate telemetry and pinned trace tests. File size alone
does not justify a new component; reopen only for demonstrated duplicated logic
or state coupling. Search budgets and independent C checks remain intact.

Build prerequisites and native test discovery are **out of scope** by the
2026-10-17 scope decision. The build stamp already hashes every kernel header,
protecting `make wasm`. Argument inference now owns placeholder
names per compilation, preserving the separate placeholder namespace and ordinary
generated-name sequence. The retired lexical
serial needs no replacement.

## Test pragmas

Pragmas are parsed source metadata, not textual preprocessing or trusted
assertions. Start with annotations attached to the next declaration or supported
executable directive:

```cubist
# test(generation.hom_universe)
# expect_error(E606)
# expect_warning(W705)
# expect_axioms([])
```

These lines illustrate the annotation forms; combinations must be meaningful
for their target. Keep pragma spans separate from declaration spans. Names after
`#` are contextual, not globally reserved words. Whitespace is insignificant;
formatting preserves attachment. Unknown, malformed, contradictory, dangling
and unsupported-target annotations fail explicitly. Enable them only in test
sources initially; ordinary loaders must reject, rather than ignore, contracts.

Compile each fixture once in its ordered module context, with an independent
program/kernel disposed afterwards. A shared observer serves Node case tests,
inline diagnostic checking and benchmark expected-refusal accounting. Annotation
metadata never changes checking, search or publication; refused declarations
remain unpublished. `inline-errors --write` never creates semantic expectations.

Each named case must exist and have an observed target. Duplicate IDs, missing
selected IDs and an empty explicit selection fail. Annotated cases succeed by
default; unannotated declarations in migrated modules must also succeed. Account
for all unexpected diagnostics, including imported failures. A short expected
error matches exactly one code owned by its target, not an unrelated failure or
cascade. Parser/pragma failures, missing imports, crashes and resource exhaustion
cannot satisfy an expected mathematical refusal.

Assumption expectations compare exact resolved external transitive dependencies,
including the type, excluding bound hypotheses. A generated-family expectation
applies to each owned member, not their union. Use existing `computable def` and
`evaluate ... expecting ...` contracts where appropriate. Keep selected message
goldens for presentation and native tests for malformed inputs Cubist cannot
express.

The source fixtures now own theory/initial-model, imported-evidence, refusal-range
and charged-search contracts; their replaced JavaScript wrappers are removed.
Stable IDs retain mutation selection and assertion-failure classification.
`# expect_error_at(...)` names a unique balanced token sequence in its target;
`# expect_searches(...)` counts charged coherence searches on an ordinary
function. The [regression guide](../guides/regression-contracts.md) defines both.
Module scenarios use sibling imports through the ordinary source loader, with
an independent program/kernel per fixture. Host reset/failure injection, source
links, exact diagnostic message goldens and DOM behavior keep their existing
JavaScript tests. There is no parallel module loader or general assertion language.

## Publication ownership

Use one lifecycle coordinator for begin/commit/rollback on every exit, with
frontend stores' ownership declared once. Replace the per-module prototype
checker and manually copied counters with an explicit module context. Keep the
native checkpoint transaction and speculative `ObservationFrame` responsibilities
distinct: selecting an elaboration attempt is not publishing a declaration.

Preserve current family boundaries. A refused Hom may leave its checked base
available while publishing no partial Hom and blocking dependent Iso artifacts.
Initial/fold groups keep their existing boundaries. Native handles, environment,
references, generated views and observers must agree after failure, including
observer exceptions. Import repair, repeated checks, failed-syntax inspection,
contextual replay and work accounting must work on error paths too.

Do not replace snapshots with a journal without measurements establishing a
need. Do not add a second rollback system or merge all generated families into
one transaction. Independent C instruction admission remains the trust boundary.

## Validation and review

Before fixing a review finding, compare it with prior rounds and the
[CB review roots](../reports/capture-bindings-review-roots.md). Repair the
responsible contract and all its consumers when the cause is architectural.
Avoid adding state or wrapper layers merely to satisfy one reproducer.

Run focused checks per slice, and the appropriate full gate before publication.
Run semantic mutation controls separately from timing measurements, with passing
unmodified baselines. Crashes and timeouts do not count as kills. Keep independent
intended/captured clients, public interfaces, assumptions, source ownership and
deterministic fuel limits. Do not raise resource limits to make a refactor pass.

Each PR records paths removed, surviving coverage, executable/test line changes
and the checks actually run. Performance claims require equivalent revision-pinned
workloads; fewer JS test wrappers alone do not imply less work. Every PR receives
Claude Code Opus 5.5 review, stopping when clean with at most eight rounds when
there are real findings. Findings must be verified rather than accepted blindly.


## Final cleanup audit

The cleanup is distributed through the implementation boundaries: old paths
are removed with their replacements. The closing pass checks those removals
and reconciles the completion records rather than introducing more wrappers.

- `CubicalPublication` stages inspection records and owns commit/rollback;
  the old full inspection-map snapshots and repeated transaction exits are gone.
  Native checkpoints and speculative observation frames retain their separate jobs.
- `Translator.definitionModule` supplies explicit names over one shared checker;
  the prototype checker and copied mutable counters are gone.
- One worker transport serves the workbench, standalone REPL and reference
  examples. Program/session ownership remains with each caller.
- The scanner, diagnostic-comment reader, term shape, display-name analysis,
  module inventories and corpus check entry point each replace their old copies.
  Ordered corpus inputs and the independent native codec remain explicit.
- Source-contract hosts share one observer. Declaration ownership comes from
  publications and declaring syntax, not an error's blame span. Resource failures
  follow the existing dependency chain; they cannot satisfy semantic contracts.
- Actual source migrations remove their old wrappers and unused fixture-map
  option. Range/search assertions move into Cubist; message presentation goldens
  remain independent. Two added mutations exercise the new assertion boundaries.

Build prerequisites/native test discovery and instruction-driver reorganization
remain outside the agreed scope. No resource limits were raised for these changes.
