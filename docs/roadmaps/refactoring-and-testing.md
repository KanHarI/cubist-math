# Refactoring, code reduction and Cubist tests

Status: proposed on 2026-10-10, as a follow-up to
[PR #211](https://github.com/KanHarI/cubist-math/pull/211)
(`fg6-preservation-gate`). This is a roadmap, not an implementation or a
claim that tests have already been removed.

The audit covers the updated stack at
[`c1780211`](https://github.com/KanHarI/cubist-math/commit/c17802111f9e20cc68c918d8590f8d74743bc375)
and code present before FG at
[`00d4ecce`](https://github.com/KanHarI/cubist-math/commit/00d4ecce016f7e18d13eedeced07dc098a2277cb).
It follows the [frontend generation roadmap](frontend-generation.md),
[syntax hygiene contract](syntax-hygiene.md) and
[FG6 preservation gate](../reports/frontend-generation-fg6.md).

Start with a small cleanup PR deleting obsolete test bookkeeping and
duplicate checks. Then move source-level behavioral tests into Cubist,
adding a small observation layer to the existing runner. Refactor the
generation and publication machinery in separate, behavior-preserving
PRs. None of the proposed testing capabilities needs a new kernel axiom
or inference rule.

## What grew, and what was already large

These are physical lines, including comments and blanks, from tracked
files at the audited revision; generated build products are excluded.
Counts include `.mjs`, `.js`, `.py`, `.c`, `.h` and `.cubist`, not HTML,
CSS, JSON evidence or Markdown. They describe maintenance surface, not
dead code or measured coverage.

| Area | Files | Lines |
| --- | ---: | ---: |
| `web/` implementation | 94 | 22,832 |
| `tools/` and `cli/` | 33 | 3,852 |
| `tests/`, including helpers, fixtures and browser scripts | 154 | 16,939 |
| `kernel/src/`, `kernel/include/`, `wasm/` | 30 | 8,475 |
| `kernel/tests/` | 14 | 3,787 |
| `cubist-tests/` | 207 | 9,772 |

To separate FG work from subsequent conflict-resolution merges, compare
the original stack's documentation base `a969fe38` with FG6 `c1ca3d2c`
using `git diff --numstat a969fe38 c1ca3d2c`. Its implementation changes
under `web/`, `kernel/`, `wasm/` and `cli/` total **+754 / -234 lines
(net +520)** across 22 files. `tests/` adds **net 1,395** lines across 15
files; tools add 191. The remaining net 2,621 lines include documentation,
reports, JSON evidence, Cubist fixtures and configuration. That remainder
is not all executable implementation.

Several substantial modules predate FG:

| File | Before FG | Audited head | Main opportunity |
| --- | ---: | ---: | --- |
| [`web/translator/translate.mjs`](../../web/translator/translate.mjs) | 1,609 | 1,696 | Separate scheduling/publication from term elaboration. |
| [`web/cubical-instruction-driver.mjs`](../../web/cubical-instruction-driver.mjs) | 1,519 | 1,519 | Separate search policy and traces from instruction emission. |
| [`web/cubist/parser.mjs`](../../web/cubist/parser.mjs) | 1,497 | 1,497 | Keep grammar tests in the host; size alone does not justify a parser rewrite. |
| [`web/proof.mjs`](../../web/proof.mjs) | 1,093 | 1,107 | Separate worker/session lifecycle from rendering. |
| [`kernel/src/instructions.c`](../../kernel/src/instructions.c) | 1,010 | 1,010 | Preserve independent admission checks; no blanket shortening. |
| [`web/diagnostics.mjs`](../../web/diagnostics.mjs) | 857 | 858 | Stop inferring diagnostic identity from English messages. |
| [`web/cubist/theories.mjs`](../../web/cubist/theories.mjs) | 720 | 752 | Reduce repeated telescope/record/source conversions. |
| [`tests/initial-models.test.mjs`](../../tests/initial-models.test.mjs) | 687 | 692 | Move ordinary Cubist client programs out of JS wrappers. |

Splitting a large file can improve ownership without reducing code. For
each extraction below, name the duplicated logic or state coupling it
removes; do not count renamed files or shorter formatting as savings.

## First cleanup PR: specific deletions

Suggested title: **Remove obsolete FG test scaffolding and duplicate
fixture checks**. This PR changes test infrastructure and its live
documentation, without changing production semantics.

| Candidate | Action and surviving coverage |
| --- | --- |
| `expectedFailures` in [`tests/fixtures/frontend-generation.mjs`](../../tests/fixtures/frontend-generation.mjs) is empty. `contractTest` in [`frontend-generation.test.mjs`](../../tests/frontend-generation.test.mjs) still implements temporary TODO failures and `CUBIST_GENERATION_STRICT`. | Delete the empty set, environment switch and unreachable expected-failure path. Run the existing contracts directly; preserve G identifiers and capture variants. Update the stale instructions in [`frontend-generation.md`](../../tests/fixtures/frontend-generation.md). |
| “FG0 maps historical fixes and passing controls to existing executable tests” reads other JS files and searches for literal `test("name",` strings. | Delete the source-spelling test and its `historicalCoverage`/`passingCoverage` data. Keep historical mapping in documentation and retain the small contract/fixture key-completeness check. The actual historical regressions still execute. |
| “theory constructors keep header parameters apart from generated field binders” in [`theories.test.mjs`](../../tests/theories.test.mjs) rechecks `theory_headers`. | Remove the redundant wrapper. Preserve `named_nat`, `named_hom`, `named_iso`, `named_by_fields` in [`theory_headers.cubist`](../../cubist-tests/theory_headers.cubist), already checked by the inlined suite. Confirm those declarations and the module remain discovered before deletion. |
| “migrated native proof scopes format without changing their expanded syntax” in [`unfolding-syntax.test.mjs`](../../tests/unfolding-syntax.test.mjs) repeats archive round trips for eight files. | Drop the repeated AST-preservation/idempotence work: [`formatter.test.mjs`](../../tests/formatter.test.mjs) already checks those archive files. Retain the prohibition on the old `with_unfolding(` spelling. Keep the focused scoped-syntax edge cases. |

The formatter's archive round-trip test and
[`formatting.test.mjs`](../../tests/formatting.test.mjs), which enforces
checked-in formatting across source roots, test different contracts.
Keep both. The generated artifact/assumption test immediately after the
`theory_headers` wrapper also adds coverage and must remain.

One further candidate needs a replacement before deletion: “both language
references and keyword styling describe the scoped syntax” checks literal
prose in HTML. Route executable reference examples through existing
reference checks and keep the keyword styling assertion. Removing prose
spelling checks must not remove verification of reference examples or
token styling.

Acceptance: record the named surviving check for each deletion; run
`npm test` and `npm run test:generation:mutations` separately; preserve
all required mutation targets and the selected Cubist declarations. The
PR should have a net reduction in test/helper code. No new generic test
framework is needed for this slice. Historical FG reports remain evidence
about their recorded revisions and should not be rewritten as current
instructions.

## Moving tests into Cubist

### Capabilities that already exist

| Intended assertion | Existing Cubist expression |
| --- | --- |
| An expression checks at a stated type | `def client : T := expression;` |
| A generated operation has the intended equation | An independently written equality type and a proof; use `rfl` when conversion itself is the contract. |
| An authored definition has no transitive assumptions | `computable def`, where its contract is appropriate. |
| A closed computation returns an expected value | `evaluate expression expecting pattern;` |
| Selected presentation remains stable | Existing `print(...)` and `// Output:` expectations. |
| A declaration is refused, with current wording | Existing `// Error:` / `// Warning:` expectations. |

[`evaluation.mjs`](../../web/translator/evaluation.mjs) already supports
expected patterns with holes, pairs, sums, declared constructors and
`typed(T, pattern)`. These are patterns, not new logical terms. Do not add
another equality or evaluation primitive merely to port a JS assertion.

A type annotation at a sufficiently large universe does not establish
the exact inferred universe: cumulativity can hide inflation. Preserve
paired too-low refusals and add an exact inferred-type observation only
where the interface promises one. Likewise, a failed elaboration or
exhausted search is not a proof of logical negation.

### Why recorded messages are insufficient

[`inline-errors.mjs`](../../tools/inline-errors.mjs) compares normalized
messages and prints, attached to a declaration/directive line;
[`stated-comments.mjs`](../../web/cubist/stated-comments.mjs) strips
trailing message positions. This is useful presentation coverage. It
does not assert exact diagnostic ranges, definition links, assumption
sets, absence of partial generated families, or work budgets. Main-source
parse failures also need isolation from the ordinary declaration loop.

The `--write` mode records the implementation's current behavior. It is
not an independent oracle for intended meaning. Keep it for presentation
goldens; never let it rewrite the semantic expectations proposed below.
Retain a small, deliberate set of full-message and CLI/printer snapshots
where wording is itself the contract.

### Add runner primitives, not reflective kernel operations

Put ordinary programs and their expectations together in `.cubist` test
files, using **parsed declaration pragmas** for semantic expectations.
The parser attaches each pragma to its target; unknown names, malformed
arguments and dangling annotations are errors. This makes expectations
discoverable and prevents a misspelled comment from silently doing
nothing. Keep comments for explanations and selected presentation goldens.
A thin JS runner observes compiler results; no runtime exception mechanism,
string evaluation or privileged assertion axiom is needed.

Reuse [`tests/check-program.mjs`](../../tests/check-program.mjs),
[`tools/module-sources.mjs`](../../tools/module-sources.mjs) and the
existing inlined checker. Factor their common execution path instead of
creating another loader or a second way to check declarations. Reuse a
WASM instance where safe, but give each independent case fresh program
and kernel state with deterministic disposal.

| Stage | Primitive and required behavior | First consumers |
| --- | --- | --- |
| T0 | **Named cases and checked declarations.** Stable IDs; enumerate cases once; reject duplicate IDs, missing named declarations, zero discovered cases and an empty explicit selection. `checked name` requires presence and verification. Every unanticipated failure fails the case. | Positive initial/free-model clients; historical coverage mapping. |
| T1 | **Structured diagnostic expectations.** Match code, severity, phase, module/declaration and multiplicity; optionally a range selected by a unique source anchor. Distinguish parse, type mismatch, unsupported generation, blocked dependency and resource exhaustion. Unexpected errors/warnings fail unless an explicit code policy allows them. | G1/G3/G6/G11, negative parser cases, lint-sensitive theory clients. |
| T1 | **Assumption sets and public artifacts.** Assert none, exact set or subset, with an explicit nonempty check when needed. Compare resolved binding identities, including imports and generated declarations. Assert artifact presence/absence and supported family status through publication metadata. | Theory interfaces, hlevel proofs, quotient proofs, universe clients. |
| T2 | **Source observations.** Assert written occurrence range, label, module and definition target; distinguish original and synthetic locations. Anchors must resolve uniquely and fail if missing or ambiguous. | G8–G10 and frontend provenance tests. |
| T2 | **Deterministic resource observations.** Set work limits, assert failure kind and counters, including exact zero searches at a forbidden fallback. Charge speculative work to the same budget. | G8 and bounded elaboration/search regressions. |
| T3 | **Module fixtures and explicit recheck scenarios.** Supply named source modules through the production loader; sequence edits and checks with declared reset/session behavior. | Imported capture, repaired imports and dependency invalidation. |

Implement T0/T1 with real migrations first. T2/T3 are separate extensions,
justified by particular tests, not an invitation to design a general
assertion language. A parse-error case must capture the parse phase in
isolation; an arbitrary throw, failed module load, crash or watchdog
timeout must never satisfy an expected type mismatch. Expected failures
may make the compiler result incomplete while the test passes, but all
remaining declarations and diagnostics must still be accounted for.

### Proposed pragma syntax and semantics

Prefer a small, fixed set of pragmas over user-defined decorators that
transform declarations. Each `# name(arguments)` occupies its own line
and attaches to the next declaration or supported executable directive;
several pragmas may attach to the same item. Argument payloads are
restricted data such as names, codes, integers and lists, not executable
Cubist expressions. Pragma names are contextual after `#`, so `test` or
`expect_axioms` need not become globally reserved identifiers.

Illustrative syntax below is **proposed, not implemented**. With the
pragma lines omitted, the Cubist program was checked at the audited head:
`hom_level` verifies without assumptions and `too_low` reports E606.

```text
import hlevels;
theory T(U < UU0) { M : set U; op(A : U1, x : A) : M; }

# test(generation.hom_universe)
# expect_axioms([])
def hom_level(S : T(U0)) : U2 := T.Hom(S, S);

# test(generation.hom_universe_too_low)
# expect_error(E606)
def too_low(S : T(U0)) : U1 := T.Hom(S, S);
```

This tests acceptance at U2 and refusal at U1, not a general exact-type
query. Expected equations and values must be authored independently of
the generator. Never derive the expected law from another artifact of the
same expansion: both can share the same capture bug.

The initial surface should be `test(id)`, `expect_error(code)`,
`expect_warning(code)` and `expect_axioms([...])`. Successful checking is
the default, so ordinary positive definitions need no extra `succeeds`
annotation. `test(id)` gives a durable selectable case ID and requires
its target to exist. `expect_axioms([...])` specifies the exact resolved
external axiom set; the empty list asserts none. Subset/nonempty options,
artifact queries, source observations and work limits follow when their
migration batch needs them, rather than adding many synonyms up front.

The axiom set includes transitive dependencies through other definitions
and the declaration's type. Ordinary bound parameters and proof hypotheses
do not count as external axioms. This pragma checks the existing reported
dependencies; it neither introduces axioms nor permits an unchecked proof.
Prefer `computable def` for authored definitions whose contract already
requires no assumptions. The test observation also covers generated or
imported declarations and exact nonempty axiom sets; later subset checks
can express, for example, that a quotient proof uses only specified
truncation axioms and does not acquire a dependency on choice.

`# throws(E606)` is a possible spelling, but **`expect_error` is preferred**:
this observes a compiler diagnostic, not a runtime exception. Its short
form expects exactly one error with that code owned by the annotated
item's elaboration/checking attempt. It neither matches an unrelated
declaration's error nor consumes cascading errors in later clients.
`expect_warning` similarly accounts for a warning without implying that
the declaration should fail. Additional phase, count and source selectors
can refine these contracts; all unaccounted diagnostics still fail.

Pragmas are metadata: they do not change the declaration's mathematical
meaning, proof search or publication policy. A failed declaration stays
failed and unpublished; only the test runner may report that the expected
refusal passed its test. Ordinary checking still reports that failure.
Never allow an expectation to swallow a pragma validation error, host
exception, resource exhaustion or missing import. Reject contradictory
expectations and unsupported targets before running the case.

An annotation targets an item in its enclosing source fixture, not a
request to recompile the file separately for every annotated declaration.
Declarations retain their ordinary lexical order and shared module context;
independent fixtures get fresh state. Preserve explicit sequential edit
scenarios separately. Annotating a theory observes its owned expansion;
do not copy the test annotation onto every generated member. Public
artifact assertions can select a particular member explicitly.

Implementation belongs in T0/T1: [`parser.mjs`](../../web/cubist/parser.mjs)
currently rejects `#`, and [`formatter.mjs`](../../web/cubist/formatter.mjs)
uses parsed item boundaries. Add a single shared grammar and AST metadata,
preserve pragma spans separately from declaration spans, and make
formatting/highlighting preserve attachment. Do not strip pragma lines
with a runner-specific regex, which would lose source positions and create
a second grammar. Keep unknown/malformed pragma and round-trip tests in
JS. For malformed Cubist that cannot produce an AST, keep isolated raw
source parser tests in the host initially; `expect_error` is not parser
error recovery.

Existing `// Error:` and `// Output:` goldens can coexist during migration.
Replace a migrated semantic error golden with its pragma in the same
change; avoid asserting the same diagnostic through two independent
mechanisms unless its exact wording is intentionally under test. The
golden-update command must never create or rewrite pragmas automatically.

### Concrete migration batches

| Suite/cases | Move into Cubist | Keep in the host |
| --- | --- | --- |
| First four tests in [`initial-models.test.mjs`](../../tests/initial-models.test.mjs): parameter capture, function/dependent-pair generators, grouped law binders, named/mixed arguments | Their source programs already contain checked client proofs; replace the `verified(...)` wrappers with discovered cases. | Migration-tool behavior, injected failures and native publication inspection. |
| Grouped-domain and repeated-name operation tests in [`theories.test.mjs`](../../tests/theories.test.mjs) | Existing client equations and computations, with explicit warning expectations. The old W706 workaround comment is no longer a reason to keep source in JS after FG5's lint changes. | Parser/formatter structure checks; generated artifact enumeration until T1 covers it. |
| [`frontend-universes.test.mjs`](../../tests/frontend-universes.test.mjs), source cases in [`frontend-evidence.test.mjs`](../../tests/frontend-evidence.test.mjs), G1/G2/G4/G6/G11/G12 | Positive clients, paired negative cases, assumptions and expected refusals. Keep direct, imported, inherited, renamed, fixed-universe and generic cases where they traverse different paths. | Direct construction of scopes/native terms and refinement/dimension restriction probes. |
| [`hlevel.test.mjs`](../../tests/hlevel.test.mjs) and [`quotient-universal.test.mjs`](../../tests/quotient-universal.test.mjs) | Use `computable def` for authored assumption-free proofs where equivalent; T1 handles generated/imported declarations and allowed assumption sets. | Low-level tactic/search instrumentation until its observation exists. |
| [`computability.test.mjs`](../../tests/computability.test.mjs) | Expected values and patterns using existing `evaluate ... expecting ...`. | Assertions about reporter completion after failed evaluation, until the runner exposes them; parser/formatter structure. |
| FG source links and diagnostics | T2 annotations replace hand-calculated JS offsets and repeated link scans. | Browser clicks, selection and navigation still need DOM tests. |

The quotient tests require a nonempty subset of specific truncation
assumptions. Replacing them with `computable` would change the contract
to no assumptions. Similarly, `checked` alone cannot replace the theory
artifact inventory or a test that native state was rolled back.

Keep randomized source generation, shrinking and mutation orchestration
in JS. They can emit readable `.cubist` reproductions and run the same
case runner; rewriting the generator in Cubist is not a prerequisite for
moving its behavioral assertions.

## Implementation refactors

### Publication: one explicit lifecycle owner

Publication is coordinated across `Translator.translate` in
[`translate.mjs`](../../web/translator/translate.mjs),
[`cubical-program.mjs`](../../web/cubical-program.mjs),
[`cubical-transaction.mjs`](../../web/cubical-transaction.mjs) and
[`declarations.mjs`](../../web/translator/declarations.mjs). The translator
owns queue/group and environment restoration; the program separately
snapshots views, binding/reference maps, local symbols, links and
statements; the transaction owns native checkpoints and checker metadata.

Introduce one explicit publication lifecycle that coordinates those
existing owners. Declare the participating stores once and pair begin,
commit and rollback on every exit, including observer exceptions. Remove
duplicated lifecycle branches and hand-maintained parallel rollback lists.
Keep the native checkpoint implementation distinct from frontend state.

Preserve the actual group boundaries: a failed Hom leaves the base theory
usable, blocks dependent Iso publication, and removes all admitted members
of its own group. Keep ownership identity and explicit family roles;
do not reconstruct them from dotted names or make an entire theory one
all-or-nothing transaction. A shared lifecycle must also preserve progress,
rechecking, REPL snapshots, export replay and benchmark behavior.

[`frontend-publication.test.mjs`](../../tests/frontend-publication.test.mjs)
is high-signal coverage: failed parent projection, late Hom/fold failure,
native signature removal, observer exceptions and repaired imports must
remain. The [FG1 report](../reports/frontend-generation-fg1.md) records
arena-cost increases. Profile before replacing snapshots with journals;
that is a separate optimization requiring alias/mutation and rollback
evidence, not an automatic part of extraction.

### Generation: fewer representations of the same telescope

[`theories.mjs`](../../web/cubist/theories.mjs) moves between field records,
`derivedSyntax` and `derivedRecord`; `parameterGroups` reconstructs shared
domains. [`morphisms.mjs`](../../web/cubist/morphisms.mjs) independently
groups/renames binders and builds source templates; theories then reparses
the generated source and inserts resolved references and type fragments.
[`initial-models.mjs`](../../web/translator/initial-models.mjs) consumes
the related theory representation through another generation path.

Consolidate the complete retained telescope and a narrow generated
declaration builder. Pilot Hom identity/composition and remove the old
path for that slice in the same PR. Compare the resulting code: a verbose
AST constructor for every template can increase maintenance cost. Expand
the builder only if it removes conversions and duplicated scope handling.

Reuse `SCOPES`, `rewritten`, `substituted` and `renamedApart` in
[`scopes.mjs`](../../web/cubist/scopes.mjs), and the identity graph in
[`dependencies.mjs`](../../web/cubist/dependencies.mjs). Do not introduce
another general visitor or merge morphism transport support with
equational support: they intentionally allow different constructions.

Preserve grouped-domain scoping, complete law binders, captured notation,
model/caller separation, binding identities, public labels, source origins
and publication roles. Infer universes from checked generated types;
do not replace that with a guessed formula. A small shared evidence mapper
may also simplify refinement/face/generalization transformations, but
must carry term, type, model and dimension information together.

### Diagnostics: identity before rendering

Most of the diagnostic catalogue predates FG.
[`diagnostics.mjs`](../../web/diagnostics.mjs) currently classifies English
messages using patterns. Introduce structured errors at producers,
carrying code, parameters, phase, primary/related spans and failure kind;
render their English at the presentation boundary. Migrate one diagnostic
family at a time and delete its fallback message-classification path.

Reuse the existing registry and
[`diagnostic-codes.mjs`](../../tools/diagnostic-codes.mjs) reference tooling.
Preserve code history and selected presentation snapshots. The T1 runner
can consume today's reported codes first; it need not wait for a catalogue
rewrite. Avoid adding a second catalogue or maintaining two permanent
definitions of every message.

### Older orchestration and tooling

| Area | Bounded change | Constraint |
| --- | --- | --- |
| Translator | Move module/declaration scheduling behind the publication lifecycle, leaving term elaboration/tactic dispatch with their existing scope and source-unit interfaces. | No mixin framework or duplicate query/fuel state. |
| Instruction driver | Extract a coherent search-policy/trace or signature-handling component behind existing `InstructionGraph` calls, if it reduces shared mutable state. | The JS driver is untrusted; keep C admission checks independent. Similar-looking rules across that boundary are deliberate validation. |
| Workbench | Extract worker/request lifecycle from `proof.mjs`, then renderer functions with explicit inputs; reuse existing navigation modules. | Preserve cancellation, stale-response rejection, source navigation and inspection. Separate from compiler refactors. |
| Browser scripts | Share the repeated server startup, readiness, Chromium lifetime and teardown used by landing, navigation, cubical and inspector scripts. | Keep scenario assertions. Older scripts are still invoked by [`release-evidence.mjs`](../../tools/release-evidence.mjs), even when absent from the default browser command. |
| Module inventories | Consolidate repeated discovery lists around [`modules.mjs`](../../web/cubist/modules.mjs) with deterministic validation/generation. | Preserve curated archive order, benchmark membership, titles and browser bundle inputs; automatic alphabetical discovery is not an equivalent replacement. |

Defer wholesale parser/kernel rewrites. In particular, the large native
signature tests exercise admission conditions and malformed inputs that
well-typed Cubist cannot express. Keep invalid-handle, ABI, isolation and
allocation-failure tests in C/JS. Do not delete an independent validator
to reduce line count.

## Ordered PR roadmap

Each row is a reviewable slice; stop or subdivide if it grows beyond the
stated boundary. RC0 is the recommended next PR after this document.

| ID | Deliverable | Depends on | Risk and exit evidence |
| --- | --- | --- | --- |
| RC0 | Delete obsolete FG scaffolding and redundant checks listed above. | This roadmap | Low. Net test/helper deletion; surviving cases named; full suite and 13 required mutation kills unchanged. |
| RC1 | Parse/format the initial pragmas, implement T0/T1 in the existing runner, and migrate the first initial-model/theory cases. | RC0 | Medium. Unknown/dangling pragmas, missing/duplicate cases, unexpected failures and assumption mismatches demonstrably fail; formatting preserves attachment and spans. Old wrappers removed in the same PR; no second module loader. |
| RC2 | T2 source/work observations, then migrate FG source assertions. Add T3 module scenarios as a separate sub-PR when needed. | RC1 | Medium. Every migrated contract detects the same deliberate defect; retain browser and native fault injection. |
| RC3 | Consolidate publication lifecycle and declaration scheduling. | RC0; RC1 useful, not required | High. Rollback, observer failure, import repair and partial-family controls pass; native handles and frontend metadata agree. Compare allocation/work counters. |
| RC4 | Pilot telescope/builder consolidation for Hom, then widen by family. | RC1; coordinate with RC3 | High. Intended/captured law pairs, universe matrix, assumptions and source origins preserved; old conversion path deleted for each migrated slice. |
| RC5 | Structured diagnostic producer migration, one family at a time. | RC1 | Medium. Codes/spans stable; presentation snapshots reviewed; corresponding English classifier branches removed. |
| RC6 | Share browser fixtures and reconcile module inventories in separate PRs. | Independent | Low/medium. Existing release/browser scenarios and discovery membership preserved; setup/list duplication removed. |
| RC7 | Extract workbench lifecycle; separately consider driver policy/trace extraction after profiling. | Independent of test migration; keep clear of RC3/RC4 | Medium/high. Stale-worker and UI controls pass; driver changes preserve instruction validity and work budgets. No trusted-kernel rewrite. |

Do not implement these as one cleanup mega-PR. RC1 should deliver actual
source migrations, not only add infrastructure; RC3/RC4 should remove
their previous paths rather than retain permanent compatibility layers.

## Preservation and completion criteria

- For each removed assertion, identify the surviving case and the behavior
  it distinguishes. For a mutation-targeted migration, run the same bad
  implementation against the new case before deleting the JS assertion.
  Update mutation selectors to stable case IDs as the runner gains them.
- Keep all **13 required FG mutation kills**, with passing unmodified
  baselines. A crash, infrastructure error or timeout is not a semantic
  kill. Preserve the eight deterministic CI source configurations and the
  wider 32-case audit unless an equivalence argument supports a change.
- Keep independent intended-law and captured-law controls, generated
  public interfaces, assumptions, source origins and deterministic work
  limits. Passing elaboration alone does not establish source meaning.
- The four documented surviving probes do not prove their guards dead.
  The historical unidentified skipped mutation remains unresolved in the
  [FG6 report](../reports/frontend-generation-fg6.md). Do not delete guards
  or claim that missing evidence was recovered as part of cleanup.
- Run the relevant suite once per implementation slice, then the full
  suite before publication. Run expensive mutation audits separately from
  timing checks. Preserve existing resource limits; raising a timeout or
  fuel budget is not a refactoring success.
- Report net executable/test/helper line changes, duplicated paths removed,
  case discovery and actual checks performed. For performance claims,
  compare the same revision-pinned workloads on the same machine, recording
  WASM/program initialization counts, imports, allocations, work counters
  and wall time. Do not substitute fewer JS `test(...)` calls for less work.

This scan establishes concrete cleanup candidates and migration boundaries;
it does not establish a coverage percentage or a runtime saving. Prefer
small measured reductions with preserved contracts over a target number
of deleted tests or a repository-wide line-count quota.
