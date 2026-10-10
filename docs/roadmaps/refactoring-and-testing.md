# Refactoring, code reduction and Cubist tests

Status: proposed on 2026-10-10, as a follow-up to
[PR #211](https://github.com/KanHarI/cubist-math/pull/211)
(`fg6-preservation-gate`), and revised after its first review the same
day. This is a roadmap, not an implementation or a claim that tests have
already been removed.

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

## Revision after review

The first review, on 2026-10-10, found these issues in the first draft:

1. **RC0 deleted an independent positive check.** The `theory_headers`
   wrapper is the only check, out of `--write`'s reach, that its four
   declarations verify. Its deletion moves to RC1, replaced by pragmas.
2. **The cited formatter coverage was vacuous.** Every tracked source is
   already formatted, so the archive round trip formats fixed points. RC0
   now makes that round trip meaningful instead of relying on it.
3. **Pragmas missed the other readers of checked comments.** The
   benchmark classifies stated refusals as intended, and reference examples
   parse the same comments with their own reader. Both now migrate with the
   pragmas, after the two readers merge (RC9).
4. **The mutation gate selects JavaScript test names.** Migrated cases
   must remain selectable by `--test-name-pattern` and fail through
   `assert`, or a required kill becomes unclassified.
5. **The pragma design was under-specified.** This revision states where
   pragmas are accepted, that newlines stay insignificant, that pragma
   names stay out of the reserved-word list, when success is the default,
   and what `expect_axioms` means on a theory. The example now uses
   `computable def` where it applies, as the text recommends. A leftover
   `checked` primitive from an earlier draft is gone.
6. **The publication section omitted the checker's own state.** Twelve of
   the fourteen collections rolled back per declaration belong to
   `cubical-elaborator.mjs`, and each module's checker is a prototype copy.
7. **Further consolidation and dead code** found by a survey of the whole
   code base are now listed under [single sources of truth](#single-sources-of-truth)
   and [small independent fixes](#small-independent-fixes), as RC8–RC11.

## Coordination with the FG0 review refactor

[PR #205](https://github.com/KanHarI/cubist-math/pull/205)'s reviewed contracts
are now integrated and active on this branch. The
[recorded design decision](https://github.com/KanHarI/cubist-math/pull/205#issuecomment-6096591882)
separated fixture failures from known compiler debt; integration retires the
temporary debt records, TODO/strict-mode classification and lifecycle-only tests.
Desired assertions, case IDs, the independent requirement map and acceptance
controls remain. This completes the FG0 integration part of RC0, not its other
cleanup work.

The contracts now cover distinct G4 branch computations, G12 base/recursive
steps in all three contexts, lexical shadowing, refused-member publication,
and validated source anchors. Downstream additions remain: G8's exact token
range and zero coherence-search count, G5's named generated-constructor client,
explicit-path negatives, both bare/partial helper contexts, and the recursive
predecessor regression. The original required compiler mutations remain and
a recursive-shadowing mutation has been added. Source semantic mutants and
injected observer controls provide separately identified acceptance evidence.
Commit-specific validation belongs in the PR discussion.

The observation helpers remain eligible for RC1/RC2 migration through the
existing runner; they add no test language or module loader.

The FG6 gate selects group prefixes (`G2:`, `G5:`, `G8:`, `G11:`), while an
individual case is selectable by its bracketed ID. Preserve those prefixes and
assertion failures until the selectors migrate together with the tests. The
existing FG5 provenance and browser tests also read fixture sources through
`gaps`; the refactor provides that ID lookup as a view of the same case records.
Update those consumers in the same change if that lookup is later removed.
RC5 remains responsible for changing production diagnostic representations;
compact observations in this test harness do not implement RC5.

## Coordination with the generated Cubist view

The companion [generated-source utility (#214)](https://github.com/KanHarI/cubist-math/pull/214)
is based on #211, separately from this documentation PR. It adds **Generated
Cubist** beside Read and Edit in `proof.html`, with a module selector and a
read-only view of the last check's theory, initial and free-model expansions.
The audited counts below remain measurements of `c1780211`; they do not include
this later UI work.

The utility retains generated declarations before reference lowering only when
requested by the browser program. Its renderer consumes that retained syntax
and the existing publication-family states; it does not run a second generator,
publish definitions or introduce another checking path. Failed and blocked
families remain visible with their actual state. Captured references use display
names, so the output is an inspection view, not a standalone Cubist module or a
replacement for checked-proof export. Unsupported display forms are reported by
declaration name without changing proof validity.

Carry these constraints into the planned work:

- **RC3:** preserve the inspection snapshot and family identity/status together
  across rollback, failed imports and rechecks. Retaining failed syntax for
  inspection must never make its bindings available to clients.
- **RC4/RC11:** migrate the generated-syntax renderer with any telescope, syntax
  or naming representation change. Keep grouped domains, implicit arguments,
  constructor patterns and captured references meaningful in the view. Share
  existing formatting and scope machinery where it reduces duplication; do not
  turn the display into a second expansion or elaboration implementation.
- **RC6/RC7:** retain host-side rendering and browser coverage for module
  selection, read-only behavior, stale-source notices, recheck invalidation,
  parse-failure recovery and static-site worker loading. The proof page's
  generation request belongs in the future shared worker client. Display tests
  remain host tests; ordinary Cubist tests continue to own proof validity.

This utility does not implement RC0–RC11, change the proposed pragma grammar,
or resolve the historical mutation-manifest or performance-budget follow-ups.

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
| [`kernel/src/instructions.c`](../../kernel/src/instructions.c) | 1,010 | 1,010 | Broad, not long: no function exceeds 38 lines. Preserve independent admission checks; no blanket shortening. |
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
| “FG0 maps historical fixes and passing controls to existing executable tests” reads other JS files and searches for literal `test("name",` strings. | Delete the source-spelling test and its `historicalCoverage`/`passingCoverage` data. Move the historical mapping into [`frontend-generation.md`](../../tests/fixtures/frontend-generation.md); retain case-ID uniqueness, fixture validation and coverage-matrix completeness checks from the revised #205. The actual historical regressions still execute. T0 can restore an executable mapping by stable case ID. |
| “migrated native proof scopes format without changing their expanded syntax” in [`unfolding-syntax.test.mjs`](../../tests/unfolding-syntax.test.mjs) repeats archive round trips for eight files. | Delete the repetition, and fix the archive round trip it repeats (below). Retain the prohibition on the old `with_unfolding(` spelling. Keep the focused scoped-syntax edge cases. |

Neither that test nor the archive round trip in
[`formatter.test.mjs`](../../tests/formatter.test.mjs) can fail today.
[`formatting.test.mjs`](../../tests/formatting.test.mjs) requires every
tracked `.cubist` source, the archive included, to be formatted already,
so both format fixed points: their token, comment, syntax-tree and
idempotence assertions compare a file with itself. Keep
`formatting.test.mjs`, and make the round trip test meaning preservation:
format each archive file at a narrower width and compare its tokens,
comments and syntax tree with the original's.

The wrapper “theory constructors keep header parameters apart from
generated field binders” in [`theories.test.mjs`](../../tests/theories.test.mjs)
stays until RC1. It asserts that `named_nat`, `named_hom`, `named_iso` and
`named_by_fields` in [`theory_headers.cubist`](../../cubist-tests/theory_headers.cubist)
verify. The inlined suite only compares refusals with `// Error:`
comments, which `tools/inline-errors.mjs --write` regenerates from current
behavior, so a regression could be recorded as expected. RC1 replaces the
wrapper with `test(...)` pragmas. The generated artifact/assumption test
immediately after it also adds coverage and must remain.

One further candidate needs a replacement before deletion: “both language
references and keyword styling describe the scoped syntax” checks literal
prose in HTML. Route executable reference examples through existing
reference checks and keep the keyword styling assertion. Removing prose
spelling checks must not remove verification of reference examples or
token styling.

Acceptance: record the named surviving check for each deletion; run
`npm test` and `npm run test:generation:mutations` separately; preserve
all required mutation targets and the selected Cubist declarations.
Show the repaired archive round trip failing against a deliberately
meaning-changing formatter edit. The PR should have a net reduction in
test/helper code. No new generic test
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

These comments have three readers, not one. Besides the inlined suite,
[`benchmark-runner.mjs`](../../web/benchmark-runner.mjs) reads a stated
`// Error:` as an intended refusal, and
[`tests/reference-pages.mjs`](../../tests/reference-pages.mjs) parses
reference examples' comments with its own reader, which also accepts an
end-of-line form. Merge the two readers before adding pragmas (RC9). When
a semantic golden becomes a pragma, every reader that consumed it must
read the pragma instead; otherwise the benchmark reports the intended
refusal as a failure. Pragmas should replace a mechanism, not become a
fourth.

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
creating another loader or a second way to check declarations; today
`inline-errors.mjs` and `check-program.mjs` each check a test module
their own way. Reuse a WASM instance where safe, but give each independent
case fresh program and kernel state with deterministic disposal. The
bridge holds at most eight sessions per instance
([`cubical_bridge.c`](../../wasm/cubical_bridge.c)).

The runner must also keep the mutation gate working.
[`frontend-generation-mutations.mjs`](../../tools/frontend-generation-mutations.mjs)
selects tests with `--test-name-pattern` over `tests/NAME.test.mjs` files,
and counts a kill only when the output contains `ERR_ASSERTION`. Register
each case as a `node:test` test or subtest whose name contains its stable
ID, and fail it through `assert`. The example below exercises G2's
contract, that fixed argument domains contribute to generated universes;
the required `hom-universe` mutation selects G2's test by name.

| Stage | Primitive and required behavior | First consumers |
| --- | --- | --- |
| T0 | **Named cases and checked declarations.** Stable IDs; enumerate cases once; reject duplicate IDs, missing named declarations, zero discovered cases and an empty explicit selection. `test(id)` requires its target to be present and, unless an expectation says otherwise, verified. Every unanticipated failure fails the case. | Positive initial/free-model clients; historical coverage mapping. |
| T1 | **Structured diagnostic expectations.** Match code, severity, phase, module/declaration and multiplicity; optionally a range selected by a unique source anchor. Distinguish parse, type mismatch, unsupported generation, blocked dependency and resource exhaustion. Unexpected errors/warnings fail unless an explicit code policy allows them. | G1/G3/G6/G11, negative parser cases, lint-sensitive theory clients. |
| T1 | **Assumption sets and public artifacts.** Assert none, exact set or subset, with an explicit nonempty check when needed. Compare resolved binding identities, including imports and generated declarations. Assert artifact presence/absence and supported family status through publication metadata. | Theory interfaces, hlevel proofs, quotient proofs, universe clients. |
| T2 | **Source observations.** Assert written occurrence range, label, module and definition target; distinguish original and synthetic locations. Anchors must resolve uniquely and fail if missing or ambiguous. | G8–G10 and frontend provenance tests. |
| T2 | **Deterministic resource observations.** Set work limits, assert failure kind and counters, including exact zero searches at a forbidden fallback. Observe speculative work in the same counters. If it is not charged to the same budget today, changing that is a production change with benchmark evidence, in its own PR. | G8 and bounded elaboration/search regressions. |
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
transform declarations. Each `# name(arguments)` attaches to the next
declaration or supported executable directive, whatever whitespace
separates them; several pragmas may attach to the same item. The
formatter writes each pragma on its own line, but newlines stay
insignificant to the grammar, as they are today. Argument payloads are
restricted data such as names, codes, integers and lists, not executable
Cubist expressions. Pragma names are contextual after `#`, so `test` or
`expect_axioms` need not become globally reserved identifiers. Keep them
out of `languageKeywords` and `reservedNames` in
[`parser.mjs`](../../web/cubist/parser.mjs): highlighting shares that
list, and a word styled as a keyword is reserved everywhere. Highlight a
pragma as a unit instead.

Accept pragmas only in test fixtures at first: modules under
`cubist-tests/` and fixtures a test runner supplies, enabled by the
loader for those sources. Reject them everywhere else, such as in
`library/`, the archive and reference examples. There, ordinary checking would parse
`# expect_axioms([...])` and never evaluate it: it would look like a
checked contract without being one. Widen their use only once ordinary
checking evaluates them.

Illustrative syntax below is **proposed, not implemented**. With the
pragma lines omitted, the Cubist program was checked at the audited head:
the twenty declarations that theory `T` generates and `hom_level` verify
without assumptions, and `too_low` reports E606.

```text
import hlevels;

# test(generation.hom_universe_interface)
# expect_axioms([])
theory T(U < UU0) { M : set U; op(A : U1, x : A) : M; }

# test(generation.hom_universe)
computable def hom_level(S : T(U0)) : U2 := T.Hom(S, S);

# test(generation.hom_universe_too_low)
# expect_error(E606)
def too_low(S : T(U0)) : U1 := T.Hom(S, S);
```

This tests acceptance at U2 and refusal at U1, not a general exact-type
query. The authored `hom_level` states its assumption contract with
`computable`; `expect_axioms` covers the generated members, which
`computable` cannot annotate. Expected equations and values must be
authored independently of the generator. Never derive the expected law
from another artifact of the same expansion: both can share the same
capture bug.

The initial surface should be `test(id)`, `expect_error(code)`,
`expect_warning(code)` and `expect_axioms([...])`. Successful checking is
the default for an item with `test(id)`, so positive cases need no extra
`succeeds` annotation. Until its module migrates, an unannotated
declaration keeps its `// Error:`/`// Warning:` contract. Once a module
migrates, prefer requiring every unannotated declaration in it to
succeed, so that `--write` cannot record a new refusal there. `test(id)`
gives a durable selectable case ID and requires its target to exist.
`expect_axioms([...])` specifies the exact resolved external axiom set;
the empty list asserts none. Subset/nonempty options, artifact queries,
source observations and work limits follow when their migration batch
needs them, rather than adding many synonyms up front.

The axiom set includes transitive dependencies through other definitions
and the declaration's type. Ordinary bound parameters and proof hypotheses
do not count as external axioms. This pragma checks the existing reported
dependencies; it neither introduces axioms nor permits an unchecked proof.
On a theory, it applies to each owned generated member separately, not to
their union, so a failure names the member that acquired an assumption.
Prefer `computable def` for authored definitions whose contract already
requires no assumptions, and lint `expect_axioms([])` on one, so that
contract has a single spelling. The test observation also covers
generated or imported declarations and exact nonempty axiom sets; later
subset checks can express, for example, that a quotient proof uses only
specified truncation axioms and does not acquire a dependency on choice.

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
change, together with every reader that consumed it. Avoid asserting the
same diagnostic through two independent mechanisms unless its exact
wording is intentionally under test. The golden-update command must never
create or rewrite pragmas automatically.

### Concrete migration batches

| Suite/cases | Move into Cubist | Keep in the host |
| --- | --- | --- |
| “theory constructors keep header parameters apart from generated field binders” in [`theories.test.mjs`](../../tests/theories.test.mjs) | `test(...)` on `named_nat`, `named_hom`, `named_iso` and `named_by_fields` in [`theory_headers.cubist`](../../cubist-tests/theory_headers.cubist); delete the wrapper in the same PR. | The generated artifact/assumption test that follows it, until T1 covers it. |
| First four tests in [`initial-models.test.mjs`](../../tests/initial-models.test.mjs): parameter capture, function/dependent-pair generators, grouped law binders, named/mixed arguments | Their source programs already contain checked client proofs; replace the `verified(...)` wrappers with discovered cases. | Migration-tool behavior, injected failures and native publication inspection. |
| Grouped-domain and repeated-name operation tests in [`theories.test.mjs`](../../tests/theories.test.mjs) | Existing client equations and computations, with explicit warning expectations. The old W706 workaround comment is no longer a reason to keep source in JS after FG5's lint changes. | Parser/formatter structure checks; generated artifact enumeration until T1 covers it. |
| [`frontend-universes.test.mjs`](../../tests/frontend-universes.test.mjs), source cases in [`frontend-evidence.test.mjs`](../../tests/frontend-evidence.test.mjs), G1/G2/G4/G6/G11/G12 | Positive clients, paired negative cases, assumptions and expected refusals. Keep direct, imported, inherited, renamed, fixed-universe and generic cases where they traverse different paths. | Direct construction of scopes/native terms and refinement/dimension restriction probes. |
| [`hlevel.test.mjs`](../../tests/hlevel.test.mjs) and [`quotient-universal.test.mjs`](../../tests/quotient-universal.test.mjs) | Use `computable def` for authored assumption-free proofs where equivalent; T1 handles generated/imported declarations and allowed assumption sets. | Low-level tactic/search instrumentation until its observation exists. |
| [`computability.test.mjs`](../../tests/computability.test.mjs) | Expected values and patterns using existing `evaluate ... expecting ...`. | Assertions about reporter completion after failed evaluation, until the runner exposes them; parser/formatter structure. |
| FG source links and diagnostics | T2 annotations replace hand-calculated JS offsets and repeated link scans. | Browser clicks, selection and navigation still need DOM tests. |

The quotient tests require a nonempty subset of specific truncation
assumptions. Replacing them with `computable` would change the contract
to no assumptions. Similarly, `test(id)` alone cannot replace the theory
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

Most of that checker state lives in a fifth file. Twelve of the fourteen
collections that `CubicalDeclarationTransaction` lists by hand for
rollback are created by `NativeCubicalElaborator` in
[`cubical-elaborator.mjs`](../../web/cubical-elaborator.mjs); the other two
are the kernel's. Each module also checks through
`Object.create(this.checker)` in `cubical-program.mjs`, so writes in
elaborator methods land on a per-module copy. The program copies `steps`
back by hand after a module, and the error path skips that copy.
[`translator/theories.mjs`](../../web/translator/theories.mjs) still
creates checker maps lazily with `??=`, although the constructor always
creates them, and the transaction still filters them with `.filter(Boolean)`.
Replace the prototype copy with an explicit module context (binding names
and `define`), and make the elaborator's collections part of the declared
participating stores.

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

Reuse `scopesOf`, `rewritten`, `substituted` and `renamedApart` in
[`scopes.mjs`](../../web/cubist/scopes.mjs) (its scope table, `SCOPES`, is
private), and the identity graph in
[`dependencies.mjs`](../../web/cubist/dependencies.mjs). Do not introduce
another general visitor or merge morphism transport support with
equational support: they intentionally allow different constructions.
The header of `scopes.mjs` says every traversal reads its scopes there,
but `namesIn` in `cubist/theories.mjs` nearly duplicates `allNames`, and
the binder walker in `legacy-syntax.mjs` restates binding scopes. Fold
`namesIn` into the pilot; `legacy-syntax.mjs` serves only the migration
verifier and can stay as it is.

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

Start with two slices that need no catalogue changes:

- **Lint warnings.** [`lint.mjs`](../../web/cubist/lint.mjs) writes each
  warning in English, then recovers its code with `diagnosticCode` and the
  W701–W707 patterns. It is the only module in `web/cubist/` that imports
  from outside the directory. Attach the code where the warning is made,
  and delete those patterns and the import.
- **Positions.** `SourceUnit.locate` in
  [`elaboration.mjs`](../../web/translator/elaboration.mjs) appends
  ` at L:C` to `error.message` although the error already carries
  `offset` and `sourceEnd`. `stated-comments.mjs`, `repl-session.mjs`,
  `cubical-program.mjs` and `describe` in `translate.mjs` then strip it or
  splice text before it. Keep the position structured, render it at the
  boundary, and share one line/column helper; `lint.mjs` and
  `translate.mjs` compute line starts separately today. Update the tests
  that match ` at \d+:\d+` deliberately.

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
| Workbench | Extract one worker client shared by `proof.mjs`, [`repl-console.mjs`](../../web/repl-console.mjs) and [`reference/examples.mjs`](../../web/reference/examples.mjs), each of which implements its own request/response exchange today; then renderer functions with explicit inputs; reuse existing navigation modules. | Preserve cancellation, stale-response rejection, source navigation and inspection. The REPL and reference clients have no worker `error` handler, so a worker that fails to load leaves their requests pending; a reference page loading both can start two workers. Separate from compiler refactors. |
| Browser scripts | Share the repeated server startup, readiness, Chromium lifetime and teardown used by landing, navigation, statement, cubical and inspector scripts; `site.browser.mjs` has a variant. | Keep scenario assertions. Older scripts are still invoked by [`release-evidence.mjs`](../../tools/release-evidence.mjs), even when absent from `test:browser`, which runs only the inspector. |
| Module inventories | Consolidate repeated discovery lists around [`modules.mjs`](../../web/cubist/modules.mjs) with deterministic validation/generation. Several tools find modules with `readdir` instead. | Preserve curated archive order, benchmark membership, titles and browser bundle inputs; automatic alphabetical discovery is not an equivalent replacement. Archive membership is checked only from list to file: also check that every archive file is listed. |
| Tool corpus checks | Four tools and the benchmark runner build an `import NAME;` program for the whole corpus their own way, and `elaboration-fingerprint.mjs` has its own source reader. Share one corpus check through [`module-sources.mjs`](../../tools/module-sources.mjs). | Compare each tool's fingerprints and reports before and after. |

Defer wholesale parser/kernel rewrites. In particular, the large native
signature tests exercise admission conditions and malformed inputs that
well-typed Cubist cannot express. Keep invalid-handle, ABI, isolation and
allocation-failure tests in C/JS. Do not delete an independent validator
to reduce line count. Do not table-drive instruction admission either:
the shared prologue is small, and per-instruction checks are the point.
The kernel's long functions are in normalization and computation, not in
`instructions.c`: `weak` in [`term_normalize.c`](../../kernel/src/term_normalize.c)
(212 lines), `ck_reduce_composition` (119) and `contract` in
`instruction_equality.c` (114). Split `weak` by term kind only behind
normal-form differential evidence, such as the evaluation baseline's
digests.

### Single sources of truth

Each row is a fact the code states more than once, where copies can
drift without a test noticing. Consolidate one row per PR, with a parity
test where the copies cross a language or build boundary.

| Fact | Copies today | Proposal |
| --- | --- | --- |
| Which commands verify the project | [`ci.yml`](../../.github/workflows/ci.yml), [`pages.yml`](../../.github/workflows/pages.yml), `localChecks` in `release-evidence.mjs` and a hand list in `release-evidence.test.mjs`, which says it matches CI but never reads it. Release evidence omits `test:generation:mutations`; CI omits instruction coverage and four browser scripts. | Derive the lists from `package.json` scripts and state deliberate differences in one place. |
| Expected-diagnostic comments | `stated-comments.mjs` and `tests/reference-pages.mjs`, with different continuation rules; read by the inlined suite, the benchmark and reference tests. | One reader, before pragmas (see above). |
| Test-host setup | The fixture-overlay reader `(name, importer) => fixtures[name] ?? library(name, importer)` in nine test files; at least eight “verified with no axioms” helpers; 74 hand-built `new CubicalProgram(await createCubical())` in 21 files. In `tests/translator/`, `close()` repeats in seven files. | `fixtures`, program and acceptance helpers in `check-program.mjs`; kernel helpers in `kernel-check.mjs`. |
| Source tokens | The parser's tokenizer and the highlighter's `tokenPattern` in [`source-tokens.mjs`](../../web/source-tokens.mjs) disagree on `>=`, `<-`, decimal and fraction literals, and `0b` literals; `proof.mjs` and `lint.mjs` scan source again. | Export one scanner from the parser that keeps whitespace and comments, and build highlighting on it. |
| Lexical sets | The universe-constant test, `Unit`/`Void`/`tt` and operator lists each recur in three or four files, and two different lists are both exported as `notationOperators`. | Export the predicates and tables from `parser.mjs`; rename the private one. |
| Term-tag metadata | The binder tags `Pi`, `Lam`, `Sigma`, `LPi`, `LLam` listed in seven places; field tables in `translator/core.mjs` and `dimension-slots.mjs`; two free-dimension functions; ad hoc free-name scans in the notation and source-text printers. | One table of fields and binding positions, one free-names module. Printers need a variant that tolerates display-only terms; the native codec in `cubical-syntax.mjs` stays separate unless a parity test covers it. |
| Builtins | `builtinTerm` in [`translator/builtins.mjs`](../../web/translator/builtins.mjs) is a 257-line `if` chain, separate from `builtinNames`; nothing checks that every reserved builtin has a handler. | A dispatch table and a parity test, so a reserved name cannot fall through to an ordinary call. |
| The WASM interface | JS copies `cubical_kernel.h`'s enums by position (`cubicalKinds`, `errorKinds`, instructions, step rules); the 64-bit step budget is split into halves at each call; raw `_cb_*` calls appear in more than a dozen files. | A test that checks the header's enums against the JS arrays, and a `setStepBudget` wrapper. |
| Site layout | [`build-site.mjs`](../../tools/build-site.mjs) and [`serve.py`](../../tools/serve.py) each list the published roots and rewrite import versions with their own pattern. | Generate one from the other, or test that they agree. |

### Small independent fixes

None needs a design decision; each is a small PR or part of one.

- **Dead code.** [`web/cubist/notation.mjs`](../../web/cubist/notation.mjs)
  (134 lines) has no importers. `rewriteFirst` in
  `translator/proof-rewrite.mjs` has no callers, and `translate.mjs`
  rebuilds its errors inline. `tests/source-edit.mjs` is unreferenced. The
  exports `binaryLiteralExpansion`, `ththRules` and `cubicalSourceFiles` are
  never imported, and the retired `W` kind is still handled in `cubical-assembly.mjs`
  and `cubical-inspection.mjs`.
- **Dev-server staleness.** The `/cubist-version` hash in `serve.py` omits
  `web/diagnostics.mjs`, `module-listing.mjs`, `module-resolution.mjs` and
  `repl-session.mjs`, all in the worker's import closure, so editing them
  does not refresh the workbench's compiler. Hash the closure instead of
  globs.
- **Build prerequisites.** The `web/dist/cubical.mjs` rule in the
  [`Makefile`](../../Makefile) omits `kernel/src/internal.h`;
  `kernel/Makefile` lists `TESTS` by hand, so a new `test_*.c` is not
  built; five C test files define their own `ok()` helper.
- **Process-wide counters.** `serial` in `translator/lexical.mjs` and
  `placeholders` in `translator/arguments.mjs` are module-level, against
  the per-unit determinism contract in `translator/names.mjs`. Move them
  into the source unit's name supply.

## Ordered PR roadmap

Each row is a reviewable slice; stop or subdivide if it grows beyond the
stated boundary. RC0 is the recommended next PR after this document.

| ID | Deliverable | Depends on | Risk and exit evidence |
| --- | --- | --- | --- |
| RC0 | Finish deleting the remaining redundant checks listed above; make the archive round trip test meaning preservation. | This roadmap | Low. Net test/helper deletion; surviving cases named; full suite and required mutation kills preserved; the repaired round trip fails against a meaning-changing formatter edit. |
| RC1 | Parse/format the initial pragmas, implement T0/T1 in the existing runner, and migrate the first initial-model/theory cases, including the `theory_headers` wrapper. | RC0, RC9 | Medium. Unknown/dangling pragmas, pragmas outside test fixtures, missing/duplicate cases, unexpected failures and assumption mismatches demonstrably fail; formatting preserves attachment and spans. The benchmark reads migrated refusals from pragmas; mutation selectors still classify kills. Old wrappers removed in the same PR; no second module loader. |
| RC2 | T2 source/work observations, then migrate FG source assertions. Add T3 module scenarios as a separate sub-PR when needed. | RC1 | Medium. Every migrated contract detects the same deliberate defect; retain browser and native fault injection. |
| RC3 | Consolidate publication lifecycle and declaration scheduling, including the elaborator's collections and an explicit module context in place of the per-module prototype checker. | RC0; RC1 useful, not required | High. Rollback, observer failure, import repair and partial-family controls pass; native handles and frontend metadata agree; the error path accounts steps as the success path does. Compare allocation/work counters. |
| RC4 | Pilot telescope/builder consolidation for Hom, then widen by family. | RC1; coordinate with RC3 | High. Intended/captured law pairs, universe matrix, assumptions and source origins preserved; old conversion path deleted for each migrated slice. |
| RC5 | Structured diagnostics: lint codes and structured positions first, then producer migration one family at a time. | Lint and position slices independent; later families RC1 | Medium. Codes/spans stable; presentation snapshots reviewed; corresponding English classifier branches and position-stripping patterns removed. |
| RC6 | Share browser fixtures (including the statement and site scripts), reconcile module inventories and share tool corpus checks, in separate PRs. | Independent | Low/medium. Existing release/browser scenarios, discovery membership and tool reports preserved; setup/list duplication removed. |
| RC7 | Extract one workbench worker client for the proof page, REPL and reference examples, then renderer functions; separately consider driver policy/trace extraction after profiling. | Independent of test migration; keep clear of RC3/RC4 | Medium/high. Stale-worker, worker-load-failure and UI controls pass; driver changes preserve instruction validity and work budgets. No trusted-kernel rewrite. |
| RC8 | The [small independent fixes](#small-independent-fixes): dead code, dev-server hash, build prerequisites, process-wide counters. | Independent | Low. Deleted code has no importers; editing any module in the worker's import closure refreshes the workbench; full suite unchanged. |
| RC9 | One reader for expected-diagnostic comments, and shared test-host helpers in `check-program.mjs`. | Independent; before RC1 | Low. Reference-example and inlined-suite results unchanged, including the end-of-line form; copies removed. |
| RC10 | Derive the verification lists from `package.json` scripts. | Independent | Low. CI, Pages, release evidence and its test name the same checks, or list their differences in one place; release evidence includes the mutation gate. |
| RC11 | The remaining [single sources of truth](#single-sources-of-truth), one row per PR: tokens and lexical sets, term-tag metadata, builtin dispatch, WASM enums, site layout. | Independent; coordinate term tags with RC4 | Medium. A parity test for each consolidated fact; generated names, goldens and normal-form digests unchanged unless reviewed. |

Do not implement these as one cleanup mega-PR. RC1 should deliver actual
source migrations, not only add infrastructure; RC3/RC4 should remove
their previous paths rather than retain permanent compatibility layers.

## Preservation and completion criteria

- For each removed assertion, identify the surviving case and the behavior
  it distinguishes. For a mutation-targeted migration, run the same bad
  implementation against the new case before deleting the JS assertion.
  Update mutation selectors to stable case IDs as the runner gains them.
- Keep all required FG mutation kills (the original thirteen plus recursive shadowing), with passing unmodified
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
