# FG1 declaration ownership and publication

This implements the ownership and publication contracts in the
[frontend generation roadmap](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication).
The pinned historical inventory remains evidence about `00d4ecce`.
G1 and G6 are active regressions in `tests/frontend-generation.test.mjs`;
G7 now has controlled failure injection in `tests/frontend-publication.test.mjs`.

## Ownership and dependencies

A module-local ownership table reserves ordinary declarations, inductive
constructors and all names of a generated expansion before checking them.
Each entry retains the module, declaration kind, source token, binding
identity and lifecycle state independently of aliases in the environment.
E872 refuses a conflicting local declaration without replacing the earlier
binding, native definition, source location or inspection symbol. A refused
duplicate makes the check incomplete even when every retained symbol is
checked. Import shadowing and local binders remain legal. Model notation
extensions still use their separate policy: a model's declaring module
may add numeral/literal rules. Refusing an extension records a directive
error and preserves the model's existing symbol and notation.

An invalid theory retains its original failure. A child reports E340 at
its parent reference, with the dependency identity and original cause,
instead of expanding the parent's invalid syntax as new source. A failed
optional operation remains an unavailable alias when a model is opened;
it does not stop checked fields being used.

## Publication groups

Generators assign family metadata explicitly. The scheduler does not infer
dependencies from dotted names.

| Group | Required members | Required predecessors |
| --- | --- | --- |
| Base theory | Model type, constructor, field projections, parent projections | Checked imported dependencies |
| Each derived operation | Its checked definition | Base theory and dependencies read by its body |
| Hom | Model type, constructor, projections, identity, composition, parent maps | Base theory |
| Iso | Model type, constructor, projections, identity, composition, inverse | Base theory and Hom |
| Initial/free prototype | Carrier signature, model, fold map, fold | Requested checked theory and referenced artifacts |

The native kernel has one active checkpoint. A generated group therefore
uses one checkpoint across all its members, with no nested declaration
checkpoints. Members can use checked predecessors inside the group, but
failure rolls back every member, including previously admitted native
signatures and definitions. A failed Hom or derived operation leaves the
base theory available; a failed Hom blocks its Iso group.

Rollback restores environment aliases, native stores, theory/projection
and notation metadata, source references, views, local symbols and proof
steps. One failed owner records the responsible member and original source
error; skipped dependents retain the original cause without cascades.
Progress counts attempted work and removes only unattempted queue members.
The benchmark uses the same transaction boundary and marks previously
checked but rolled-back members as blocked.

Checking an edited source graph invalidates the previous kernel session
and all dependent frontend caches before replay. This includes changes to
imported theories with unchanged main source. REPL entries deliberately
extend their immutable in-memory session snapshot instead of re-reading
previous entries as files. Exports still replay supplied source through
the ordinary checker.

## Producer and consumer audit

| Boundary | Producer and consumers |
| --- | --- |
| Reservations and lifecycle | `translator/declarations.mjs`; `Translator.translate` reserves definitions, inductives and expansion plans together. Constructor checks retain their more specific within-signature diagnostics. |
| Group roles | `cubist/theories.mjs` and `cubist/morphisms.mjs` assign roles; initial/free members carry their existing construction identity. The queue and program hooks consume the explicit groups. The former name-based skip helper is removed. |
| Dependency failure | Inheritance lookup and initial/free requests check availability before retained syntax; `Untranslated` carries the original binding/cause through imported aliases. Name availability during freshening is a separate, non-failing query. |
| Native state | `CubicalDeclarationTransaction` and `CubicalProgram` stage native definitions/signatures and the associated metadata; benchmark checking uses these same boundaries. |
| Separate diagnostics | Program results retain the earlier symbol and a duplicate gap. Inline-error reports, REPL, audit CLI, elaboration panels and the proof page consume that gap. E872 is in both diagnostic catalogues and the checked reference example. |
| Rechecking and export | Ordinary checks rediscover imports, including repaired reads, parse failures and interrupted loads. REPL entries reuse their immutable snapshot. Exported source is replayed and checked, including failures. |

## Evidence and limits

The publication tests inject failure after confirming that an earlier
member was admitted: a parent projection (G7), Hom composition, and an
initial-model fold. They inspect native definition/signature stores,
metadata and checked source links after rollback, and test unaffected
clients, import/edit recovery, progress and export replay. An observer
exception also rolls back its active group.

Five negative inductive fixture modules used the same constructor name
for unrelated declarations. They now give those constructors distinct
names, preserving their original shape, universe and positivity errors.
The refusal fixtures about hiding an imported dependency now actually
place that dependency in an imported module; a same-module duplicate is
E872. These are compatibility updates to test inputs, not acceptance of a
previously incorrect result.

`node tools/frontend-generation-metrics.mjs REPORT.json 3` runs the three
roadmap workloads in fresh sessions with default limits. It records the
revision, frontend/input digests, kernel build stamp, work counters,
declaration-boundary peak arena size and each wall time. Arena size is an
available memory measure, not a whole-process memory peak. No performance
budget is inferred from a single measurement.

Measured on Node v24.13.0 / Apple M3 Pro, three fresh sessions per workload,
with the same kernel build and default limits. The before report is
[`ed276a03`](frontend-generation-metrics/fg0.json); the after report is the
clean implementation commit [`fe05ea5e`](frontend-generation-metrics/fg1.json).
The baseline used the same source/measurement loop before the reusable
tool and frontend digests were added. Its raw build stamp and revision
are retained rather than retroactively filling missing provenance.

| Workload | Median wall ms, before → after | Instructions | Queries | Peak arena bytes |
| --- | --- | --- | --- | --- |
| Algebra import | 1251.9 → 1286.9 | 118781 → 118850 | 14411 → 14495 | 2889728 → 4593664 |
| Captured inheritance | 346.2 → 320.0 | 53172 → 51732 | 3735 → 3883 | 1772544 → 2624512 |
| Generated fold | 1316.1 → 1310.5 | 128166 → 125859 | 14927 → 14990 | 2889728 → 4593664 |

All samples checked without gaps or deadlines. Algebra/fold each had six
kernel budget-growth events after the change, versus five before;
inheritance had none. No limit was increased. The wider atomic checkpoints
retain more intermediate arena data until a family commits: observed peak
arena bytes rose about 59% for algebra/fold and 48% for inheritance. These
are costs to track in subsequent slices; the timings do not establish a
performance improvement or a regression budget.

Validation: `npm test -- --test-concurrency=4` reports 798 tests, 786 passed,
12 expected TODOs assigned to later phases, and no failures. The inspector
browser suite, built-site browser suite, diagnostic catalogue audit and
`git diff --check` pass. The standalone dependency-cause and interrupted
load tests also pass after their final strengthened assertions.

This phase does not implement FG2's complete dependency/support analysis,
FG3's universe inference, FG4's contextual evidence, or FG5's source-label
and lint contracts. Their remaining expected failures stay explicit in the
FG0 manifest. No initial/free capability or universal proof is registered.
