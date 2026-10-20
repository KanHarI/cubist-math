# Archive retirement (I0.5)

**Direction adopted on 2026-10-20:** the first library in
`archive/first-library/` is retired. It remains regression evidence until the
results the library must keep have been rebuilt on the H1 foundation; then the
directory, its module root and the compatibility machinery that exists only
for it are deleted. The timing is open: retirement follows the runtime phase
and is a prerequisite of no scheduled package. This note owns the follow-ups
that other tasks hand to the retirement, starting with the legacy truncation
assumptions of K2.5. It is a plan, not a delivered change; the
[work plan](work-plan.md#stage-0-delivered-baseline-and-remaining-documentation)
schedules it as I0.5.

## What the archive is today

Measured on 2026-10-20 at main `694882af` with
`node tools/audit-cubical.mjs --all`: 368 modules (372 checked, with the
library prelude they import), 3,810 declarations, all checked. I0.2 archived
it; the [module resolution contract](work-plan.md#stage-0-delivered-baseline-and-remaining-documentation)
reads it last, after `cubist-tests/` and `library/`, for fixtures, files
outside the roots, REPL entries and reference examples, and never for a
library module.

[Results of the first library](../library-results.md) records what it proved,
in statements independent of its encodings, and names the modules that hold
each area. What the library already builds has left the archive: `nat`'s
arithmetic (from `primes`) and `sets` (for `hlevels`). What the library builds
differently remains and is not migrated in place: `truncation` and
`classical` rest on the legacy `Truncate` assumptions, `set_quotients` are
predicate quotients over them, and `equivalences` are bijections and
half-adjoint equivalences where the library has contractible maps.

## What depends on it

Measured on 2026-10-20, as files that import an archive module or read the
archive directory.

| Consumer | Files | What they use |
| --- | --- | --- |
| `cubist-tests/` fixtures | 65 | 26 import only `primes`, for `simp`, `calc` and `rw` fixtures; 26 are mathematical regressions over Galois theory, polynomials, dimension, linear algebra and quotient groups; 11 import a small helper, `w`, `paths_`, `pushout`, `suspension_types`, `binary_naturals`, `binary_arithmetic` or `classical`; `h1_cauchy_quotient` and `h1_zorn_step` build on archive developments by design |
| Reference pages | 5 | `paths`, `assumptions`, `checking`, `induction` and `cubical` import `paths_`, `classical`, `binary_naturals`, `pushout` and `suspension_types` |
| JavaScript tests | 22 | The Artin, Galois, dimension, linear-algebra and polynomial suites; corpus, benchmark, inspection, statement, module-resolution, proof-migration, search-fuel, historical-syntax, site-layout, landing and inspector tests |
| Tools | 13 | The archive audit, instruction coverage, elaboration fingerprint, evaluation baseline, generation metrics, linearization, proof-syntax migration, migration and module sources, search-fuel baseline, test selection, the migration verifier and the module list |
| Web | 5 | The module list, listing, resolution, the proof workspace and the reference examples |
| Legacy assumptions | 6 modules | `truncation` and `field_logic` wrap `Truncate`, `TruncateIntro`, `TruncateProp` and `TruncateElim` for 77 and 35 modules (the specification's count of 2026-09-27); `independent_extension`, `linear_span`, `span_subspace` and `vector_subspaces` use them directly. See [K2.5](hott/h1-truncation-migration.md#removing-the-legacy-assumptions) |
| Docs | | The tactical checkpoints (Galois, complex analysis, basis theorem and others), the mathematics roadmaps' checked-progress columns, and the module table of the results catalog |

Archive coverage is also compatibility evidence for the instruction kernel
([the instruction kernel and this plan](work-plan.md#the-instruction-kernel-and-this-plan)):
every stored definition derives again under the driver. That evidence moves to
the library and the fixtures as the archive shrinks.

## What retirement means

- The archive directory and its module root are deleted. Module resolution
  loses its archive fallback, and the machinery that serves only archive
  sources goes with it: the retired-syntax readers in `web/cubist/legacy-*.mjs`
  where nothing else reads historical sources, archive-specific tool roots,
  and the archive module list.
- Results the library must keep are rebuilt in `library/` first, on H1:
  `Trunc`, `Quotient`, `hlevels` and theories, stated at the universes they
  need and computable where assumption-free. The results catalog decides what
  "must keep" means, area by area. A result that is not rebuilt stays in the
  catalog as proved by the first library only, with its logical footprint.
- Git history and the catalog keep the record. No archive source stays in the
  tree unchecked.
- Retirement is not a blanket rebuild. The
  [deferred library backlog](work-plan.md#deferred-library-backlog) B3–B5
  stays deferred; paused mathematics does not resume because the archive goes.

## Steps

Each step is small enough for one pull request, or a few.

| Step | Work | Measure |
| --- | --- | --- |
| R1 | Confine new dependencies. Fixtures and reference examples that import an archive module only for a small helper (`primes`'s rules, `paths_`, `w`, `pushout`, `suspension_types`, `binary_naturals`, `binary_arithmetic`, `classical`) take it from the library or from `cubist-tests/`; `simp` fixtures get rules of their own | Archive imports from `cubist-tests/` and the reference fall to the mathematical regressions and the two H1 slices |
| R2 | Legacy truncation confined to the archive: K2.5's steps 1–4 in the [removal plan](hott/h1-truncation-migration.md#removing-the-legacy-assumptions), with excluded middle and choice as `def … := axiom …` definitions in `classical_axioms` | No library, fixture, reference or guide directly invokes `Truncate`, `TruncateIntro`, `TruncateProp`, `TruncateElim` or the builtin `LEM`/`Choice`; archive regression expectations retain the legacy labels until their tests retire |
| R3 | Decide per area of the results catalog: rebuild in the library before deletion, or record and drop. The mathematics roadmaps that cite archive modules as checked progress (Galois, complex analysis, reals) record what their archive modules proved and what the rebuild must restate | A decision per catalog area, recorded in the catalog |
| R4 | Remaining fixtures, reference examples, tests and tools. Following R3's decisions, move or retire the 26 mathematical regression fixtures and the two H1 slices left after R1, and any other remaining archive-dependent fixture or reference example; update their module lists, test selections and generated file index together. Each archive-reading JavaScript test moves to library modules or retires with the module it tests; the audit, coverage, fingerprint and baseline tools take `library/` and `cubist-tests/` roots; remaining archive-dependent ledger comparisons retire with their last passing revisions recorded before the migration verifier loses its archive baseline resolution | None of the original 65 fixtures, 5 reference pages, 22 tests or 13 tools, nor any replacements, imports an archive module or reads an archive path; the 28 fixtures deliberately retained by R1 have each migrated or retired |
| R5 | Delete. The directory, the module list and the resolution root; the legacy assumptions (K2.5 step 5); archive-only readers and settings. The tactical checkpoints move to `historical/`, the catalog's module table becomes a historical record, and the roadmap index and documentation index are updated | `npm test`, the site build and the reference pass with no `archive/` directory; `git grep archive/first-library` finds only historical documents |

Acceptance for R5 is the measure in its row, with the catalog's per-area
decisions of R3 recorded before the deletion.

## Relation to other work

- [K2.5](work-plan.md#stage-2-one-sort-signatures-basic-theories-and-matching):
  the legacy truncation assumptions are removed with the archive; the
  archive's 47 resizing-dependent declarations are rebuilt or recorded by R3,
  not migrated in place.
- I1.1, module resolution: the archive root is the last fallback and the only
  one that goes.
- The [instruction coverage report](work-plan.md#the-instruction-kernel-and-this-plan):
  archive coverage is replaced by library and fixture coverage as evidence.
- The [mathematics roadmaps](README.md#mathematics) and the tactical
  checkpoints: their checked progress is archive progress until R3 decides
  what the library rebuilds.
- The [runtime evaluation track](runtime/runtime-evaluation-roadmap.md):
  evaluation baselines that run archive workloads need library workloads
  before R5.
- The [deferred library backlog](work-plan.md#deferred-library-backlog):
  R3's decisions name which B3–B5 results the retirement waits for.

## Open decisions

1. Which catalog areas are rebuilt before deletion, and which are recorded and
   dropped. The Galois and analysis developments are the largest.
2. Whether the retired-syntax readers go with the archive, or stay for
   historical sources outside the tree.
3. When R3–R5 start: after the runtime phase, and not as a gate of the
   language progression.
