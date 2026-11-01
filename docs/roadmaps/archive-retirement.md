# Archive retirement (I0.5)

**Direction adopted on 2026-10-20:** the first library in
`archive/first-library/` is retired. It remains regression evidence until the
results the library must keep have been rebuilt on the H1 foundation; then the
directory, its module root and the compatibility machinery that exists only
for it are deleted. The timing is open: retirement follows the runtime phase
and is a prerequisite of no scheduled package. This note owns the follow-ups
that other tasks hand to the retirement. The legacy truncation assumptions
of K2.5 are no longer among them: since 2026-10-29 the archive uses the
library's truncation and axioms, and K2.5 removed the legacy builtins the
same day. It is a plan, not a delivered change; the
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
arithmetic and, by NT1, the unary order lemmas (both from `primes`); by
NT2, `euclid` and `primes`' divisibility and primality; by NT5, the rest of
`primes`, `natural_minimum` and the binary and radix numerals, which NT3
and NT4 rebuilt; and `sets` (for `hlevels`). What the library builds differently remains:
`set_quotients` are predicate quotients over the truncation, and
`equivalences` are bijections and half-adjoint equivalences where the
library has contractible maps. `truncation` and `classical` rested on the
legacy `Truncate` assumptions until 2026-10-29, when the user directed the
archive migrated in place to the library's `Trunc`, `LEM` and `Choice`,
with the library's `PropResizing` where a result needs a resized
proposition ([K2.5](hott/h1-truncation-migration.md#migration-in-place-2026-10-29)).

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
| Legacy assumptions | 6 modules | `truncation` and `field_logic` wrapped `Truncate`, `TruncateIntro`, `TruncateProp` and `TruncateElim` for 77 and 35 modules (the specification's count of 2026-09-27); `independent_extension`, `linear_span`, `span_subspace` and `vector_subspaces` used them directly. Migrated in place on 2026-10-29: they use the library's `Trunc`. See [K2.5](hott/h1-truncation-migration.md#removing-the-legacy-assumptions) |
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
| R2 | Legacy truncation confined to the archive: K2.5's steps 1–4 in the [removal plan](hott/h1-truncation-migration.md#removing-the-legacy-assumptions), with excluded middle and choice as `def … := axiom …` definitions in `classical_axioms` | No library, fixture, reference or guide directly invokes `Truncate`, `TruncateIntro`, `TruncateProp`, `TruncateElim` or the builtin `LEM`/`Choice`; archive regression expectations retain the legacy labels until their tests retire. Since 2026-10-29 the archive uses none of them either, its expectations list the library's axioms, and the builtins are removed from the language (K2.5 step 5) |
| R3 | Decide per area of the results catalog: rebuild in the library before deletion, or record and drop. The mathematics roadmaps that cite archive modules as checked progress (Galois, complex analysis, reals) record what their archive modules proved and what the rebuild must restate | A decision per catalog area, recorded in the catalog |
| R4 | Remaining fixtures, reference examples, tests and tools. Following R3's decisions, move or retire the 26 mathematical regression fixtures and the two H1 slices left after R1, and any other remaining archive-dependent fixture or reference example; update their module lists, test selections and generated file index together. Each archive-reading JavaScript test moves to library modules or retires with the module it tests; the audit, coverage, fingerprint and baseline tools take `library/` and `cubist-tests/` roots; remaining archive-dependent ledger comparisons retire with their last passing revisions recorded before the migration verifier loses its archive baseline resolution (K2.5 step 5 retired the last two, on 2026-10-29) | None of the original 65 fixtures, 5 reference pages, 22 tests or 13 tools, nor any replacements, imports an archive module or reads an archive path; the 28 fixtures deliberately retained by R1 have each migrated or retired |
| R5 | Delete. The directory, the module list and the resolution root; archive-only readers and settings. The tactical checkpoints move to `historical/`, the catalog's module table becomes a historical record, and the roadmap index and documentation index are updated | `npm test`, the site build and the reference pass with no `archive/` directory; `git grep archive/first-library` finds only historical documents |

Acceptance for R5 is the measure in its row, with the catalog's per-area
decisions of R3 recorded before the deletion.

**Scheduled early, on 2026-10-26.** Two parts no longer wait for the runtime
phase to end: R2 (K2.5's steps 1–4) runs alongside it, and so does the
archive's number theory, below. R2 is done (2026-10-28): the legacy
builtins were accepted only in an archive module, read unedited from the
archive's root, and refused anywhere else. On 2026-10-29, by the user's
decision, the archive was migrated in place, and K2.5 removed the builtins
without waiting for R5: no module, the archive's included, can use them.

## Number theory in the library

**Directed on 2026-10-26:** all number theory in the archive moves to the
library, and then leaves the archive. This is R3's decision for the
arithmetic part of "Numbers and counting": rebuild. The scope below was
measured on main `7230825e`; imports are transitive, so "used by" counts
every module that reaches a definition, not only direct importers.

| Archive source | What it holds and who uses it | In the library |
| --- | --- | --- |
| `primes` (637 lines): divisibility and primality | `Divides`, its decision and lemmas, `Prime`, `prime_divisor_exists`, `factorial_positive`, `bounded_divisor_of_factorial`. Among Cubist sources only `euclid` uses them; JavaScript tests, the evaluation baseline and the Cubist guide name some of them | **Done** (NT2): EVAL7's remainder-based divisibility, primality and least-prime-divisor search over binary `Nat` (`divisibility`, `prime_numbers`), with `nat`'s binary factorial; deleted from `primes`, which keeps 258 lines |
| `euclid` (25 lines) | Euclid's theorem ★; the showcase example of the site, the reference and many tests, and the evaluation baseline's workload | **Done** (NT2): the library's `euclid` over binary `Nat`; every consumer moved to it, and the archive's is deleted |
| `primes`: nine unary order and equality lemmas | `unat_zero_ne_succ`, `nat_le_zero`, `nat_le_step`, `nat_le_trans`, `nat_le_total`, `nat_le_succ_split`, `nat_le_add`, `nat_eq_decidable`, `nat_add_positive`. Used by polynomial, linear-algebra, Galois, analysis and radix modules, and the `h1_cauchy_quotient` fixture | **Done** (NT1): `unat`'s `unat_zero_ne_succ`, `unat_le_zero`, `unat_le_step`, `unat_le_trans`, `unat_le_total`, `unat_le_succ_split`, `unat_le_add` and `unat_add_positive`, and `unat_decide`, which moved from `hlevels` to `unat`; the archive imports them from there, as it did `nat`'s arithmetic |
| `primes`: bounded least-witness search; `natural_minimum` (72 lines) | Least elements of decidable predicates; `polynomial_degree` and `artin_degree` import `natural_minimum` | **Done** (NT3): `least_elements` over binary `Nat`, and `unat_least_elements` over `UNat`, by which the archive's polynomials index their coefficients; the search and `natural_minimum` have no consumer left, and NT5 deleted them |
| `primes`: unary `factorial` | Used by four binary and radix transfer modules | **Done** (NT4): `nat`'s binary factorial, and `radix_factorials`' in every radix; only the archive's `binary_*` and `radix_*` modules use the unary one, and NT5 deleted it with them |
| `binary_*` (6 modules, 672 lines) | Binary numerals: induction, arithmetic, equivalence with unary, correctness and the 10! transfer. Helper imports from the fixtures `wasm_binary_literal`, `computability_evaluation` and `wasm_bad_factorial` | **Done** (NT4): checked against NUM0/NUM1's `bnat_*` ([correspondence](../reports/radix-numerals.md#binary-numerals)); 10! in binary and carried by transport added in `radix_factorials`; the three fixtures import the library; NT5 deleted the archive's |
| `radix_*` (11 modules, 2,347 lines) | Positional numerals in every base b ≥ 2: uniqueness, arithmetic and factorial correspondence, direct conversion to binary, 10! in bases 2 and 10 | **Done** (NT4): rebuilt over binary `Nat` in `radix_numerals`, `radix_operations`, `radix_conversion` and `radix_factorials` (879 lines; [correspondence](../reports/radix-numerals.md#radix-numerals)); NT5 deleted the archive's |

Steps, each one or a few pull requests:

| Step | Work |
| --- | --- |
| NT1 | The unary order and equality lemmas move to `unat`; the archive's users import them there. **Done** on 2026-10-28: `primes` keeps none of them, its users name the `unat_*` lemmas, and `nat_eq_decidable`'s users take `unat_decide`, or `unat_is_set` where they rebuilt it with Hedberg |
| NT2 | EVAL7: divisibility, primality and Euclid in the library; every consumer of `euclid` moves to it. **Done** on 2026-10-28 ([report](../reports/binary-euclid.md)): the library modules `bnat_order_laws`, `bnat_division`, `divisibility`, `prime_numbers` and `euclid` (named `binary_euclid` until the archive's was deleted); the site, reference, tests, evaluation baseline (version 10) and probes moved to it; the archive's `euclid` and `primes`' divisibility and primality deleted, and Euclid's theorem recorded as rebuilt in the catalog |
| NT3 | Least elements: the bounded search and `natural_minimum` in the library; `polynomial_degree` and `artin_degree` import it. **Done** on 2026-10-30: the library's `least_elements` finds the least element of a decidable predicate over binary `Nat` from a witness, deciding 0, 1, 2, … by `nat`'s Peano recursion, so it stops at the least element however large the witness; a least element is unique, so for a predicate valued in propositions its mere existence gives it (`least_element_from_mere`). Every definition is `computable` and assumption-free, and source contracts evaluate the search. It computes least elements up to 63, 64 candidates, and stops with K344 at 64, the depth guard NUM1's recursion meets ([findings](../reports/binary-euclid.md#findings)). `unat_least_elements` has the same over `UNat`, by structural recursion: the archive's polynomials index their coefficients by `UNat`, and 21 modules use their degree's cutoff, so moving them to binary `Nat` is not small. `polynomial_degree` defines `classical_least`, excluded middle's decision passed to `unat_least_element_from_mere`, which `polynomial_ideals` and `polynomial_irreducible_factors` use too, and imports `finite_basis_search`, which it reached through `natural_minimum`; `artin_degree` and `polynomial_monic` needed only that unary order is a proposition, `unat`'s `unat_le_is_prop`. Nothing imports `natural_minimum` or uses `primes`' search; NT5 deletes them. `unat` gains its order's antisymmetry and propositionality, `bnat_order_laws` antisymmetry on the bits, and `nat` takes `nat_succ_add_shift` from `prime_numbers`. `node tools/audit-cubical.mjs --all` checks 374 modules and 3,873 declarations with no failure, against main's 3,857: `unat_least_elements`, a module of 13, `unat`'s 2 and `classical_least`. The driver trace was recorded again for `unat`'s two |
| NT4 | Numerals: the binary results checked against `bnat_*` and completed; radix numerals rebuilt over binary `Nat`; the helper fixtures moved. **Done** on 2026-10-30 ([report](../reports/radix-numerals.md)): the library modules `radix_numerals`, `radix_operations`, `radix_conversion` and `radix_factorials`, with no assumption and every declaration `computable`, and general laws they use in `nat`, `bnat_order_laws` and `bnat_division` (quotient and remainder are unique); every binary result has its library counterpart or is superseded by the binary factorial; the source contracts `radix_contracts` evaluate conversions, transport along the univalence path and factorials in base 10 and base 2; `wasm_binary_literal`, `wasm_bad_factorial` and `computability_evaluation`, their JavaScript tests, three more tests and the reference's binary numbers moved to the library. The archive consumers left for NT5 are listed in the report |
| NT5 | Delete `primes`, `natural_minimum`, `binary_*` and `radix_*` (19 modules) from the archive, update the catalog's module table and record the rebuilt results. **Done** on 2026-10-30: the 19 modules (3,353 lines) are deleted, and the catalog's module table no longer lists them; its numerals entry links the library's radix and binary modules and the [correspondence](../reports/radix-numerals.md#correspondence). Every other module that imported `primes` reached only `unat` through it: six archive modules drop the import; one unused import removed from `finite_cardinalities`, a counting module, and nothing else in the counting modules changed, so the counting decision below stays open (their 144 declarations check with unchanged, empty, assumption lists); 27 Cubist tests, the HoTT fixtures and the proof-ergonomics examples import `unat`, five JavaScript tests name it where they named `primes`, and the REPL test's mocked module list names `circle`; and 26 of those Cubist tests, R1's fixtures that imported only `primes`, now import no archive module. The instruction driver's face-step test derives `radix_factorials`' `radix_factorial_from_nat`, and its Glue test defines `ua` and `UnivalenceBeta` from a three-line source over `paths_`; `tests/cubical-transfers.test.mjs` and its two helpers retire, since the library transports along `radix_path` in Cubist, `tests/cubical-wasm.test.mjs` checks the arena of 10! carried from base 10, and the Glue builders have their own tests. The source printer's `0b` display of the archive's `BinaryNat` goes; `BNat`'s decimal display keeps the digit reader. The HoTT and ergonomics measurement scripts select `circle`'s `successor_transport` and `unat`'s `unat_add_assoc`, and run again; their recorded baselines, the saved benchmark reports and the capture-bindings costs stay dated records. `node tools/audit-cubical.mjs --all` checks 353 modules and 3,527 declarations with no failure, against 374 and 3,873: the 19 modules' 331 declarations, and the library's `lexemes` (8) and `lists` (7), which only `binary_naturals` imported; the corpus test records the count |

**Open:** whether the counting results of the same catalog area count as
number theory here: finite cardinalities, counting functions and
permutations, binomial types and fibered counting (8 modules, 1,323 lines).
They stay in the archive until decided. NT5 removed one unused import, of
`primes`, from `finite_cardinalities` and changed nothing else in them.

## Relation to other work

- [K2.5](work-plan.md#stage-2-one-sort-signatures-basic-theories-and-matching):
  since 2026-10-29 (the user's decision) the archive is migrated in place to
  the library's truncation and axioms, and K2.5 removed the legacy
  truncation assumptions the same day, before the retirement. The archive's 47
  resizing-dependent declarations are kept: 27 need no resizing, and 20 use
  the library's `PropResizing`. R3 still decides which the library rebuilds,
  at the universes they need.
- I1.1, module resolution: the archive root is the last fallback and the only
  one that goes. Its provenance, which vouched for the only modules that
  could use the legacy builtins (`fromArchive`, K2.5 step 4), left with the
  builtins on 2026-10-29.
- The [instruction coverage report](work-plan.md#the-instruction-kernel-and-this-plan):
  archive coverage is replaced by library and fixture coverage as evidence.
- The [mathematics roadmaps](README.md#mathematics) and the tactical
  checkpoints: their checked progress is archive progress until R3 decides
  what the library rebuilds.
- The [runtime evaluation track](runtime/runtime-evaluation-roadmap.md):
  evaluation baselines that run archive workloads need library workloads
  before R5. EVAL7's library Euclid supplies the Euclid workloads and
  replaces the archive's.
- The [deferred library backlog](work-plan.md#deferred-library-backlog):
  R3's decisions name which B3–B5 results the retirement waits for.

## Open decisions

1. Which catalog areas are rebuilt before deletion, and which are recorded and
   dropped. The Galois and analysis developments are the largest.
2. Whether the retired-syntax readers go with the archive, or stay for
   historical sources outside the tree.
3. When R3–R5 start: after the runtime phase, and not as a gate of the
   language progression. The number theory (NT1–NT5) and R2 are scheduled
   earlier (2026-10-26).
4. Whether the counting results (finite cardinalities, functions and
   permutations, binomial types, fibered counting) join the number theory's
   early migration or wait for R3.
