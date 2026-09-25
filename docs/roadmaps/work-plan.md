# Work plan: kernel, language, library rebuild and reference

Status: plan of 2026-09-25, after merging PRs #2–#4 into
`proof-ergonomics-roadmap`. It sequences these documents:
- the [kernel roadmap](cubical-kernel-roadmap.md): G0, H1–H4;
- the [proof ergonomics roadmap](proof-ergonomics-roadmap.md): milestones 5–8;
- the [HoTT automation roadmap](hott-automation-roadmap.md);
- the [reals roadmap](reals-roadmap.md);
- the two adopted designs,
  [higher inductive-inductive types](higher-inductive-types-design.md) and
  [theories and inductive declarations](inductive-language-features.md).

The rebuild's specification is [library-results.md](../library-results.md).

**Governing requirement.** Computability is expressible and preserved. Every
stage's acceptance includes the canonicity fixture. Every rebuilt result that
can compute is marked `computable`, and its computations are tested with
`evaluate`.

**Sizes** are relative (S < M < L < XL): dependency-sized work packages, not
time estimates. **IDs:** K = kernel, L = language and elaborator, B = library
rebuild, D = reference and documentation, I = infrastructure. Every package
lands with its tests, and kernel packages land in the reference checker
before the C kernel.

## Overview

| Stage | Theme | Gate to leave the stage |
| --- | --- | --- |
| 0 | Consolidate: merge, archive, computability tracking, reference harness | Archive checked in CI; `computable` and `evaluate` available; reference examples checked |
| 1 | Universes (G0) and the goal layer | G0 reviewed, and both checkers agree; archive templates rechecked generically |
| 2 | One-sort inductive signatures (H1) and the first language release | H1 soundness note reviewed; hand-coded rules agree with H1; `inductive`/`match`/theories released |
| 3 | Rebuild wave 1: foundations, numbers, counting, order, homotopy types, groups | Hull and iconic results of those areas re-proved |
| 4 | Indexed families (H2), inference, rebuild wave 2: algebra, fields, Galois | `Id` with J on `refl`; implicit arguments; wave 2 results re-proved |
| 5 | Inductive-inductive types (H3), reals and analysis | H3 soundness note reviewed, or the fallback taken; Cauchy reals instance; analysis rebuilt |
| 6 | On demand: H4, G4, G5; resume the paused mathematical roadmaps | Per item |

Stages overlap wherever dependencies allow. For example, stage 1's tooling
packages (HoTT A1, A2, A4, A6) continue alongside stage 2.

## Stage 0: consolidate

| ID | Package | Owner | Depends on | Size |
| --- | --- | --- | --- | --- |
| I0.1 | Merge `proof-ergonomics-roadmap` into `main` (deferred: work continues off `main`) | — | Maintainer decision | S |
| I0.2 | Archive the first library (done) | Plan | — | M |
| I0.3 | Start the new library tree | Plan | I0.2 | S |
| I0.4 | Remove local scratch state (done) | — | — | S |
| L0.1 | Non-computing dependencies, `computable`, `evaluate` | Ergonomics 8 | — | M |
| D0.1 | Checked-example harness for the reference (done) | Plan | — | S |
| D0.2 | Reference chapters for the stable language | Plan | D0.1 | L |

**I0.2 Archive the first library.** Done on 2026-09-25, working off `main`
(I0.1 is deferred by choice).
- **Move.** The 367 sources moved from `web/proofs/` to
  `archive/first-library/` with history preserved. They are a closed world
  under their own source root, so rebuilt modules can reuse their names.
- **Code paths.** The CLI, tests, tools, benchmark and corpus checks, and the
  browser loaders read from the new root.
- **Serving.** The dev server maps `/archive/…` to the directory, and the
  Pages build copies it into the site. Proof pages say they show the archived
  library, with a link to the results catalog.
- **Checks.**
  - `npm test`: the archive checks 3,761 declarations and 43 templates, with
    none failed or blocked.
  - `npm run test:browser`, the landing test, and the site build with
    `npm run test:site` all pass.

**I0.3 Start the new library tree.** Create the rebuilt library's root,
proposed `library/`, served the same way as the archive.
- Its areas mirror `library-results.md`, starting with a placeholder module
  per area and the site's topic index.
- Layout rules: one theme per module, and no helper duplicated across
  modules.

**I0.4 Remove local scratch state.** Delete the unmerged `migration-curated`
branch and the scratch directories `.migration/` and `.catalog/`. The
curated pass's findings are recorded in the ergonomics handoff.

**L0.1 Non-computing dependencies, `computable`, `evaluate`.**
- Compute each declaration's non-computing dependencies from the checked
  dependency graph; show them in the inspector and CLI.
- Add the `computable` modifier and the `evaluate term expecting pattern;`
  directive.
- Add a CLI `evaluate` command with witness readout for truncations.
- Make the migration verifier compare non-computing dependencies.
- Acceptance: on the archive, the computed dependencies agree with today's
  assumption lists; negative tests name the dependency chain.

**D0.1 Checked-example harness.** Done on 2026-09-25 as
`tests/reference-examples.test.mjs`. It found that the reference documented
`unfold(term)`, which was removed with the cubical kernel; that passage now
describes conversion instead. A test extracts every code block from the
reference pages. It checks those marked `accept` and requires those marked
`reject` to fail with their stated message. Today's `data-check` markers are
inert, so every current example is unverified. Acceptance: all current
examples run under the harness, with failures fixed or removed.

**D0.2 Reference chapters.** Split `web/language.html` into chapters, each
with several checked examples per construct, including rejected ones:
1. first proof and file structure;
2. terms, functions and pairs;
3. proof blocks;
4. equality and paths;
5. rewriting and simplification;
6. cubical paths and composition;
7. conversion and unfolding;
8. assumptions and computability;
9. checking, inspection and the CLI;
10. errors.

The universe and induction chapters describe today's syntax and are marked
for rewrite in stages 1–2. The quick reference in `proof.html` becomes one
checked example per construct, each linking to its chapter.

## Stage 1: universes and the goal layer

| ID | Package | Owner | Depends on | Size |
| --- | --- | --- | --- | --- |
| K1.1 | G0 rule specification and consistency note | Kernel G0 | — | M |
| K1.2 | G0 in the reference checker | Kernel G0 | K1.1 | L |
| K1.3 | G0 in the C kernel, ABI, serialization, sanitizers | Kernel G0 | K1.2 | L |
| L1.1 | Universe binders, level expressions, removal of templates | Kernel G0 (language part) | K1.2 | L |
| L1.2 | Goal and proof-construction layer | HoTT A5 | — | L |
| L1.3 | Deterministic fuel; residual goals in diagnostics | HoTT A4, A6 | L1.2 for A6 | M |
| L1.4 | Folded path vocabulary; congruence through constructors | HoTT A1, A2 | L1.2 | L |

**K1.1–K1.3.**
- Implement level expressions, `Uω` as a binder type only, large types,
  capture-avoiding level substitution, and symbolic cumulativity.
- Acceptance is G0's list in the kernel roadmap: the native and reference
  checkers agree, and the canonicity fixture computes instantiated closed
  results.

**L1.1 Universe binders and levels.**
- `U : Universe` elaborates to a kernel binder.
- Source gains `next(U)` and `max(U, V)`.
- Specialization, per-universe builtins and per-universe assumption schemas
  are removed.
- The inspector shows level arguments.
- **Archive recheck:** every archive template is checked generically, and
  those that only worked at particular levels are listed.
- The universe chapter of the reference is rewritten.

**L1.2 Goal and proof-construction layer** (A5), with the review's elaborator
items:
- one name supply;
- result values instead of message matching;
- one computation of link sites;
- an explicit elaboration context;
- motive abstraction for several scrutinees, with dependent-hypothesis
  generalization, as `match` needs.

**L1.4 Path vocabulary and constructor congruence** (A1, A2). Include the
curated pass's findings:
- constructor descent, which H1 makes uniform;
- a statement-level `with unfolding`;
- beta-reduction after full-context `cong` rules.

## Stage 2: one-sort inductive signatures and the first language release

| ID | Package | Owner | Depends on | Size |
| --- | --- | --- | --- | --- |
| K2.1 | H specification and H1 soundness note | Kernel H1 | K1.1 | L |
| K2.2 | H1 in the reference checker | Kernel H1 | K1.2, K2.1 | XL |
| K2.3 | Differential oracle against the hand-coded rules | Kernel H1 | K2.2 | M |
| K2.4 | H1 in the C kernel; retire hand-coded rules after K2.3 | Kernel H1 | K1.3, K2.3 | XL |
| L2.1 | `inductive` declarations for one sort | Ergonomics 7 | K2.2 | L |
| L2.2 | `match`, recursion, path clauses, automatic clauses, obligations | Ergonomics 7 | L1.2, L2.1, L2.5 | XL |
| L2.3 | Derived declarations: `paths`, `decidable_equality`, `universal`, `ind_prop`, `rec` | Ergonomics 7 | L2.2 | L |
| L2.4 | Theories: models, homomorphisms, notation, sections, `extends` | Ergonomics 6 | L1.1 | L |
| L2.5 | h-level definitions and the first `hlevel` slice | HoTT D0a, D1 | L1.2 | M |
| L2.6 | `initial T` and `free T on A` with `fold` | Ergonomics 6 | L2.2, L2.4 | M |
| L2.7 | Canonical quotients, views and presentations | Ergonomics 7 | L2.2 | L |
| L2.8 | Squares and `cell` syntax | HoTT E2 | L2.1 | M |
| D2.1 | Reference chapters for the new language | Plan | L2.1–L2.7 | L |

**K2.2 H1 in the reference checker.**
- The signature normal-form checker: data, positions as cubes, dimensions,
  boundaries and positivity.
- Generated formation rules, constructors and boundary reductions.
- One formal composition per sort, with pushing through constructors.
- Transport along parameters with boundary correction.
- The eliminator, with clause typing through the partial eliminator, and its
  computation rules.
- The provisional `kernel extension: H1` marker.

**K2.3 Differential oracle.**
- Declare natural numbers, sums, W types and pushouts generically.
- Compare typing, reduction and composition with the hand-coded rules on
  the kernel tests and on the archive.
- Measure checking time.
- Acceptance: they agree, and any performance gap is recorded.

**Showcase acceptance for the stage:**
- a declared circle whose loop has winding number 1 by computation;
- `code_meridian` by `rfl`;
- `Trunc` and `Quotient` declared, with dependent eliminators;
- a canonical rational printed in lowest terms by `evaluate`.

**Theories** (L2.4, L2.6):
- ring lemmas take one `CommRing.Model`;
- `T.equality` follows once HoTT F1 lands;
- until then, identity is proved per theory by hand.

## Stage 3: rebuild wave 1

This wave starts once L2.2 and L2.4 have their first release. Each module
re-proves the hull and iconic results of its area in
[library-results.md](../library-results.md), in the new syntax, with
`computable` and `evaluate` where the results compute.

| ID | Area | Main results | Needs |
| --- | --- | --- | --- |
| B3.1 | Foundations | Path algebra; equivalences (D0b); h-levels; Hedberg; structure identity through theories; quotients and truncation as declarations; choice gives sections | L2.2–L2.5, HoTT D0b |
| B3.2 | Numbers | Nat; Euclid; integers (inductive, with presentations); binary and base-b numerals with transport by univalence | L2.2, L2.7 |
| B3.3 | Finite types and counting | Cardinality uniqueness; functions and permutations counted; binomial types; finite choice | B3.1, B3.2 |
| B3.4 | Order | Cantor–Schröder–Bernstein; Bourbaki–Witt; Zorn | B3.1 |
| B3.5 | Homotopy types | π₁(S¹) ≅ ℤ as groups; degree and no retraction; bouquets and punctures; the non-abelian twice-punctured plane | B3.1, B3.2, L2.8, HoTT F4 |
| B3.6 | Groups | Group theory; subgroup lattice; quotient groups; first isomorphism theorem; S₃ | B3.1, L2.4, L2.6 |

Tooling runs alongside this wave:
- HoTT B1 (`Path` induction), B3 (`ext` on Σ and the universe), C1–C3
  (conversion catalogue, transport rules, path algebra) and D2–D4, as the
  wave needs them;
- ergonomics milestone 5's holes, needed by stage 4.

Acceptance:
- every listed result is re-proved;
- nothing uses a non-computing dependency the archive's version did not
  need;
- winding numbers and numeral conversions pass `evaluate`;
- the site's topic pages switch from the archive to the rebuilt modules.

## Stage 4: indexed families, inference and rebuild wave 2

| ID | Package | Owner | Depends on | Size |
| --- | --- | --- | --- | --- |
| K4.1 | H2 soundness note: index-line matching and its stability, formal composition along indices | Kernel H2 | K2.1 | L |
| K4.2 | H2 in both checkers; `Id` with J on `refl` and its comparison with `Path` | Kernel H2, G3 | K2.4, K4.1 | L |
| L4.1 | Implicit binders, `_` holes, level inference | Ergonomics 5 | L1.2 | L |
| L4.2 | Dependent matching without K; coverage; impossible branches | Ergonomics 7 | K4.2, L2.3, L4.1 | L |
| L4.3 | Nested declarations | Ergonomics 7 | L2.1 | M |
| L4.4 | `apply` and `refine` | Ergonomics 5 | L4.1 | M |

**Rebuild wave 2:**

| ID | Area | Main results | Needs |
| --- | --- | --- | --- |
| B4.1 | Linear algebra | Vector spaces as a theory; every vector space has a basis; invariance of dimension; spanning families contain bases | B3.4 (Zorn), L2.4 |
| B4.2 | Polynomials | Integral domain; division; Bézout; principal ideals; roots bound; residue fields; adjoining roots | B3.2, B4.1 |
| B4.3 | Rationals | Canonical quotient; ordered field; Archimedean property (reals R1) | B3.2, L2.7 |
| B4.4 | Fields and Galois theory | F₂ and F₄; tower law; splitting fields; embedding counts; Dedekind–Artin; Artin; the fundamental theorem; Galois groups as loops | B4.1, B4.2, B3.6 |

The [Galois roadmap](galois-roadmap.md) resumes here. Its next items must be
restated against the rebuilt modules first.

Showcase acceptance: `Vec` and a typed-syntax evaluator are declared, and
`evaluate` runs the evaluator; `head` needs no `nil` branch.

## Stage 5: inductive-inductive types, reals and analysis

| ID | Package | Owner | Depends on | Size |
| --- | --- | --- | --- | --- |
| K5.1 | H3 soundness note | Kernel H3 | K4.1 | XL (new work) |
| K5.2 | H3 in both checkers | Kernel H3 | K4.2, K5.1 | XL |
| L5.1 | Companion sorts and functions; relations; bundles; theories with inductive-inductive initial models | Ergonomics 6–7 | K5.2, L2.6 | L |
| B5.1 | Cauchy reals: `initial CauchyStructure`, operations by fold, `CompleteOrderedField` model | Reals R2–R3 | L5.1, B4.3 | XL |
| B5.2 | Analysis: limits, complex numbers, integration along segments, periods | Reals R2; complex-analysis roadmap | B5.1 | XL |
| B5.3 | Syntax of type theory as `initial CwF`, with a computable interpreter | Showcase | L5.1 | L |

**Research gate at K5.1.** If the H3 soundness note does not converge, take
the reals roadmap's fallback: Dedekind reals (R4), which need only H1.
Analysis (B5.2) is written against the `CompleteOrderedField` theory, so it
does not change when the carrier does.

Showcase acceptance: `evaluate` reads a rational within 10⁻³ of √2 from a
closed real.

The complex-analysis roadmap resumes here, restated against the rebuilt
modules.

## Stage 6: on demand

- **H4**, several untruncated sorts: only when a concrete development needs
  it.
- **G4**, transport regularity for declared data types: when
  `transport_constant` corrections become a measurable cost.
- **G5**, certified interval normalization: when compact interval formulas
  block proofs.
- HoTT C4 and E1, E3, E4; HoTT F1 and F2 beyond what theories and
  presentations need.
- The RH roadmap, after stage 5.

## Documentation track, across stages

- The reference chapters (D0.2) are updated with each release:
  - universes after L1.1;
  - `inductive`, `match` and theories after stage 2 (D2.1);
  - indexed families after stage 4;
  - inductive-inductive types after stage 5.

  Every example is checked by the harness (D0.1). Rejected examples keep
  their expected messages.
- Each kernel stage adds a tactical handoff: the supported fragment, the
  soundness note, commands run, and the next obligation.
- `library-results.md` gains a column recording where each result lives in
  the rebuilt library, and when.

## First actions

Stage 0's housekeeping is settled:
- I0.1 is deferred, because work continues off `main` on
  `proof-ergonomics-roadmap`;
- I0.2 and I0.4 are done.

Next, in parallel:

1. L0.1, computability tracking.
2. D0.1, the reference harness, then D0.2, the reference chapters.
3. K1.1, the G0 specification.
4. L1.2, the goal layer.
5. I0.3, the new library tree, which is needed only when stage 3 starts.
