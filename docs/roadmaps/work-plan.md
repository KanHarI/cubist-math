# Work plan: language features and their kernel support

Status: reviewed against `fabb174` on 2026-09-27, after PRs #46–#48, and
revised the same day: K2.1 is the main track, learned-search phases 1–2 are
scheduled with L1.3, and L4.1a no longer gates explicit matching.
This is the scheduling authority for the linked roadmaps. Package IDs from
the earlier plan are retained; their stage numbers do not impose dependencies.
Sizes (S < M < L < XL) describe relative scope, not elapsed time.

**Current scope.** Advance the language, elaborator, tooling and the kernel
features they require. Use small checked programs and the archived library
as acceptance evidence. Broad library rebuilding, real/complex analysis,
Galois theory and RH are paused. Reaching a language milestone does not
resume those developments. Their old B-package IDs are retained in the
[deferred library backlog](#deferred-library-backlog).

**Governing requirement.** Computability is expressible and preserved.
Every applicable release extends the canonicity fixture; results with no
non-computing dependencies use `computable` and closed `evaluate` examples.
A new syntax form must elaborate completely through the instruction driver.

## Current status

| Area | Delivered | Still open |
| --- | --- | --- |
| Instruction kernel | Stages 1–5; every elaboration check is derived; K1.4's own conversion guide is the default; explicit driver options and cumulative kernel-work counters (learned-search phases 1–2) | Retiring the old checker APIs and their test clients; optional performance/certificate work |
| G0 universes | K1.1–K1.4 and L1.1; `U < UU0`, `next`, `max`, generic builtins and rewriting; all 43 former templates check generically | E1 level constraints and E2 higher-tier generic definitions remain deferred proposals |
| Proof ergonomics | Grouped binders, `have`, `rfl`, `calc`, `rw`, registered/conditional `simp` and `simpa`, cubical shorthand; Σ projections `p.1`/`p.2`, `show` and `suffices` (L1.5) | General inference, `apply`/`refine`, folded path rules, broader dependent rewriting, `Path` induction (B1) |
| Goal layer | L1.2/A5 core: `Goal`, `Transition`, one name supply, explicit scopes, shared reconstruction; multi-scrutinee motive abstraction | Face-aware plans, filling/source-span records, tactic integration, indexed and companion motives |
| Computability | L0.1: dependency tracking, `computable`, exact-value `evaluate`, CLI inspection | Expected-value patterns and closed truncation readout; H-stage dependency markers |
| Declarations | Existing built-in types and explicit eliminators | H1–H4, `theory`, user `inductive`, general `match`, views, derived declarations |
| Computation notation | Design only | N0–N5; no `do`/`proc` syntax or interfaces delivered |
| Reference and library | Checked-reference harness; universe chapter rewritten; `library/naturals`, `classical_axioms`, `universe_automorphisms` | Induction chapter rewrite and quick-reference expansion; these three modules are not completion of a rebuild wave |

Evidence lives in `tests/universe-generic.test.mjs`,
`tests/proof-ergonomics.test.mjs`, `tests/computability.test.mjs`,
`lib/cubical/tests/proof-goals.test.mjs`, `lib/cubical/tests/motives.test.mjs`,
`tests/reference-examples.test.mjs` and `tests/library.test.mjs`.
HoTT's gated probes still reject constructor descent and folded-path cases;
A1/A2 are not complete. The motive abstraction service has no source-level
`match` client yet.

The completed [G0 specification](historical/g0-universe-specification.md)
is kept in `historical/`; its rules remain the contract for later features.
The [historical index](historical/README.md) records the archival decision.
Other roadmaps still contain open work, including the instruction kernel's
cleanup and conditional stage 6.

## Overview

| Stage | Language outcome | Release gate |
| --- | --- | --- |
| 0 | Delivered baseline and reference | Preserve existing checks; finish independent documentation cleanup |
| 1 | Predictable goals, diagnostics and inference | Scoped holes resolve or report local errors; counted fuel and residual goals; CLI/browser agreement |
| 2 | One-sort declarations, basic theories and matching | Reviewed H1 rules, explicit and automatic clauses, checked theory records; differential and canonicity fixtures |
| 3 | Derived interfaces, views and proof automation | Supported structure identity/transfer fragments and closed computational examples |
| 4 | Indexed declarations | `Vec`, `Id`, impossible branches and a small typed evaluator; no axiom K |
| 5 | Inductive-inductive language | Reviewed H3 fragment and a small companion-sort interpreter |
| 6 | Optional extensions | A concrete use and a separate acceptance gate for each |

L4.1 inference is scheduled in stage 1 despite its retained ID. Core theories
can progress alongside H1: records need no new kernel rule. N1/N2/N4 need
neither initial models nor a rebuilt algebra library.

## The instruction kernel and this plan

The trusted checker is the [instruction kernel](kernel-instructions.md).
The untrusted driver is `web/cubical-instruction-driver.mjs`; its own guide
has been the default since K1.4. The old conversion oracle is comparison
only (`node tools/instruction-coverage.mjs --oracle`). The C term checker
and JavaScript reference checker are not extended to new language features.

Each kernel package adds instructions in `kernel/src/instructions.c`, their
computation rules and driver support. Acceptance includes:

1. Direct instruction acceptance/rejection cases in the C tests and source
   cases through the driver; malformed signatures and scope violations fail.
2. The archive checks and every stored definition derives again under
   `node tools/instruction-coverage.mjs` with the default guide.
3. Applicable canonicity computations pass, including formal compositions.
4. ABI, syntax encoding/decoding, inspection, checkpoint/rollback and cache
   invalidation cover new node and signature forms.

Ordinary source migrations retain strict public-type and assumption checks.
H1's replacement of primitive types needs an explicit representation map:
primitive syntax and generic signature applications are not automatically
convertible. K2.4 must specify comparison fixtures before retiring anything.
G2's deliberate universe/assumption changes have a separate reviewed ledger;
weakening the ordinary migration verifier is not an acceptance strategy.

**I1.2, optional checker retirement (M).** K1.4 removes the runtime dependency,
but deletion also requires migrating test-only clients and bridge exports.
Move the trusted alpha-equality, syntactic-cumulativity and pushout bridge
helpers out of the old checker files, preserve required syntax builders,
and check the remaining call graph before removing old APIs. This is not a
gate for H1, inference or theories. Native search, certificate compaction and
exported content hashes remain conditional stage-6 work.

## Stage 0: delivered baseline and remaining documentation

| ID | Package | Status / next obligation |
| --- | --- | --- |
| I0.1 | Merge the development branch into `main` | Deferred maintainer decision; work is on `proof-ergonomics-roadmap` |
| I0.2 | Archive the first library | Done: 367 sources in `archive/first-library/`; keep it as regression evidence |
| I0.3 | Start `library/` | Done: three modules listed above; broader topic coverage is deferred |
| I0.4 | Remove local scratch state | Recorded done on 2026-09-25 |
| L0.1 | Non-computing dependencies, `computable`, `evaluate` | Done; extensions have explicit L2.9 packages below |
| D0.1 | Checked-reference harness | Done: accept/reject examples, excerpts, CLI and REPL transcripts; sketches must be labelled |
| D0.2 | Reference chapters and quick reference | Chapter 5 done with G0; rewrite chapter 6 with H1. Quick reference done on 2026-09-27: `proof.html` gives each construct one checked example and a link to its chapter section; add an entry with each new construct |

The harness is active; `data-check` markers are not inert. Its acceptance
allows explicitly labelled fragments, so a passing harness does not claim
that every design sketch executes.

**I1.1, module resolution parity (S). Done on 2026-09-27.** One contract,
`web/module-resolution.mjs`, resolves imports for the CLI, the test runner,
the library, REPL and reference tests and the browser worker. Each module
resolves its imports by where it lives: an archive module only in the archive,
so checking it is archive-isolated; a library module in `library/`, then the
archive; a checked file outside both roots in its own directory, then the
library, then the archive; a REPL entry or reference example library-first.
A check holds one module per name, and a clash fails on the later importer.
Before, `tools/test-selection.mjs` resolved selected-proof imports only from
the archive. `tests/module-resolution.test.mjs` covers same-name modules,
local imports, source-root selection and CLI/test-runner parity.

**I1.3, coverage acceptance reporting (S). Done on 2026-09-27.**
`node tools/instruction-coverage.mjs` succeeds only when every import
checks, no gap remains and every stored definition derives again
(`derived === definitions`, with at least one); otherwise it prints
"Coverage incomplete" and exits with status 1. It no longer reads
`CubicalProgram.complete`, which is false for an import-only root. The
report also pins the revision, machine, budgets and session mode, and gives
the kernel work of each phase (learned-search phases 1–2).

## Stage 1: goals, diagnostics and inference

G0 (K1.1–K1.4, L1.1) is complete. Its source acceptance cases and level
property tests remain regressions, not next actions.

| ID | Package | Depends on | Size |
| --- | --- | --- | --- |
| L1.2 | A5 core goal and proof-construction layer | Delivered | — |
| L1.2r | Remaining A5 plan metadata and clients: faces, filling, source spans; index/companion motives with H2/H3 | Extend the delivered core with each consuming feature | L |
| L1.3 | Deterministic fuel and residual-goal diagnostics (HoTT A4/A6), on learned-search phases 1–2. Delivered 2026-09-27; worker cancellation remains | L1.2; A7 baseline | M |
| L1.4 | Folded path vocabulary and constructor congruence (A1/A2) | L1.1, L1.2; A4 fuel for bounded search | L |
| L1.5 | Σ projections `p.1`/`p.2`, `show`, `suffices` (A8/B4): delivered 2026-09-27. Open: the separate `Path` induction/`subst` slice (B1) | L1.2; B1 uses A1b's checked induction construction | M |
| L4.1a | Known-signature application elaboration, named arguments and scoped `_` holes | L1.1, L1.2; L1.3 fuel for inference search | M |
| L4.1b | Opt-in implicit binders and level-argument inference | L4.1a | M |
| L4.4 | `apply`, `refine`, pair/sum witness conveniences with visible goals | L4.1a; L4.1b for implicit arguments | M |
| L2.5a | Checked h-level definitions (HoTT D0a) | L1.1; small foundation module | S |
| L2.5b | First `hlevel` solver slice (HoTT D1) | L2.5a, L1.2, L1.3 fuel | M |

L4.1a/b together retain the old L4.1 scope; L2.5a/b retain L2.5.
Inference is not blocked by H2. L4.1a improves the first general `match`
release without gating it: explicit matching accepts explicit motives and
arguments. Implicit indices are required for the indexed release. Decide only
constraints determined by supplied arguments and expected types; E1's
user-declared level constraints remain deferred. Every implicit argument
has an explicit spelling.

**Acceptance details:**

- Application spines use known signatures rather than repeated whole-spine
  inference. Metavariables have scope, occurs checks and deterministic
  solutions; ambiguous levels, escaping dimensions and unresolved holes
  fail before kernel admission. The inspector shows inferred arguments.
- Fuel counts traversal, candidates, failed attempts, reconstruction,
  native queries and retries. Specify cache/reset accounting so fresh and
  reused sessions agree. Deadlines remain separately reported safety
  timeouts. Done (L1.3): searches and declarations spend counted fuel
  (`lib/cubical/fuel.mjs`), which counts questions rather than the kernel's
  steps, so warm caches change nothing; a query's growing step budget is
  capped and restored after it; the defaults are recorded with their
  measurement in `tests/fixtures/search-fuel.json`. The kernel-work counters
  (`cc_kernel_work`) measure the steps behind the questions. Decided on
  2026-09-27: the kernel's step budget is a safety limit outside the
  determinism guarantee, like the deadline, since near its cap a query can
  pass warm and fail cold. Deferred: capping the driver's speculative
  normalization, whose failed attempts took 47% of re-derivation steps in
  the #52 measurement. Measure a lower cap with the coverage telemetry
  before changing the driver.
- A1 uses level-generic checked definitions. Reintroducing per-universe
  specialization would undo L1.1. A2 initially excludes binder bodies;
  binder-aware rewriting remains a separately scoped extension.
- B1 is derived cubical `Path` induction. It must not promise judgmental
  computation for arbitrary neutral motives; H2's `Id`/J has its own gate.
- Finish each A5 remainder when its client needs it. Basic projections,
  `show` and `suffices` do not wait for all indexed or companion motives.

## Stage 2: one-sort signatures, basic theories and matching

| ID | Package | Depends on | Size |
| --- | --- | --- | --- |
| K2.1 | Precise H1 signature fragment and soundness note; review gates release. Drafted in the [H1 specification](h1-signature-specification.md); every question decided and the specification approved on 2026-09-27. K2.2 is open, behind the experimental gate, on the `h1-signatures` branch. Default admission and release wait for the open proofs D1, D4, D5 and Lemma H2 | G0 specification | L |
| K2.2 | H1 instructions: signature admission, constructors, composition, eliminators and steps, as the six families F1–F6 of the specification's section 5, each reviewed and merged into `h1-signatures` separately. All six families are implemented, with ABI version 3: F1 (admission), F2 (instances and constructors), F3 (boundary reduction), F4 (Kan structure), F5 (elimination) and F6 (the extension gate). K2.3 (the driver) follows | K1.2, K2.1 | XL |
| K2.3 | H1 driver, bridges, signature serialization and generated-rule derivation. In progress on `h1-signatures`: admission from a normal form, the syntax codec and renderers, and the driver's derivations and search for instances, constructors and eliminators; the `kernel extension: H1` marker, with L2.1; import invalidation, by construction; signatures in the CLI's `inspect`. Open: the workbench inspector and clause types, with L2.2a | K1.3, K2.2 | L |
| K2.4 | Differential fixtures for native and declared Nat/sum/W/pushout; then retirement | K2.3; explicit representation/comparison contract | M |
| K2.5 | G2 truncation/resizing policy and migration ledger. Policy and measured ledger in the [H1 specification](h1-signature-specification.md#8-k25-truncation-and-resizing-g2); no resizing assumption (Q12) and the 8.4 remedy groups (Q17) decided, and the policy approved, on 2026-09-27 | K2.1; implementation with K2.3/L2.1 | M |
| L2.1 | One-sort `inductive` declarations and signature diagnostics. Implemented behind the experimental option `h1`: the header's result position, lowering with data before positions, universe classification and the least level, uses of the type and its constructors, precise refusals. Open: the reference chapter (D2.1), `T.squash` as a name | K2.3 | L |
| L2.2a | Explicit `match`, motives, structural recursion and path clauses. First slice implemented behind `h1`: the expression `match v [as z] [return T] { c(xs) i => … }`, each clause checked against the kernel's clause type; dependent motives; path clauses and hand-written squash clauses with `T.squash`; recursion on a constructor's argument with the other arguments fixed. The H1 winding-number fixture computes in source. Open: `match` as a proof statement with goal-derived motives (A5), recursion whose other arguments vary, and the `cases` migration | L2.1, L1.2; relevant L1.2r metadata; L4.1a improves the release without gating it | L |
| L2.2b | Automatic clauses and explicit `obligations` | L2.2a, L2.5b; checked h-level evidence | M |
| L2.3 | Supported `deriving`: `paths`, `decidable_equality`, `irrelevance`, `ind_prop`, `rec`; `universal` slice | L2.2; `universal` also uses L2.4/L2.6 | L |
| L2.4 | Core theories: named model records, explicit homomorphisms/isomorphisms, scoped notation, sections, `extends` | L1.1, L1.5 projections, L2.5a for h-level fields | L |
| L2.6 | Single-sort `initial T`, `free T on A`, `fold`, checked uniqueness/universal interface | L2.2, L2.4; H1-admissible signature | M |
| L2.8 | Squares and `cell` face syntax with boundary inspection (HoTT E2) | L2.1; face/source metadata from L1.2r | M |
| L2.9a | Expected-value patterns for `evaluate` | L0.1; own pattern contract and L4.1a infrastructure | S |
| L2.9b | Closed truncation witness readout | Native H1 `Trunc`, K2.5, L0.1 | M |
| D2.1 | Checked reference, formatter and inspection for each released construct | Corresponding package, including L2.8/L2.9 | L |

L2.2 means both slices when another package needs automatic clauses.
Explicit matching can land before automatic clause search. The theories
release accepts explicit fields and arguments; L4.1b improves its notation
without making records depend on H1. Generated `T.equality` and richer
`T.Displayed`/coherence support have separate gates in stage 3.

**Specify before implementing H1:** the admitted grammar and positivity,
constructor ordering, substitution under levels and dimensions, overlaps,
formal composition, parameter transport and dependent eliminator clauses.
Split K2.2/K2.3 into reviewable instruction families with rejection tests,
then demonstrate their integration. The specified fragment precedes the
implementation; experiments and fixtures may precede review in an explicitly
enabled experimental mode. Default admission and release require the reviewed
soundness note. While review is pending, experimental results carry
`kernel extension: H1`; test its transitive provenance separately from
non-computing assumptions. A design sketch is not a reviewed soundness note.

Universe fixtures cover phantom parameters, stored data, arities, indices
and quotient relations: parameters contribute only through those types.
Reject lowering and mismatched level instances; preserve G0's distinction
between a sort's universe and its parameter telescope's universe.

**K2.5/G2.** Native `Trunc(U, A) : U` preserves the universe. The archive's
`Truncate : U -> U0` has resizing and is not a drop-in replacement. Keep
legacy assumptions available to archive checks until each intentional
migration is justified. Record changed public universes, removed assumptions
and affected consumers; do not add resizing to the rebuilt foundation.
The ordinary migration check stays strict for unrelated changes.

**Release fixtures:** declared Nat/list, W and pushout comparisons;
a circle with computed winding number 1 and `code_meridian` by `rfl`;
`Trunc` and set quotient with checked dependent elimination; a tiny theory
whose law and homomorphism preservation are checked; and rejected bad
boundaries, nonstructural recursion, missing clauses and missing h-level
proofs. These fixtures need only their small foundation dependencies.
A canonical rational is a later library example, not the H1 gate.

`evaluate` patterns require a specified matching language and clear mismatch
messages; they do not inherently require H1. Truncation readout does require
native truncation and is a closed evaluation tool, not a source eliminator
`Trunc(A) -> A`.

After general `match` is released, migrate the archive's `cases` uses under
the strict verifier before removing that statement from parser, formatter,
highlighter and reference. Legacy explicit eliminators remain parseable.

## Stage 3: derived interfaces, views and automation

These packages provide the language's small checked foundation. They do not
require rebuilding whole mathematical areas.

| ID | Package | Depends on | Size |
| --- | --- | --- | --- |
| L3.1 | Canonical equivalence interface (HoTT D0b) | G0; existing checked equivalence constructions | M |
| L3.2 | Σ/universe `ext`, property-field closure, contractibility combinators (B3/D2/D4 slices) | L1.2, L2.5, L3.1 as required by each slice | L |
| L2.4b | Theory identity and displayed/coherence interfaces for an explicit supported grammar (HoTT F1) | L2.4, L3.1, L3.2; D3 only for identity-system registration | L |
| L3.3 | Minimum checked transfer maps for views/presentations (HoTT F2) | L3.1; C2 for paths built through `ua` | M |
| L2.7 | Checked eliminator views, canonical quotients, presentations | L2.2, L3.1/L3.3 for equivalence-based views; L2.5 for setness | L |

L2.3 and L2.4b must state which signatures they support and report obligations
for the rest. A law field is not automatically proof irrelevant. Setness
cannot rely circularly on a squash clause whose omission it is meant to
justify. Test nonidentity carrier equivalences and reject incorrect operation
preservation. Full higher coherence and unrestricted derivation remain open.

Use small finite normal-form and product-swap examples for L2.7, with closed
computations and rejected wrong maps. Arbitrary binder rewriting, general
transfer automation, algebraic normalization, expected-type completion and
lemma suggestions remain explicitly deferred; none is silently included in
the core theories release.

## Stage 4: indexed families

| ID | Package | Depends on | Size |
| --- | --- | --- | --- |
| K4.1 | H2 soundness note: index-line matching and stability under faces | K2.1; H1 computation contract | L |
| K4.2 | H2 instructions/driver, formal composition along indices, `Id` and J | K2.3, K4.1 | L |
| L4.2 | Dependent matching without K, coverage, impossible branches | K4.2, L2.3's path-characterization slice, L4.1a/b; indexed L1.2r motives | L |
| L4.3 | Nested declarations: specify an admissible lowering first | H3/H4 if lowering introduces companion sorts; an H1 subset needs its own one-sort translation | M |

Acceptance: `Vec`, `Fin`, `Id`, vector append and a small typed-syntax
evaluator are declared; `J` on `refl` computes, and `head` needs no `nil`
branch. Reflexive index equations can be erased only with the required
setness proof. Distinguish this from derived `Path` induction.

L4.3 formerly depended only on L2.1. That was insufficient: the proposed
translation creates mutual declarations, beyond H1's one-sort fragment.
No general nested-declaration release is promised at H2.

## Stage 5: inductive-inductive language

| ID | Package | Depends on | Size |
| --- | --- | --- | --- |
| K5.1 | H3 soundness note, including induction-induction and partial eliminators | K4.1; stabilized H1/H2 rules | XL |
| K5.2 | H3 instructions, driver and declared set/prop companion sorts | K4.2, K5.1 | XL |
| L5.1 | Companion functions/motives, relations, bundles, inductive-inductive initial models | K5.2, L2.6; companion L1.2r motives | L |

H3 is a research gate. First specify a small context/type signature and a
computable interpreter that exercise genuine dependent companion sorts and
joint elimination; ordinary mutual data alone do not test H3. This replaces
the active requirement to build Cauchy reals and extract an approximation to
√2. The reals example remains deferred mathematical acceptance, not evidence
already supplied by a syntax fixture. If H3's note does not converge, H1/H2
language releases remain useful and continue independently.

## Stage 6: on demand

- H4: several sorts with untruncated sorts, only with a concrete use.
- G4 transport regularity; G5 certified interval normalization, when measured
  proof costs justify them.
- HoTT C4/E1/E3/E4, fuller identity systems, binder-aware rewriting, transfer
  automation and theory morphisms, each with an explicit fragment and gate.
- E1/E2 universe enhancements remain in their proposal document.
- Learned-search phases 3–5 and native search/certificate work are optional.
  Phases 1–2, the driver's explicit options and measured per-instruction
  cost, are scheduled with L1.3 in stage 1; that baseline must include
  failed queries, model overhead and session/cache effects. Training waits
  for it.

## Computation notation track

The [computation roadmap](computation-notation-roadmap.md) owns N0–N5.
The exact syntax remains proposed; none is delivered.

- **N0:** explicit baselines can start now. Preserve archived span closure as
  evidence; use identity/function/static-option fixtures for language work.
- **N1:** checked operations and law records after G0 and L2.4's core record
  slice. No initial model or generated structure identity is required.
- **N2 and N4:** monadic `do` and basic `proc` after N1, the goal layer and
  L4.1a/b. They proceed independently; full mathematical instances do not
  gate the first notation releases.
- **N3a:** exhaustive patterns after N2 and the relevant matching service.
  Small pair/sum fixtures prove scope, rejection of refutable binds and
  absence of witness escape.
- **N3b:** native truncation and free-algebra examples after H1/L2.6; rebuilt
  span closure only when library development is resumed. These are separate
  instance gates, not prerequisites for N3a or N4.
- **N5:** explicit choice and dynamic application after N4 and checked
  capability laws. Probability and partiality instances remain deferred.

## Release checks and documentation

Every language package includes parser/formatter round trips, original source
spans, generated-term inspection, native acceptance/rejection, and browser/CLI
agreement. Transactions discard failed generated declarations, rules and
signature registrations; import changes invalidate affected caches. Complete
terms contain no unresolved goals or metavariables.

Use the existing canonicity and false-equality fixtures, archive coverage and
strict migration checks as applicable. Kernel/ABI changes also require native
tests and sanitizers. Performance comparisons record revision, workload,
limits, total checking time, kernel work and memory; historical timings are
observations, not current guarantees. Fuel defaults come from the post-G0
baseline in `tests/fixtures/search-fuel.json`; rerun
`node tools/search-fuel-baseline.mjs --write` when workloads change. The A7
baseline's specialization-cost fields no longer describe the runtime.

D0.2 and D2.1 advance with their features, including indexed/companion syntax.
Update the reference, roadmap status, index and tactical checkpoint together.
A roadmap moves to `historical/` only when its scope is complete; a completed
milestone does not retire a document with open work. Update incoming and
outgoing links when moving it. Specifications remain linked where normative.

## Deferred library backlog

The [results catalog](../library-results.md) and mathematical roadmaps retain
the long-term targets. These packages are not active dependencies or language
release gates:

| Retained IDs | Deferred work |
| --- | --- |
| B3.1–B3.6 | Full foundations, numbers, finite counting, order, homotopy types and groups rebuild |
| B4.1–B4.4 | Linear algebra, polynomials, rationals, fields and Galois rebuild |
| B5.1–B5.2 | Cauchy/Dedekind reals and analysis |
| B5.3 | Full `initial CwF` development and interpreter; L5.1 instead requires a smaller H3 fixture first |
| Later mathematical roadmaps | Complex analysis, Galois continuation and RH; no automatic resumption |

Small h-level/equivalence definitions and language acceptance fixtures are
part of their owning language packages. They do not commit to proving all
results from the corresponding library area.

## Planning corrections in this review

- Refresh completed G0, computability, goal-core and reference status; keep
  partial features distinct from delivered ones.
- Move holes/inference before their matching and notation clients; make
  fuel, projections and h-level dependencies explicit.
- Separate core theories from F1 identity, explicit matching from automatic
  clauses, and notation patterns from large mathematical instances.
- Schedule G2 policy, H1 representation comparison, minimum view/transfer
  support, `irrelevance`, `evaluate` extensions, module-resolution parity
  and a reliable coverage-command exit status.
- Remove unsupported H1 mutual-type assumptions from nested declarations.
- Replace mathematical rebuild gates with small language fixtures, preserving
  the paused mathematical backlog and H3's research gate.
- Same-day revision: name K2.1 as the main track; schedule learned-search
  phases 1–2 with L1.3, since deterministic fuel and per-instruction cost
  are one accounting; make L4.1a an input to explicit matching rather than
  its gate, because every implicit argument has an explicit spelling.

## First actions

1. **Main track: K2.1**, the H1 signature fragment and soundness note, with
   K2.5's truncation and resizing policy. It depends on nothing open and
   gates K2.2, the largest package in the plan.
2. Alongside: L1.3 deterministic budgets and diagnostics together with
   learned-search phases 1–2, which share its cost accounting; and L1.5,
   the small goal conveniences.
3. Between those, the small items: the quick reference (D0.2),
   module-resolution parity (I1.1) and coverage reporting (I1.3). Rebaseline
   current generic declarations for fuel accounting.
4. Build L4.1a, then L4.1b/L4.4; start L2.5a/b and core theories (L2.4) as
   their projection/fuel prerequisites land.
5. Implement H1 instruction families and driver support, explicit matching,
   then automatic clauses and their canonicity/differential acceptance.
6. Advance N0/N1, then N2/N4 alongside derived declarations and views. H2
   follows H1's stable rules; H3 waits for its reviewed research result.

Checker retirement and learned-search phases 3–5 may proceed separately;
neither blocks this language sequence. Concrete mathematical development
remains paused.
