# Work plan: language features and their kernel support

Status: reviewed against `02a57ef` (PR #71 on `h1-signatures`) on
2026-09-28 by the [work-plan audit](audits/2026-09-28-audit.md), and revised
the same day; the previous review was against `fabb174` on 2026-09-27.
This is the scheduling authority for the linked roadmaps. Package IDs from
the earlier plan are retained; their stage numbers do not impose dependencies.
Sizes (S < M < L < XL) describe relative scope, not elapsed time.

Rows record one of five statuses. **Implemented**: delivered and on by
default. **Experimental**: implemented behind the `h1` option, with results
carrying `kernel extension: H1`; not approved for default admission.
**Review pending**: a semantic obligation that implementation and passing
tests do not discharge. **Migration pending**: specified tooling or
migrations not yet built. **Deferred**: not scheduled.

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

The cells name packages; each package's row below holds its details and
status, so a status changes there, and here only when a package moves
between columns.

| Area | Delivered | Still open |
| --- | --- | --- |
| Instruction kernel | Stages 1–5; every elaboration check is derived; K1.4's own conversion guide is the default; explicit driver options and cumulative kernel-work counters (learned-search phases 1–2); I1.2a, instruction isolation: no untrusted query can change an instruction's verdict | I1.2b, the optional retirement, after the call-graph audit I1.2a recorded; stage-6 performance and certificate work |
| G0 universes | K1.1–K1.4 and L1.1; `U < UU0`, `next`, `max`, generic builtins and rewriting; all 43 former templates check generically | E1 and E2, deferred proposals |
| Proof ergonomics | Grouped binders, `have`, `rfl`, `calc`, `rw`, registered/conditional `simp` and `simpa`, cubical shorthand; Σ projections `p.1`/`p.2`, `show` and `suffices` (L1.5); path-operator notation (`-i`, `&`, `\ | L4.1a/b and L4.4 (inference, `apply`/`refine`), L1.4 (folded path rules, constructor descent), B1 (`Path` induction), broader dependent rewriting |
| Goal layer | L1.2/A5 core: `Goal`, `Transition`, one name supply, explicit scopes, shared reconstruction; multi-scrutinee motive abstraction | L1.2r |
| Computability | L0.1: dependency tracking, `computable`, exact-value `evaluate`, CLI inspection; the `kernel extension: H1` marker (experimental), tracked apart from assumptions, listed by `inspect`, the CLI and the workbench, and compared by the migration verifier | L2.9a, L2.9b |
| Declarations | Built-in types and explicit eliminators. **Experimental:** K2.2, K2.3, L2.1 and L2.2a's first slice; the circle's winding number computes in source | **Review pending:** K2.1. **Migration pending:** K2.4a, K2.5. Open: L2.2a's remainder, L2.2b, L2.3, L2.3b, L2.4, L2.6–L2.9, stages 4 and 5 |
| Computation notation | Design only | N0–N5 |
| Reference and library | Checked-reference harness; universe chapter rewritten; quick reference (`proof.html`); `library/naturals`, `classical_axioms`, `universe_automorphisms`, `hlevels` (L2.5a) | The induction chapter and an H1 chapter (D0.2, D2.1); the four modules do not complete a rebuild wave |

Evidence lives in `tests/universe-generic.test.mjs`,
`tests/proof-ergonomics.test.mjs`, `tests/computability.test.mjs`,
`lib/cubical/tests/proof-goals.test.mjs`, `lib/cubical/tests/motives.test.mjs`,
`tests/reference-examples.test.mjs` and `tests/library.test.mjs`; for H1,
in `kernel/tests/test_signatures.c`, `tests/h1-admission.test.mjs`,
`tests/h1-driver.test.mjs`, `tests/inductive-declarations.test.mjs`,
`tests/declared-match.test.mjs` and `tests/inductive-repl.test.mjs`.
HoTT's gated probes still reject constructor descent and folded-path cases;
A1/A2 are not complete. The motive abstraction service has no source-level
`match` client yet: `lib/cubical/match.mjs` builds its own explicit or
expected motive.

**Baseline at `02a57ef`** (the audit's section 5, one machine's
observations): `make test` and the focused H1 suite pass; the archive
coverage command reports 365 modules, 3,804 of 3,804 declarations checked
with no gap and 3,916 of 3,916 definitions re-derived, at 5,524,209
checking and 2,012,235 re-derivation instructions. That is archive
compatibility evidence, not the declared-type comparison (X4) and not a
proof of H1's soundness. CI runs only for PRs into `main`, so integration
into `h1-signatures` is recorded by a manual run against a pinned revision.

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

Stage 2's gate is not passed at `02a57ef`: its rules are implemented
experimentally, their review is pending, and the differential fixtures do
not exist. L4.1 inference is scheduled in stage 1 despite its retained ID.
Core theories can progress alongside H1: records need no new kernel rule.
N1/N2/N4 need neither initial models nor a rebuilt algebra library.

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

**I1.2a, instruction isolation (M). Done on 2026-09-28.** The audit of
that day (finding 1) found the separation from the old conversion checker
incomplete in two places: the reducers behind `Step(Whnf)` and
`Step(Normalize)` decided pair and Glue eta with `ck_convertible`, and a
conversion success entered the memo table that the folded comparison read,
so a public `cc_kernel_convertible` query could satisfy a later
instruction's syntactic side condition. The correction keeps the folded
result and conversion's success as separate facts in each memo entry,
decides both eta rules in reduction by syntax, gives conversion its own
pair and Glue eta, and makes `ck_convertible` refuse to run inside an
instruction.
`kernel/tests/test_isolation.c` covers each part, including the audit's
probe, and reverting any part fails it. A static call graph finds no path
from an instruction to the conversion search or the typing rules. Archive
coverage stays complete with the driver's guide, at essentially unchanged
work, and with the conversion oracle, at about 1% more kernel steps, since
side conditions the leaky memo answered are now derived. The
[kernel instructions](kernel-instructions.md#what-remains-of-the-term-checker)
record the boundary, the evidence and the measurements.

**I1.2b, optional checker retirement (M).** K1.4 removes the runtime
dependency, but deletion also requires migrating test-only clients and
bridge exports. Move the trusted helpers out of the old checker files,
preserve required syntax builders, and remove old APIs only after the
call graph I1.2a recorded is rechecked: the folded comparison shares its
function with the conversion modes, and its level, formula and scope
helpers move with it. Native search,
certificate compaction and exported content hashes remain conditional
stage-6 work.

## Stage 0: delivered baseline and remaining documentation

| ID | Package | Status / next obligation |
| --- | --- | --- |
| I0.1 | Merge the development branch into `main` | Deferred maintainer decision; work is on `h1-signatures`, whose CI runs only through PRs into `main` |
| I0.2 | Archive the first library | Done: 367 sources in `archive/first-library/`; keep it as regression evidence |
| I0.3 | Start `library/` | Done: the modules listed above; broader topic coverage is deferred |
| I0.4 | Remove local scratch state | Recorded done on 2026-09-25 |
| L0.1 | Non-computing dependencies, `computable`, `evaluate` | Done; extensions have explicit L2.9 packages below |
| D0.1 | Checked-reference harness | Done: accept/reject examples, excerpts, CLI and REPL transcripts; sketches must be labelled |
| D0.2 | Reference chapters and quick reference | Chapter 5 done with G0; chapter 6 and an H1 chapter wait for D2.1, since `docs/examples/h1/winding.cubist` is a checked example and not a chapter. Quick reference done on 2026-09-27: `proof.html` gives each construct one checked example and a link to its chapter section; add an entry with each new construct, `inductive` and `match` included once they leave the experimental option |

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
| L1.2r | Remaining A5 plan metadata and clients: faces, filling, source spans; the source `match` client of the motive service (with L2.2a); indexed motives with L4.2 and companion motives with L5.1, neither of which gates H1's explicit `match` | Extend the delivered core with each consuming feature | L |
| L1.3 | Deterministic fuel and residual-goal diagnostics (HoTT A4/A6), on learned-search phases 1–2. Delivered 2026-09-27; worker cancellation remains | L1.2; A7 baseline | M |
| L1.4 | Folded path vocabulary and constructor congruence (A1/A2) | L1.1, L1.2; A4 fuel for bounded search | L |
| L1.5 | Σ projections `p.1`/`p.2`, `show`, `suffices` (A8/B4): delivered 2026-09-27. Open: the separate `Path` induction/`subst` slice (B1) | L1.2; B1 uses A1b's checked induction construction | M |
| L4.1a | Known-signature application elaboration, named arguments and scoped `_` holes | L1.1, L1.2; L1.3 fuel for inference search | M |
| L4.1b | Opt-in implicit binders and level-argument inference | L4.1a | M |
| L4.4 | `apply`, `refine`, pair/sum witness conveniences with visible goals | L4.1a; L4.1b for implicit arguments | M |
| L2.5a | Checked h-level definitions (HoTT D0a). **Done** on 2026-09-29: `library/hlevels.cubist` defines `IsContr`, `IsProp`, `HasLevel` by recursion on `Nat` and `IsSet` as its level 1, in every universe below `UU0`. It proves contractible types propositions, propositions sets, levels cumulative, having a level a proposition, being contractible a proposition, closure under retracts, Π, Σ, products, subtypes and path types at every level, closure of contractible types under the same constructions but subtypes, which can be empty (`exists x : Unit. Void` is not contractible), and Hedberg's theorem, with `Nat` a set. An equivalence's inverse makes a retract; the statement for the public `Equiv` type waits for D0b | L1.1; small foundation module | S |
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
| K2.1 | Precise H1 signature fragment and soundness note; review gates release. Specified in the [H1 specification](h1-signature-specification.md): every question decided and the specification approved for experimental implementation on 2026-09-27. **Review pending:** the proofs D1, D4, D5 and Lemma H2, the critical-pair check of its 3.7, and canonicity relative to the assumed baseline (its 4.5). Their evidence, and what each decision still needs, is in the [review evidence](h1-review-evidence.md) (2026-09-29). The release checklist in its header covers the finite-level fragment only; the classification walk of its 2.3 belongs to the deferred tier-parametric proposal, not to this gate (audit finding 2) | G0 specification | L |
| K2.2 | H1 instructions, the six families F1–F6 of the specification's section 5. **Experimental:** all six implemented with ABI version 3, each reviewed and merged into `h1-signatures` separately. Open: the acceptance matrix's randomized K10/K11 property tests, K1 with tubes and K6 along `ua` (the specification's 10.10, which `tests/acceptance-matrix.test.mjs` checks against the tests), and a review record per family for its semantic obligations; passing tests do not discharge them | K1.2, K2.1 | XL |
| K2.3 | H1 driver, bridges, signature serialization and generated-rule derivation. **Experimental:** admission from a normal form, the codec and renderers, derivations and search for instances, constructors and eliminators, rollback and commit, the `kernel extension: H1` marker (with L2.1), import invalidation by construction, signatures in the CLI's `inspect`, and clause types, which L2.2a's `match` consumes (`lib/cubical/match.mjs`). Since 2026-09-28 the CLI's `inspect` and the workbench's inspector show a declared type's signature and its eliminator's clause types, and the migration verifier compares the marker apart from assumptions (the specification's 6.4, 6.5). The acceptance matrix traces every case of 10.10 but K1 with tubes, K6 along `ua`, and those that wait for another package or a randomized generator; each traced case is named by its ID in its test, and `tests/acceptance-matrix.test.mjs` checks the matrix against the tests. The whole suite ran at a pinned revision on 2026-09-28: CI run 36472206548 at `bef00e3`, all seven jobs passed. A release repeats that run at its own revision | K1.3, K2.2 | L |
| K2.4a | Differential fixtures X1–X8 of the specification's 7.3 and their tooling: the translation τ as a driver option, the verifier's report of a mixed-tier call (X8), X5's cost record, and the verifier's comparison of a module that declares a type, whose edited copy has another, generative signature. **Migration pending:** none exists at `02a57ef`; the archive coverage run is not X4 | K2.3; the representation map of the specification's section 7 | M |
| K2.4b | Retire the `Nat` instructions only, by the criterion of the specification's 7.4 (Q16): X1–X4 and X6–X8 pass, X5 is recorded, and the archive is migrated by τ under the strict verifier. Sum, W and pushout stay trusted for tier-1 arguments, with X1–X3, X7, X8 and their native tests as regressions | K2.4a | M |
| K2.4c | Wider retirement of the sum, W and pushout instructions. **Deferred** with the tier-parametric proposal (Q16). At the source boundary a mixed-tier program has no image under τ: the verifier reports it, and nothing is migrated in part | The tier-parametric proposal, adopted and reviewed | M |
| K2.5 | G2 truncation/resizing policy and migration ledger. Policy and measured ledger in the [H1 specification](h1-signature-specification.md#8-k25-truncation-and-resizing-g2); no resizing assumption (Q12) and the 8.4 remedy groups (Q17) decided, and the policy approved, on 2026-09-27. **Migration pending:** the ledger file and verifier of its 8.5 (fixture G4) and each migration (G2, G5–G7); the two H2-dependent tower declarations stay deferred, so removing every legacy truncation assumption is not an H1 prerequisite | K2.1; implementation with K2.3/L2.1 | M |
| L2.1 | One-sort `inductive` declarations and signature diagnostics. **Experimental:** the header's result position, lowering with data before positions, universe classification and the least level, uses of the type and its constructors, precise refusals. Open: the reference chapter (D2.1). Excluded by the specification: a composite boundary such as `Torus2`'s `trans(p, q) = trans(q, p)` (its 1.4, Q3; the square torus is admitted), and proof-first `: set`/`: prop`, which is L2.3b | K2.3 | L |
| L2.2a | Explicit `match`, motives, structural recursion and path clauses. **Experimental, first slice:** the expression `match v [as z] [return T] { c(xs) i => … }`, each clause checked against the kernel's clause type; dependent motives; path clauses and hand-written squash clauses with `T.squash`; recursion on a constructor's argument with the other arguments fixed, in a definition whose whole body is the match, where the matched parameter stands for the clause's constructor. The H1 winding-number fixture computes in source. Open: `match` as a proof statement with goal-derived motives through the A5 motive service, which the match does not use yet; recursion whose other arguments vary, with explicit acceptance cases; broader pattern coverage; and the `cases` migration, with `cases` retained until its gate passes | L2.1, L1.2; relevant L1.2r metadata; L4.1a improves the release without gating it | L |
| L2.2b | Automatic clauses and explicit `obligations`. The h-level solver gates this package only: explicit squash clauses work without it (audit finding 5) | L2.2a, L2.5b; checked h-level evidence | M |
| L2.3 | Supported `deriving`: `paths`, `decidable_equality`, `irrelevance`, `ind_prop`, `rec`; `universal` slice, once L2.6's contract is specified | L2.2; `universal` also uses L2.4/L2.6 | L |
| L2.3b | Proof-first h-levels: `: set` and `: prop` proved from the generated path characterization instead of a squash constructor, and `set!` to force the constructor (proposal section 4). It changes the admitted signature and the clauses a `match` needs, so a declaration that switches is a migration the verifier must see | L2.3's `paths`, L2.5a/b | M |
| L2.4 | Core theories: named model records, explicit homomorphisms/isomorphisms, scoped notation, sections, `extends` | L1.1, L1.5 projections, L2.5a for h-level fields | L |
| L2.6 | Single-sort `initial T`, `free T on A`, `fold`, checked uniqueness/universal interface. **Specify first** (audit finding 4): the proposal's `universal : (initial T → M) ≃ T.Hom(…)` is not a valid contract. State separately the contractibility of `T.Hom(initial T, M)` for a fixed model `M`, the free-model property relating homomorphisms out of `free T on A` to generator assignments `A → M`, and any maps-out characterization in terms of the constructor and clause data, with higher theories' coherence fields | L2.2, L2.4; H1-admissible signature | M |
| L2.8 | Squares and `cell` face syntax with boundary inspection (HoTT E2) | L2.1; face/source metadata from L1.2r | M |
| L2.9a | Expected-value patterns for `evaluate` | L0.1; own pattern contract and L4.1a infrastructure | S |
| L2.9b | Closed truncation witness readout: a closed computable input, a checked error certificate, and the extracted witness's type specified under transported truncations, which its tests include. Native truncation alone supplies no approximation result | Native H1 `Trunc`, K2.5, L0.1 | M |
| D2.1 | Checked reference, formatter and inspection for each released construct | Corresponding package, including L2.8/L2.9 | L |

L2.2 means both slices when another package needs automatic clauses.
Explicit matching can land before automatic clause search. The theories
release accepts explicit fields and arguments; L4.1b improves its notation
without making records depend on H1. Generated `T.equality` and richer
`T.Displayed`/coherence support have separate gates in stage 3.

**H1's gates at `02a57ef`.** The fragment was specified before it was
implemented, and K2.2/K2.3 landed as reviewable instruction families with
rejection tests, as this plan required. The experiments preceded review, in
the explicitly enabled experimental mode, and every result carries
`kernel extension: H1`, whose transitive provenance is tested apart from
non-computing assumptions. Default admission and release require the
finite-level checklist in the specification's header: the reviewed
soundness note (D1, D4, D5, Lemma H2, the critical-pair check, canonicity),
the complete acceptance matrix, K2.3's verifier and inspection items, a
recorded integration run, and K2.4a's differential contract. A design sketch
is not a reviewed soundness note, and passing examples do not remove the
option.

Universe fixtures cover phantom parameters, stored data, arities, indices
and quotient relations: parameters contribute only through those types.
Reject lowering and mismatched level instances; preserve G0's distinction
between a sort's universe and its parameter telescope's universe.

**K2.5/G2.** Native `Trunc(U, A) : U` preserves the universe. The archive's
`Truncate : U -> U0` has resizing and is not a drop-in replacement. Keep
legacy assumptions available to archive checks until each intentional
migration is justified. Record changed public universes, removed assumptions
and affected consumers; do not add resizing to the rebuilt foundation.
The ordinary migration check stays strict for unrelated changes. The ledger
verifier is not implemented at `02a57ef`; until it is, the archive keeps
its legacy assumptions and no migration is claimed.

**Release fixtures,** with their status at `02a57ef`: declared Nat/list, W
and pushout comparisons (K2.4a, not started); a circle with computed winding
number 1 and `code_meridian` by `rfl` (done in source, in
`docs/examples/h1/winding.cubist`, checked by `tests/declared-match.test.mjs`);
`Trunc` with checked dependent elimination (done, with a hand-written squash
clause) and the set quotient (waits for L2.2b's automatic set clauses); a
tiny theory whose law and homomorphism preservation are checked (L2.4);
rejected bad boundaries (the kernel, done), nonstructural recursion and
missing clauses (L2.2a, done) and missing h-level proofs (L2.2b). These
fixtures need only their small foundation dependencies. A canonical rational
is a later library example, not the H1 gate.

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
| K4.2 | H2 instructions/driver, formal composition along indices, `Id` and J. Explicit deliverables (audit finding 8): the ABI change that represents indices, substitution and level substitution through index lines, rollback, the codec, inspection, and cross-stage regressions that keep every H1 case passing | K2.3, K4.1 | L |
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
| K5.2 | H3 instructions, driver and declared set/prop companion sorts, with the same explicit deliverables as K4.2 for several sorts and joint motives: ABI, substitution, rollback, codec, inspection and cross-stage regressions | K4.2, K5.1 | XL |
| L5.1 | Companion functions/motives, relations, bundles, inductive-inductive initial models | K5.2, L2.6; companion L1.2r motives | L |

The design's statement that the code is the same at every stage and only
the gate widens is a reuse goal, not the implementation contract: ABI 3
represents one sort, its parameters and recorded levels, and one eliminator
motive. Indices, varying-index composition, dependent companion sorts and
joint motives need representation and computation work, which K4.2 and K5.2
list.

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
| B3.1–B3.6 | Full foundations, numbers, finite counting, order, homotopy types and groups rebuild; the reals roadmap's R1 integers are B3 work |
| B4.1–B4.4 | Linear algebra, polynomials, rationals, fields and Galois rebuild; the reals roadmap's canonical rationals (R1) and field interface (R2) are B4 work |
| B5.1–B5.2 | Cauchy/Dedekind reals and analysis: the reals roadmap's R3 and R4, with the [dependencies corrected on 2026-09-28](reals-roadmap.md#dependencies-and-acceptance) |
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

**Corrections from the audit of 2026-09-28** (the
[audit](audits/2026-09-28-audit.md) lists each finding):

- Record the experimental H1 language (K2.2, K2.3 in part, L2.1, L2.2a) with
  the five statuses above, and retire the delivered items from the first
  actions.
- Add I1.2a, instruction isolation, as current work, ahead of the optional
  retirement I1.2b.
- Restrict H1's release checklist to the finite-level fragment; the
  classification walk belongs to the deferred tier-parametric proposal.
- Split K2.4 into differential fixtures and tooling (K2.4a), `Nat`
  retirement (K2.4b) and deferred wider retirement (K2.4c); state that a
  mixed-tier call is reported, not migrated in part.
- Require a specified universal-property contract before L2.6 and L2.3's
  `universal` slice.
- Attach indexed and companion motives to L4.2/L5.1 and the h-level solver
  to L2.2b, so the explicit H1 release depends only on its single-sort
  services.
- Add L2.3b for proof-first h-levels, and record that composite boundaries
  are outside H1.
- Give K2.3/K2.4/K2.5 explicit verifier deliverables, an acceptance matrix
  with missing cases visible, and a recorded integration run.
- Make ABI, substitution, rollback, codec, inspection and cross-stage
  regressions explicit deliverables of K4.2/K5.2.
- Correct the reals roadmap: precision and modulus types, normal-form and
  approximation promises, R3's breakdown, and each package's dependencies.

## First actions

1. **I1.2a, instruction isolation.** Done on 2026-09-28; the optional
   deletion (I1.2b) stays separate.
2. **Reconcile H1's release scope.** One checklist for finite-level H1
   (the specification's header), one differential and retirement contract
   (K2.4a–c), and an explicit review record for each obligation of the
   specification's 4.5. Refresh the status pages and the superseded
   proposals as each gate moves.
3. **Finish the experimental H1 integration (K2.3, L2.1, L2.2a).** K2.3
   is done: the acceptance matrix (10.10) traces every case but K1 with
   tubes, K6 along `ua`, K10, K11 and the cases that wait for other
   packages, and a test checks it against the tests; the inspection, the
   verifier's marker comparison and a recorded run are done. Write the
   checked reference chapter (D2.1). Extend L2.2a through A5, with explicit acceptance
   cases for recursion whose other arguments vary. Retain `cases` until its
   migration gate passes.
4. **Independent language work alongside it.** L4.1a, then L4.1b/L4.4;
   L2.5a/b; core L2.4 records. Automatic clauses (L2.2b) consume the
   h-level work. Settle the universal-property contract before L2.6 and
   L2.3's `universal` slice.
5. **K2.4a and staged K2.5 tooling.** Implement the representation
   comparison and the exact migration ledger without weakening ordinary
   checks. The two H2-dependent tower declarations stay deferred; complete
   removal of the legacy truncation assumptions is not an H1 prerequisite.
6. **Derived interfaces and notation on small examples.** N0/N1 with their
   record prerequisites; N2/N4 after inference. Keep canonical quotient and
   view examples finite and computable.
7. **H2, then the H3 research gate.** Specify the representation and
   computation changes (K4.2, K5.2) before implementing them. Keep the full
   Cauchy reals deferred; the reals roadmap's corrected R2 interface and R3
   obligations give later work a usable contract.

Checker retirement (I1.2b) and learned-search phases 3–5 may proceed
separately; neither blocks this language sequence. H4, E1/E2, trained
search, transport regularity (G4) and interval normalization (G5) keep
their concrete-use and performance gates. Concrete mathematical development
remains paused.
