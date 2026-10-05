# Work plan: language features and their kernel support

Status: revised on 2026-10-04 against `551f9f9`, `main` after PR #140. Since
the last full review, the [work-plan audit](audits/2026-09-28-audit.md) of
2026-09-28 against `02a57ef`, H1 was released (2026-10-02) and merged into
`main` (#118, 2026-10-03), the term checker was retired (I1.2b), partial
elements on a face check (I1.2c), univalence is proved in the library, and
the library is self-contained. The [first actions](#first-actions) are
current as of this revision.
This is the scheduling authority for the linked roadmaps. Package IDs from
the earlier plan are retained; their stage numbers do not impose dependencies.
Sizes (S < M < L < XL) describe relative scope, not elapsed time.

Rows record one of four statuses. **Implemented**: delivered and on by
default; a package delivered in slices names the slices still open.
**Review pending**: a semantic obligation that implementation and passing
tests do not discharge. **Migration pending**: specified tooling or
migrations not yet built. **Deferred**: not scheduled. A fifth,
**Experimental** (behind the `h1` option, results marked
`kernel extension: H1`), ended with H1's release on 2026-10-02, when the
option and the marker were removed.

**Current scope.** Advance the language, elaborator, tooling and the kernel
features they require. Use small checked programs as acceptance evidence. On
2026-10-05 the library rebuild resumed for its foundations: the natural
numbers' arithmetic, quotients, the integers and rationals, and the algebraic
hierarchy through L2.4's theories ([first actions](#first-actions)). Real
and complex analysis, Galois theory and RH stay paused; reaching a language
milestone does not resume them. Their old B-package IDs are retained in the
[deferred library backlog](#deferred-library-backlog).

**The archive is a reference.** The first library in `archive/first-library/`
is not rebuilt as it is and is not relied on. Where the library implements a
part of it, that part is removed from the archive and its dependents import
the library instead; the archive keeps checking completely. So far `nat`'s
arithmetic (from `primes`) and `sets` (for `hlevels`) are gone. What the
library builds differently stays until it is migrated: the archive's
`truncation` and `classical` rest on the legacy `Truncate` assumptions
(K2.5's remedies, first action 7), its `set_quotients` are predicate
quotients over them, and its `equivalences` are bijections and half-adjoint
equivalences, where the library has contractible maps.

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
| Instruction kernel | Stages 1–5; every elaboration check is derived; K1.4's own conversion guide is the default; explicit driver options and cumulative kernel-work counters (learned-search phases 1–2); I1.2a, instruction isolation: no untrusted query can change an instruction's verdict; I1.2b, the term checker and conversion oracle retired (2026-10-02); I1.2c, judgements on a face and partial elements on a face-dependent context, with its two remaining gaps closed (2026-10-04) | Stage-6 performance and certificate work |
| G0 universes | K1.1–K1.4 and L1.1; `U < UU0`, `next`, `max`, generic builtins and rewriting; all 43 former templates check generically | E1 and E2, deferred proposals |
| Proof ergonomics | Grouped binders, `let` with a stated type or a proof block (which replaced `have`, `show` and `suffices` on 2026-09-30), `rfl`, `calc`, `rw`, registered/conditional `simp` and `simpa`, cubical shorthand; Σ projections `p.1`/`p.2` (L1.5); path-operator notation (`-i`, `&`, `\|`, `path i =>`) and readable path diagnostics (PR #71); `hlevel`, L2.5b's first slice; holes `_` and named arguments (L4.1a); implicit parameters and universe inference (L4.1b) | L1.4 (folded path rules, constructor descent), B1 (`Path` induction), broader dependent rewriting, L2.5b's remainder |
| Goal layer | L1.2/A5 core: `Goal`, `Transition`, one name supply, explicit scopes, shared reconstruction; multi-scrutinee motive abstraction | L1.2r |
| Computability | L0.1: dependency tracking, `computable`, exact-value `evaluate`, CLI inspection. The `kernel extension: H1` marker, tracked apart from assumptions while H1 was experimental, was removed at its release | L2.9a, L2.9b |
| Declarations | **Released** on 2026-10-02, on by default with no marker, after K2.1's review (Lemma H2 and the critical pairs approved on 2026-09-30, the model and canonicity on 2026-10-02): K2.2, K2.3, L2.1, L2.2a's first three slices (the expression `match`, the closing statement, and recursion whose other arguments vary), and since 2026-10-04 its fourth (several values and nested patterns), the match statement on sums, which replaced `cases`, and L2.2b's automatic clauses. Nat, W and pushouts are source declarations; sums stay native; the circle's winding number computes in source. K2.4a's differential fixtures and K2.5's ledger verifier are implemented | K2.5's other archive remedies; a review record per K2.2 family; L2.3, L2.3b, L2.4, L2.6–L2.9; stages 4 and 5 |
| Computation notation | Design only | N0–N5 |
| Reference and library | Checked-reference harness; universe chapter rewritten; induction chapter rewritten for declared types: declarations, `match`, structural recursion, dependent matches, path and truncation clauses (D2.1); quick reference (`proof.html`), with a file explorer over every published source. The library's eleven modules, self-contained since 2026-10-04: `nat`, `lists`, `quotients`, effective since 2026-10-05, `hlevels` (L2.5a), `contractible_maps`, `univalence` (L3.1's start) and `propositions`, `h1_truncation`, `h1_classical`, `classical_axioms` and `universe_automorphisms`. The test suite's Cubist sources are modules in `cubist-tests/` | An H1 chapter on higher constructors, obligations and truncation clauses beyond chapter 6's introduction (D0.2, D2.1); one module for the classical assumptions, which `classical_axioms` and `h1_classical` state over two truncations; the library is foundations, not a rebuild wave |

Evidence lives in `tests/universe-generic.test.mjs`,
`tests/proof-ergonomics.test.mjs`, `tests/computability.test.mjs`,
`tests/translator/proof-goals.test.mjs`, `tests/translator/motives.test.mjs`,
`tests/reference-examples.test.mjs` and `tests/library.test.mjs`; for H1,
in `kernel/tests/test_signatures.c`, `tests/h1-admission.test.mjs`,
`tests/h1-driver.test.mjs`, `tests/inductive-declarations.test.mjs`,
`tests/declared-match.test.mjs` and `tests/inductive-repl.test.mjs`.
HoTT's gated probes still reject constructor descent and folded-path cases;
A1/A2 are not complete. The `match` statement is the motive abstraction
service's first source-level client; the expression `match` still builds
its own explicit or expected motive in `web/translator/match.mjs`.

**Baseline at `551f9f9`** (2026-10-04, one machine's observations): the
archive coverage command, `node tools/instruction-coverage.mjs`, reports
3,794 of 3,794 declarations in 369 modules checked with no gap and 3,899 of
3,899 definitions re-derived, at 5,710,965 checking and 2,149,815
re-derivation instructions. The audit's baseline at `02a57ef` was 3,804
declarations in 365 modules and 3,916 definitions, before Nat, W and
pushouts became source declarations and the prelude moved to the library.
That is archive compatibility evidence, not a proof of H1's soundness,
which its review supplies. CI runs on every pull request into `main`, where
work has landed since #118 merged `h1-signatures` on 2026-10-03.

The completed [G0 specification](historical/g0-universe-specification.md)
is kept in `historical/`; its rules remain the contract for later features.
The [historical index](historical/README.md) records the archival decision.
Other roadmaps still contain open work, including the instruction kernel's
conditional stage 6.

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

Stage 2's H1 part passed its gate with the release of 2026-10-02: reviewed
rules, explicit and automatic clauses, and the differential and canonicity
fixtures. Its theories (L2.4) and the rest of matching remain. L4.1
inference is scheduled in stage 1 despite its retained ID.
Core theories can progress alongside H1: records need no new kernel rule.
N1/N2/N4 need neither initial models nor a rebuilt algebra library.

## The instruction kernel and this plan

The trusted checker is the [instruction kernel](kernel-instructions.md).
The untrusted driver is `web/cubical-instruction-driver.mjs`; its own guide
has been the default since K1.4. The C term checker, its conversion oracle
and the JavaScript reference checker were removed on 2026-10-02 (I1.2b).

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

**I1.2b, optional checker retirement (M). Done on 2026-10-02:** the term
checker, the conversion search, the unfolding hints and the trace are
deleted from the kernel and the bridge, their test-only clients moved to
instructions, and archive coverage with the guide is unchanged; see
[what remains of the term checker](kernel-instructions.md#what-remains-of-the-term-checker).
K1.4 removed the runtime dependency, but deletion also required migrating
test-only clients and bridge exports. Move the trusted helpers out of the old checker files,
preserve required syntax builders, and remove old APIs only after the
call graph I1.2a recorded is rechecked: the folded comparison shares its
function with the conversion modes, and its level, formula and scope
helpers move with it. Native search,
certificate compaction and exported content hashes remain conditional
stage-6 work.

**I1.2c, gaps found moving the library's tests to the instruction kernel
(S).** Recorded on 2026-10-02, when the historical kernel was removed.
The instruction kernel derived no partial tube or Glue piece whose term
is a variable whose type reduces only on that face: on the face, the
variable's type was not restricted. `glue [k = 0 ↦ g] (unglue g)`, for `g`
of a Glue type on the face `k = 0`, was refused, where the term checker
accepted it, and library builders for univalence's eta, `idtoequiv` after
`ua`, and the total-space contraction were refused with mismatches of the
same form. **Fixed on 2026-10-04:** face entries, CCHM's `Γ, φ`, and the
instruction `Restrict` type a judgement on a face, and only a partial
element on a face that implies it discharges the assumption
([contexts](kernel-instructions.md#contexts)); the translator translates a
part on its face, its coordinates at their endpoints. The cases are Cubist
sources, `cubist-tests/face_restriction.cubist`, and Glue eta for a
variable, the former todo test, is one of them. The library's new
`univalence` module checks the identity equivalence, the Glue path,
`idtoequiv` and eta in Cubist. The same day (#138) the module proved the
rest as Cubist: unglue's equivalence along a line of Glue types, the
contraction of the type of types equivalent to a type, `idtoequiv` after
`glue_path`, and univalence, all computable; the JavaScript builders they
replace were retired. Archive coverage is unchanged, to the instruction
and the step. Two gaps remained, neither accepting a false judgement;
both were closed later on 2026-10-04:

- **(a) Systems split differently.** The normal form of unglue's
  equivalence over a Glue type on `i = 0` was not checked again: there two
  tubes' agreement is a composition whose tube a substitution of a
  compound point leaves on `i = 0 ∨ j = 0`, where the other side has a
  tube on each, and the driver compared no systems split differently.
  **Closed:** the kernel's step rule `Split` writes a composition's system
  one clause to a tube, each the same term, and drops a tube on the face 0
  (CCHM's systems are partial elements, the same however their faces are
  written; `kernel/tests/test_faces.c`). The driver's split move makes it,
  first, where two compositions' tubes are on different faces, and a
  conversion that falls back to normal forms that differ compares them
  again when either has such a tube, since normal forms keep faces as
  written. The normal form now checks again
  (`tests/translator/univalence-derived.test.mjs`, from the retired builder
  kept as a fixture), and the move is tested on its own
  (`tests/driver-search.test.mjs`). Archive coverage stays complete, with
  less kernel work: 5,685,090 checking and 2,120,554 re-derivation
  instructions, against 5,710,965 and 2,149,815 before. Making normal forms
  split their systems instead was tried and refused: a face's clauses are
  ordered by dimension index, so two normal forms alike up to bound names
  could split into different orders.
- **(b) A face given as an interval.** The driver read a face-sorted
  formula given as a path's argument as the interval with the same
  clauses, and a system's or a transport's interval-sorted face as a face,
  and derived those well-formed terms. **Closed:** it refuses each, with
  its own message (E663–E665).

Rechecking the normal forms of `library/univalence.cubist` finds limits
that are not these gaps, the same on `main`: `glue_path_idtoequiv`'s normal
form meets a type mismatch between two compositions, and those of
`glue_line_equiv`, `equivalent_types_contractible`, `idtoequiv_glue_path`
and `univalence` exhaust the kernel's step budget.

## Stage 0: delivered baseline and remaining documentation

| ID | Package | Status / next obligation |
| --- | --- | --- |
| I0.1 | Merge the development branch into `main` | Done on 2026-10-03: #118 merged `h1-signatures` into `main`, where work has landed since |
| I0.2 | Archive the first library | Done: 369 sources in `archive/first-library/`; keep it as regression evidence. Its prelude `nat` moved to `library/` on 2026-10-04, and `sets` gave way to the library's `hlevels` on 2026-10-05 |
| I0.3 | Start `library/` | Done: the modules listed above, self-contained since 2026-10-04; broader topic coverage is deferred |
| I0.4 | Remove local scratch state | Recorded done on 2026-09-25 |
| L0.1 | Non-computing dependencies, `computable`, `evaluate` | Done; extensions have explicit L2.9 packages below |
| D0.1 | Checked-reference harness | Done: accept/reject examples, excerpts, CLI and REPL transcripts; sketches must be labelled |
| D0.2 | Reference chapters and quick reference | Chapter 5 done with G0. Chapter 6 rewritten on 2026-09-30, when H1 became the default: declarations, parameters, `match`, structural recursion, dependent matches, path and truncation clauses, with the library's Nat, `add` and W quoted as checked, inspectable excerpts. An H1 chapter waits for D2.1. Quick reference done on 2026-09-27: `proof.html` gives each construct one checked example and a link to its chapter section; add an entry with each new construct (`inductive` and `match` on declared types added on 2026-09-30) |

The harness is active; `data-check` markers are not inert. Its acceptance
allows explicitly labelled fragments, so a passing harness does not claim
that every design sketch executes.

**I1.1, module resolution parity (S). Done on 2026-09-27.** One contract,
`web/module-resolution.mjs`, resolves imports for the CLI, the test runner,
the library, REPL and reference tests and the browser worker. Each module
resolves its imports by where it lives. Since 2026-10-04 (#140) a library
module resolves only in `library/`, so the library is self-contained; an
archive module in the archive, then the library, which holds the prelude; a
module of `cubist-tests/` there, then the library, then the archive; a
checked file outside the roots in its own directory, then the library, then
the archive; a REPL entry or reference example library-first. (At first a
library module could import from the archive, and an archive module only
from the archive.) A check holds one module per name, and a clash fails on
the later importer.
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
| L1.5 | Σ projections `p.1`/`p.2`, `show`, `suffices` (A8/B4): delivered 2026-09-27. On 2026-09-30 `show` and `suffices`, with `have`, were removed: `let name : T { … }` expresses each. Open: the separate `Path` induction/`subst` slice (B1) | L1.2; B1 uses A1b's checked induction construction | M |
| L4.1a | Known-signature application elaboration, named arguments and scoped `_` holes. **Done** on 2026-10-04 (`web/translator/arguments.mjs`): a call reads each parameter's type from its function's type once, substituting the kernel's derivation of each earlier argument, where it asked the kernel for the type of the growing application at every argument; on four archive modules and their imports that is 22% fewer elaboration queries (74,548 against 95,547), and archive coverage's kernel work is unchanged (5,710,733 checking instructions). A hole `_` is solved at its call by first-order unification with the arguments' types and the expected type, descending only through type formers, constructors and neutral terms and unfolding definitions; a solution must not mention the hole or a variable bound inside the constraint, a universe that cumulativity leaves open is refused, every solution is checked at its type, and an argument of a call with holes is checked at its parameter's type, where a mismatch is reported. Nothing is searched for. `x := e` names a definition's declared parameter; the parameters before the last one given that nothing gives are holes. The inspector shows each solution. Universe arguments stay explicit (L4.1b); builtins, constructors and recursive calls take no holes. Evidence: `cubist-tests/arguments.cubist`, `tests/arguments.test.mjs`, the reference's [holes](../../web/reference/terms.html#holes) | L1.1, L1.2; L1.3 fuel for inference search | M |
| L4.1b | Opt-in implicit binders and level-argument inference. **Done** on 2026-10-04: a double brace group before a definition's parameters, `def append{{U < UU0, A : U}}(xs, ys : List(U, A))`, declares implicit parameters, which a call does not give among its other arguments: each before the last argument given is a hole, and double braces after the name give them, in order, `concat{{U0, Nat}}(p, q)` (`_` for one to infer), or by name, `concat{{A := Nat}}(p, q)`. An implicit parameter is named only in double braces, and an explicit one only in parentheses. Double braces, which no block or clause list starts with, keep the syntax unambiguous. A definition that calls itself passes them unchanged. Goals and messages show a definition's implicit arguments in double braces. A definition's, or a declared type's, parameters have distinct names, and so have a constructor's arguments. A universe argument can be a hole: the least universe the call needs, the largest lower bound its arguments' types give or an equality's value; U0 where nothing bounds it and the call's type does not mention it, and refused where it does. A type hole that cumulativity leaves open is settled by agreeing bounds from below and above. `library/lists` uses implicit parameters. Evidence: `cubist-tests/implicit_parameters.cubist`, `tests/arguments.test.mjs`, the reference's [universe arguments](../../web/reference/terms.html#universe-arguments) and [implicit parameters](../../web/reference/terms.html#implicit-parameters) | L4.1a | M |
| L4.4 | `apply`, `refine`, pair/sum witness conveniences with visible goals. **Withdrawn** on 2026-10-05, to keep the language small: `let` and `exact` express each, as for `have`, `show` and `suffices`, and holes and implicit parameters already infer what `apply` would; only restating a subgoal's type is saved | L4.1a; L4.1b for implicit arguments | — |
| L2.5a | Checked h-level definitions (HoTT D0a). **Done** on 2026-09-29: `library/hlevels.cubist` defines `IsContr`, `IsProp`, `HasLevel` by recursion on `Nat` and `IsSet` as its level 1, in every universe below `UU0`. It proves contractible types propositions, propositions sets, levels cumulative, having a level a proposition, being contractible a proposition, closure under retracts, Π, Σ, products, subtypes and path types at every level, closure of contractible types under the same constructions but subtypes, which can be empty (`exists x : Unit. Void` is not contractible), and Hedberg's theorem, with `Nat` a set. An equivalence's inverse makes a retract; the statement for the public `Equiv` type waits for D0b | L1.1; small foundation module | S |
| L2.5b | First `hlevel` solver slice (HoTT D1). **First slice** done on 2026-09-29: after `import hlevels;`, `hlevel;` and `hlevel with [h, …];` prove `IsContr`, `IsProp`, `IsSet` and `HasLevel`, and an equality in a type proved a proposition, so a set's parallel paths are equal. Evidence comes from hypotheses and hints, lifted by cumulativity, where a proposition or a contractible type has every level; from h-level statements, which are propositions; and, at a numeral level, from structural rules for Π, Σ, products, homogeneous path types, `Unit`, `Void` and `Nat`. The search builds a term from `library/hlevels.cubist`'s lemmas, which the kernel checks, spends counted fuel, and names the first obligation nothing discharges. Open: `hlevel_rule` registration, with Hedberg for registered carriers such as `Z`; quantified hints used as rules; one layer of unfolding for registered definitions, which the archive's aliases such as `Proposition` need; `Truncate`; the solver for conditional-rule premises and truncation targets; and the inspector's record of selected witnesses | L2.5a, L1.2, L1.3 fuel | M |

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
  (`web/translator/fuel.mjs`), which counts questions rather than the kernel's
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
| K2.1 | Precise H1 signature fragment and soundness note; review gates release. Specified in the [H1 specification](h1-signature-specification.md): every question decided and the specification approved for experimental implementation on 2026-09-27. Lemma H2 and the critical-pair check of its 3.7 **approved** on 2026-09-30; the model (D1, D4, D5) and canonicity **approved** on 2026-10-02, relative to the assumed baseline and premise P1 (its 4.5). **Released** on 2026-10-02: default admission, no experimental option and no marker; item 5's recorded run follows at that revision. Their evidence and decisions are in the [review evidence](h1-review-evidence.md); the [H2 case analysis and critical-pair draft](h1-critical-pairs.md) was added on 2026-09-30, and the written-out [model](h1-model.md) and [canonicity](h1-canonicity.md) arguments the same day, as review drafts, revised after their first review the same day. The release checklist in its header covers the finite-level fragment only; the classification walk of its 2.3 belongs to the deferred tier-parametric proposal, not to this gate (audit finding 2) | G0 specification | L |
| K2.2 | H1 instructions, the six families F1–F6 of the specification's section 5. **Released** on 2026-10-02: all six implemented with ABI version 3, each reviewed and merged into `h1-signatures` separately. Open: a review record per family for its semantic obligations; passing tests, the acceptance matrix's randomized K10/K11 property tests among them (the specification's 10.10, which `tests/acceptance-matrix.test.mjs` checks against the tests), do not discharge them | K1.2, K2.1 | XL |
| K2.3 | H1 driver, bridges, signature serialization and generated-rule derivation. **Released** on 2026-10-02: admission from a normal form, the codec and renderers, derivations and search for instances, constructors and eliminators, rollback and commit, the `kernel extension: H1` marker (with L2.1), import invalidation by construction, signatures in the CLI's `inspect`, and clause types, which L2.2a's `match` consumes (`web/translator/match.mjs`). Since 2026-09-28 the CLI's `inspect` and the workbench's inspector show a declared type's signature and its eliminator's clause types, and the migration verifier compares the marker apart from assumptions (the specification's 6.4, 6.5). The acceptance matrix traces every case of 10.10 but those that wait for another package, K1 with tubes, K6 along `ua` and the randomized K10 and K11 since 2026-09-29; each traced case is named by its ID in its test, and `tests/acceptance-matrix.test.mjs` checks the matrix against the tests. Since 2026-09-29 fixtures of its own try the checker on the mutations its reviews found: a missing label, an invalid ID, a missing remainder and a range traced in part. The whole suite ran at a pinned revision on 2026-09-28: CI run 36472206548 at `bef00e3`, all seven jobs passed. A release repeats that run at its own revision, and `node tools/release-evidence.mjs` records it: the revision, its build stamp, each local check's command and outcome, run in a fresh checkout of it, and the jobs of the CI runs dispatched on that commit (a pull request's run checks out a merge commit) | K1.3, K2.2 | L |
| K2.4a | Differential fixtures X1–X8 of the specification's 7.3 and their tooling: the translation τ as a driver option, the verifier's report of a mixed-tier call (X8), X5's cost record, and the verifier's comparison of a module that declares a type, whose edited copy has another, generative signature. **Implemented:** the representation option, declared archive replay, mixed-call verifier and schema comparison; see the [differential evidence](h1-differential-evidence.md). X2 has an explicit coverage remainder and exposes an administrative Eta mismatch in its literal criterion. **Historical since 2026-10-02:** no longer a release gate (the specification's checklist item 6), since Nat, W and pushouts were retired by source declaration and sums stay native | K2.3; the representation map of the specification's section 7 | M |
| K2.4b | Retire the `Nat` instructions only, by the criterion of the specification's 7.4 (Q16): X1–X4 and X6–X8 pass, X5 is recorded, and the archive is migrated by τ under the strict verifier. Sum, W and pushout stay trusted for tier-1 arguments, with X1–X3, X7, X8 and their native tests as regressions. **Overtaken:** at the maintainer's request Nat and W were retired on 2026-09-30, before this criterion was met, and pushouts on 2026-10-01; the X fixtures compare against the pinned pre-migration kernel | K2.4a | M |
| K2.4c | Wider retirement of the sum, W and pushout instructions. **Decided** on 2026-10-01: sums stay native at every level, and pushouts are an H1 declaration in `pushout.cubist`, their instructions retired as W's were on 2026-09-30. Nothing remains to retire. A W type or pushout over `UU`-tier types needs a separate fixed-universe declaration | — | — |
| K2.5 | G2 truncation/resizing policy and migration ledger. Policy and measured ledger in the [H1 specification](h1-signature-specification.md#8-k25-truncation-and-resizing-g2); no resizing assumption (Q12) and the 8.4 remedy groups (Q17) decided, and the policy approved, on 2026-09-27. **Implemented:** the exact ledger verifier, 17 pinned changes and G2/G4–G7 fixtures; see the [scoped migration record](h1-truncation-migration.md). Two of the migrated slices, `h1_cauchy_quotient` and `h1_zorn_step`, build on archive developments and moved to `cubist-tests/` when the library became self-contained (2026-10-04). **Migration pending:** the rest of the archive remedies; the two H2-dependent tower declarations remain deferred; removing every legacy truncation assumption is not an H1 prerequisite | K2.1; implementation with K2.3/L2.1 | M |
| L2.1 | One-sort `inductive` declarations and signature diagnostics. **Released** on 2026-10-02: the header's result position, lowering with data before positions, universe classification and the least level, uses of the type and its constructors, precise refusals. Reference chapter 6 teaches them since 2026-09-30 (D2.1). Excluded by the specification: a composite boundary such as `Torus2`'s `trans(p, q) = trans(q, p)` (its 1.4, Q3; the square torus is admitted), and proof-first `: set`/`: prop`, which is L2.3b | K2.3 | L |
| L2.2a | Explicit `match`, motives, structural recursion and path clauses. **Released, first slice:** the expression `match v [as z] [return T] { c(xs) @ i => … }`, each clause checked against the kernel's clause type; dependent motives; path clauses and hand-written squash clauses with `T.squash`; recursion on a constructor's argument with the other arguments fixed, in a definition whose whole body is the match, where the matched parameter stands for the clause's constructor. The H1 winding-number fixture computes in source. **Released, second slice** (written on 2026-09-29): the closing proof statement `match v { c(xs) @ i => { … } … }`, its motive the goal over `v` through the A5 motive service. A hypothesis whose type mentions `v` is generalized and bound again, under its own name, in each clause. There a variable `v` names the constructor, and a local definition made from either is made again from their values; a recursive call passes its own value for each generalized parameter. **Released, third slice** (written on 2026-09-29): recursion whose other arguments vary. When a recursive call changes another parameter, or passes one whose type mentions the matched parameter, the match, in either form, takes its motive from the motive service, over the declaration's other parameters but those the matched parameter's type depends on; each clause binds them again under their own names, and a call passes values of its own for them. It passes those the matched parameter's type depends on, and universe parameters, unchanged. Name resolution decides, so no spelling of a call or a binder changes it; a match whose calls pass the other parameters unchanged, or that never calls itself, is elaborated as written. The motive over the other parameters also stands when the match as written fails before any call and that motive makes one, as when a dependent parameter is used at its refined type first. Only the elaboration kept spends the declaration's fuel. A goal shows a parameter bound again under its source name, without the one it supersedes. Acceptance cases: an accumulator, computed and proved equal to addition; a call spelled with an operator; parameters before the matched one, dependent (used before the call too), shadowed and taken apart by a nested match; a squash clause over a generalized parameter; fuel and searches recorded once. **Released, fourth slice** on 2026-10-04 (`web/translator/patterns.mjs`): several values, `match xs, ys { nil, _ => …; … }`, in both forms; nested patterns, `cons(x, cons(y, rest))`; a variable or `_` in a constructor's place, and a constructor without arguments by its name inside a pattern; clauses tried in order, the first that fits taking a case, with a missing case and a clause never reached refused. Compiled value by value into matches on one value each, which elaborate as before, so recursion on the first value taken apart still works. The expression form takes its motive from the motive service when its expected type mentions the matched variable, binding the hypotheses about it again in each clause; and a match whose first elaboration fails as written is kept elaborated over the declaration's other parameters, recursive call or not. Evidence: `cubist-tests/patterns.cubist`, the reference's [patterns](../../web/reference/induction.html#patterns). **`cases` retired** on 2026-10-04: the match statement takes a sum apart, `left(a) => { … } right(b) => { … }`, each clause proving the goal at its side through the motive service; a goal that depends on the value only through a redex that drops it, as after `intro`, is the motive itself, as `cases` made it. The 26 `cases` statements, 24 in 11 archive modules and two in test sources, became matches: at the migration's commit (1118c1a), where `cases` still parses, `node tools/verify-proof-migration.mjs --base main` reports identical terms for all 50 modules compared, 39 of them dependents. `cases` is refused with its match form (E164), and a historical source reads `cases` as `match` (`web/cubist/legacy-syntax.mjs`). Evidence: `cubist-tests/sum_match.cubist`, the reference's [taking a sum apart](../../web/reference/proof-blocks.html#sums) | L2.1, L1.2; relevant L1.2r metadata; L4.1a improves the release without gating it | L |
| L2.2b | Automatic clauses and explicit `obligations`. **Released** with H1 on 2026-10-02: dependent set and groupoid squash clauses derive from checked h-level evidence; expression and statement forms accept explicit obligations. E4/E11 and evidence/refusal/inspection regressions are in `tests/automatic-clauses.test.mjs`. The broader h-level solver remains independent of this package | L2.2a, L2.5b; checked h-level evidence | M |
| L2.3 | Supported `deriving`: `paths`, `decidable_equality`, `irrelevance`, `ind_prop`, `rec`; `universal` slice, once L2.6's contract is specified | L2.2; `universal` also uses L2.4/L2.6 | L |
| L2.3b | Proof-first h-levels: `: set` and `: prop` proved from the generated path characterization instead of a squash constructor, and `set!` to force the constructor (proposal section 4). It changes the admitted signature and the clauses a `match` needs, so a declaration that switches is a migration the verifier must see | L2.3's `paths`, L2.5a/b | M |
| L2.4 | Core theories: named model records, explicit homomorphisms/isomorphisms, scoped notation, sections, `extends`. **Specified** on 2026-10-05 in [core theories](core-theories.md): `theory` declarations of set and proposition sorts, constants, operations with notation and laws; `T.Model` as a Σ record with a constructor and projections, `m.f`; `open`; sections; `extends` with labels and renaming; `T.Hom` and `T.Iso` with identity, composition and inverse. Slices: notation packs and `open`, theories with models and extension, sections, homomorphisms and isomorphisms | L1.1, L1.5 projections, L2.5a for h-level fields | L |
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

**H1's gates.** The fragment was specified before it was implemented, and
K2.2/K2.3 landed as reviewable instruction families with rejection tests, as
this plan required. The experiments preceded review, behind an explicit
option, with every result marked `kernel extension: H1`. Default admission
required the finite-level checklist, now in the specification's
[history](h1-history.md#status-and-release-record): the reviewed soundness
note (D1, D4, D5, Lemma H2, the critical-pair check, canonicity), the
complete acceptance matrix, K2.3's verifier and inspection items, a recorded
integration run, and K2.4a's differential contract, retired as a gate on
2026-10-02. **Released on 2026-10-02:** with the checklist's items 1–4 approved
and item 6 retired as a gate, the option was removed and default admission
granted; results carry no marker. Item 5's run at that revision, `581e03c`,
passed the same day, and again on 2026-10-03 at `8229181`, the revision
merged into `main` after the refactors of #120–#132: the
[release evidence](h1-release-evidence.md).

Universe fixtures cover phantom parameters, stored data, arities, indices
and quotient relations: parameters contribute only through those types.
Reject lowering and mismatched level instances; preserve G0's distinction
between a sort's universe and its parameter telescope's universe.

**K2.5/G2.** Native `Trunc(U, A) : U` preserves the universe. The archive's
`Truncate : U -> U0` has resizing and is not a drop-in replacement. Keep
legacy assumptions available to archive checks until each intentional
migration is justified. Record changed public universes, removed assumptions
and affected consumers; do not add resizing to the rebuilt foundation.
The ordinary migration check stays strict for unrelated changes. The [ledger verifier and scoped migrations](h1-truncation-migration.md) are implemented since 2026-09-30; the archive keeps its legacy assumptions.

**Release fixtures,** updated 2026-09-30: declared Nat, sum, W
and pushout comparisons (K2.4a implemented, with the X2 remainder in its evidence record); a circle with computed winding
number 1 and `code_meridian` by `rfl` (done in source, in
`docs/examples/h1/winding.cubist`, checked by `tests/declared-match.test.mjs`);
`Trunc` with checked dependent elimination (done, with a hand-written squash
clause, or automatic h-level evidence) and the set quotient (E4's dependent elimination and E11's groupoid elimination checked with automatic squash clauses); a
tiny theory whose law and homomorphism preservation are checked (L2.4);
rejected bad boundaries (the kernel, done), nonstructural recursion and
missing clauses (L2.2a, done) and missing h-level proofs (L2.2b). These
fixtures need only their small foundation dependencies. A canonical rational
is a later library example, not the H1 gate.

`evaluate` patterns require a specified matching language and clear mismatch
messages; they do not inherently require H1. Truncation readout does require
native truncation and is a closed evaluation tool, not a source eliminator
`Trunc(A) -> A`.

The archive's `cases` uses were migrated to `match` under the strict
verifier, and the statement removed from parser, elaborator, highlighter,
reference and error tables, on 2026-10-04. Legacy explicit eliminators
remain parseable.

## Stage 3: derived interfaces, views and automation

These packages provide the language's small checked foundation. They do not
require rebuilding whole mathematical areas.

| ID | Package | Depends on | Size |
| --- | --- | --- | --- |
| L3.1 | Canonical equivalence interface (HoTT D0b). **Started** in the library on 2026-10-04: `contractible_maps` defines `ContrEquiv`, the kernel's contractible-fiber form with the native orientation `y = f(x)`, with the identity, inverses and both inverse laws (`equiv_inverse`), equivalences from inverses (`inverse_equiv`), and equality of two equivalences with one forward map; `univalence` proves `glue_path`, `idtoequiv` and univalence, all computable. Open: composition and the Π/Σ/product equivalences, `equiv_eq` for pointwise-equal maps, and moving the `ua` builtin from `paths`' `Equiv` to `ContrEquiv` | G0; existing checked equivalence constructions | M |
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

Resumed on 2026-10-05, as first actions 1, 2 and 4: the natural numbers'
arithmetic, quotients, the integers, the rationals as a quotient, and the
algebraic hierarchy from semigroups to fields. The rest of B3 and B4 stays
deferred.

Small h-level/equivalence definitions and language acceptance fixtures are
part of their owning language packages. They do not commit to proving all
results from the corresponding library area.

## Planning corrections

**Revision of 2026-10-05:** withdraw L4.4, `apply` and `refine`, which
`let` and `exact` express; resume the library's foundations, with the
archive kept as a reference that loses each part the library implements;
specify L2.4 in [core theories](core-theories.md) and schedule it before the
algebraic hierarchy, whose structures are its theories and whose notation is
its scoped notation, since `+` and `*` otherwise mean one `add` and one `mul`
per scope.

**Review of 2026-09-27** (against `fabb174`):

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

**Revision of 2026-10-04** (against `551f9f9`):

- Record H1's release, its merge into `main`, I1.2b and I1.2c, and retire
  the experimental status with the `h1` option.
- Record the library's eleven modules and its self-containment, the
  univalence proofs as L3.1's start, and the `cubist-tests/` root in module
  resolution.
- Refresh the archive baseline, and replace the completed first actions
  with the current sequence: L4.1a, I1.2c's remaining gaps, then the rest
  of matching and the `cases` migration. The same day L4.1a and both
  gaps were delivered.

## First actions

Revised on 2026-10-05. Done since the audit: instruction isolation (I1.2a),
H1's release scope and integration, with its release on 2026-10-02 and its
merge into `main`, the checker's retirement (I1.2b), face restriction
(I1.2c), argument inference (L4.1a, L4.1b, 2026-10-04), and the rest
of explicit matching with the `cases` migration (L2.2a, 2026-10-04).

1. **One module for the natural numbers.** `nat` and `naturals` become one
   module, `nat`, written in today's syntax: `Nat`, its arithmetic and
   order, and their laws. Nothing is imported automatically: a module that
   uses the natural numbers, numerals included, imports `nat` itself. The
   archive's copies of that arithmetic are removed, its dependents
   importing `nat`. **Done** on 2026-10-05, with the archive's `sets`,
   which `hlevels` replaces.
2. **Effective quotients.** In `quotients`, related elements are exactly
   those with equal classes, for a relation that is an equivalence of
   propositions: the integers' and rationals' decidable equality needs it.
   **Done** on 2026-10-05: relatedness to an element descends into the set
   of propositions, `Prop(U)` of the new module `propositions`, by
   univalence's propositional extensionality; the eliminators take their
   motive from any universe below `UU0`. Closed classes compute
   (`cubist-tests/quotient_effectiveness.cubist`).
3. **Core theories (L2.4),** as [specified](core-theories.md), in slices:
   notation packs and `open`; theories with their models and extension;
   sections; homomorphisms and isomorphisms.
4. **The algebraic hierarchy, the integers and the rationals.** Semigroups,
   monoids, groups, abelian groups, commutative rings and fields as library
   theories; `Nat` a commutative monoid for addition and for
   multiplication; the integers as a quotient of pairs of naturals, a
   commutative ring; the rationals as a quotient of fractions, a field.
5. **Independent language work.** L2.5b's remainder; the universal-property
   contract before L2.6 and L2.3's `universal` slice; L1.3's worker
   cancellation.
6. **Equivalences (L3.1), from the library's univalence.** Then L3.2's
   Σ/universe `ext`. In the library, one module for the classical
   assumptions, over the computing `Trunc`.
7. **K2.5's remaining archive remedies.** The two H2-dependent tower
   declarations stay deferred; complete removal of the legacy truncation
   assumptions is not required.
8. **Derived interfaces and notation on small examples.** N0/N1 after the
   theories of first action 3; N2/N4 after inference. Keep canonical
   quotient and view examples finite and computable.
9. **H2, then the H3 research gate.** Specify the representation and
   computation changes (K4.2, K5.2) before implementing them. H2's indexed
   families will need implicit indices. Keep the full Cauchy reals deferred;
   the reals roadmap's corrected R2 interface and R3 obligations give later
   work a usable contract.

Learned-search phases 3–5 may proceed separately; they do not block this
language sequence. H4, E1/E2, trained
search, transport regularity (G4) and interval normalization (G5) keep
their concrete-use and performance gates. Concrete mathematical development
beyond the library's foundations of first actions 1, 2 and 4 remains paused.
