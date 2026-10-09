# Work plan: language features and their kernel support

Status: revised on 2026-10-05 against `066ca77`, `main` after PR #164. Since
the last full review, the [work-plan audit](audits/2026-09-28-audit.md) of
2026-09-28 against `02a57ef`, H1 was released (2026-10-02) and merged into
`main` (#118, 2026-10-03), the term checker was retired (I1.2b), partial
elements on a face check (I1.2c), univalence is proved in the library, and
the library is self-contained. Since the revision of 2026-10-04: argument
inference and implicit parameters (L4.1a, L4.1b), the rest of explicit
matching and the retirement of `cases` (L2.2a), core theories (L2.4), the
library's foundations (that revision's first actions 1, 2 and 4: `nat`, effective
quotients, the algebraic hierarchy, the integers and the rationals), and the
decisions of the notation roadmap (L2.10) and of the theory syntax revision
(L2.4c). The [first actions](#first-actions) are current as of this
revision, and the [open decisions](#open-decisions) list what waits for
the maintainer. The roadmaps' [index](README.md#at-a-glance) summarizes
both.
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
hierarchy through L2.4's theories, all done the same day
([first actions](#first-actions)). Real
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
(K2.5's remedies, first action 11), its `set_quotients` are predicate
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
| Proof ergonomics | Grouped binders, `let` with a stated type or a proof block (which replaced `have`, `show` and `suffices` on 2026-09-30), `rfl`, `calc`, `rw`, registered/conditional `simp` and `simpa`, cubical shorthand; Σ projections `p.1`/`p.2` (L1.5); path-operator notation (`&`, `\|`, `path i =>`) and readable path diagnostics (PR #71); `~p` and `~i` for reversal, in place of prefix `-` (L2.10i, 2026-10-06); `hlevel`, L2.5b's first slice; holes `_` and named arguments (L4.1a); implicit parameters and universe inference (L4.1b); the keywords of terms and statements and the built-in `Unit` and `Void` reserved (E175). `apply` and `refine` (L4.4) withdrawn | L1.4 (folded path rules, constructor descent), B1 (`Path` induction), broader dependent rewriting, L2.5b's remainder |
| Theories and notation | L2.4, complete on 2026-10-05: `theory` declarations of sorts, operations with notation, and laws, which must state propositions (E818); `T.Model`, `open`, sections, `extends` with labels and renaming, `T.Hom` and `T.Iso`. The library's algebraic hierarchy is its first client. L2.10's and L2.4c's decisions recorded | L2.4c, the theory syntax revision; L2.4b (structure identity, displayed models), L2.6 (initial and free models), L2.10a–e, j and k, notation views and literals; implementation not started |
| Goal layer | L1.2/A5 core: `Goal`, `Transition`, one name supply, explicit scopes, shared reconstruction; multi-scrutinee motive abstraction | L1.2r |
| Computability | L0.1: dependency tracking, `computable`, exact-value `evaluate`, CLI inspection. The `kernel extension: H1` marker, tracked apart from assumptions while H1 was experimental, was removed at its release. L2.9a expected-value patterns and L2.9b closed witness readout delivered in #181/#182 (2026-10-07, after the runtime evaluation investigation at `825c8b88`). EVAL0's evaluation baseline recorded on 2026-10-08 | EVAL1–EVAL8 |
| Declarations | **Released** on 2026-10-02, on by default with no marker, after K2.1's review (Lemma H2 and the critical pairs approved on 2026-09-30, the model and canonicity on 2026-10-02): K2.2, K2.3, L2.1, L2.2a's first three slices (the expression `match`, the closing statement, and recursion whose other arguments vary), and since 2026-10-04 its fourth (several values and nested patterns), the match statement on sums, which replaced `cases`, and L2.2b's automatic clauses. Nat, W and pushouts are source declarations; sums stay native; the circle's winding number computes in source. K2.4a's differential fixtures and K2.5's ledger verifier are implemented | K2.5's other archive remedies; a review record per K2.2 family; L2.3, L2.3b, L2.6–L2.8; stages 4 and 5 |
| Computation notation | Design only; N1's prerequisite, L2.4, delivered on 2026-10-05, though its laws cannot yet state a monad's; L2.4c's theory families, decided, will, for monads on sets | N0–N5 |
| Reference and library | Checked-reference harness; universe chapter rewritten; induction chapter rewritten for declared types: declarations, `match`, structural recursion, dependent matches, path and truncation clauses (D2.1); quick reference (`proof.html`), with a file explorer over every published source; since 2026-10-05 a chapter on [theories and models](../../web/reference/theories.html) with the library's algebra and numbers, and set quotients, the library's univalence and `propositions` in the cubical chapters (#159). The library's fourteen modules, self-contained since 2026-10-04: `nat`, `lists`, `quotients`, effective since 2026-10-05, `algebra`, the hierarchy as theories, `integers`, `rationals`, `hlevels` (L2.5a), `contractible_maps`, `univalence` (L3.1's start) and `propositions`, `h1_truncation`, `h1_classical`, `classical_axioms` and `universe_automorphisms`. The test suite's Cubist sources are modules in `cubist-tests/` | An H1 chapter on higher constructors, obligations and truncation clauses beyond chapter 6's introduction (D0.2, D2.1); one module for the classical assumptions, which `classical_axioms` and `h1_classical` state over two truncations; the library is foundations, not a rebuild wave |

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

**Baseline at `b6aa6e5`** (2026-10-05, one machine's observations): the
archive coverage command, `node tools/instruction-coverage.mjs`, reports
3,837 of 3,837 declarations in 368 modules checked with no gap and 3,942 of
3,942 definitions re-derived, at 5,694,660 checking and 2,131,461
re-derivation instructions, in 44 and 13 seconds; #163 and #164 changed
only documents, so it holds at `066ca77`. At `551f9f9` (2026-10-04)
it was 3,794 declarations in 369 modules and 3,899 definitions, at
5,710,965 and 2,149,815 instructions, before `nat` replaced the archive's
copies of its arithmetic and `hlevels` its `sets`. The audit's baseline at
`02a57ef` was 3,804 declarations in 365 modules and 3,916 definitions,
before Nat, W and pushouts became source declarations and the prelude moved
to the library.
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
| L2.5b | First `hlevel` solver slice (HoTT D1). **First slice** done on 2026-09-29: after `import hlevels;`, `hlevel;` and `hlevel with [h, …];` prove `IsContr`, `IsProp`, `IsSet` and `HasLevel`, and an equality in a type proved a proposition, so a set's parallel paths are equal. Evidence comes from hypotheses and hints, lifted by cumulativity, where a proposition or a contractible type has every level; from h-level statements, which are propositions; and, at a numeral level, from structural rules for Π, Σ, products, homogeneous path types, `Unit`, `Void` and `Nat`. The search builds a term from `library/hlevels.cubist`'s lemmas, which the kernel checks, spends counted fuel, and names the first obligation nothing discharges. **Second slice** done on 2026-10-06: `hlevel_rule lemma;` registers a checked lemma whose type states a level, for the modules after it and those that import it; its parameters are read by matching its statement's carrier against an obligation, and its premises, level statements under binders, are proved in turn, a premise that repeats an obligation being proved counting as a cycle. Quantified evidence in scope and quantified hints are rules too, and a failed premise is named. The library registers `prop_type_is_set`; quotients, `Z` and `Q` were already sets through their squash constructors. The same search fills a level statement a call leaves out, as a model's setness field omitted from `T.make(…)`. Evidence: `cubist-tests/hlevel_rules.cubist`. Open: Hedberg from registered decidable equality; one layer of unfolding for registered definitions, which the archive's aliases such as `Proposition` need; `Truncate`; the solver for conditional-rule premises and truncation targets; and the inspector's record of selected witnesses | L2.5a, L1.2, L1.3 fuel | M |

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
| L2.4 | Core theories: named model records, explicit homomorphisms/isomorphisms, scoped notation, sections, `extends`. **Specified** on 2026-10-05 in [core theories](core-theories.md): `theory` declarations of set and proposition sorts, constants, operations with notation and laws; `T.Model` as a Σ record with a constructor and projections, `m.f`; `open`; sections; `extends` with labels and renaming; `T.Hom` and `T.Iso` with identity, composition and inverse. Slices: notation packs and `open`, theories with models and extension, sections, homomorphisms and isomorphisms. **First two slices done** on 2026-10-05: a theory expands, in the translator, to `T.Model`, `T.make`, a projection per field and a model per parent, each checked and computable; `m.f` reads a field or a parent's model and prints so; `open m;` binds fields and notation for the rest of a block; parents are labelled and renamed, and an ancestor two parents reach with one field and one type is shared. Refusals have codes E801–E815. **Homomorphisms and isomorphisms done** the same day: `T.Hom` and `T.Iso` with their constructors, fields, identity, composition, inverse and parents' homomorphisms, generated when every operation takes and returns sorts (E817 otherwise), computing on closed models; `e.f` on any value whose type is a theory's record; and argument inference reads a homomorphism's models off its type: a definition applied on both sides is compared unfolded first, and matched argument by argument only where the other arguments and the expected type leave a parameter open. **Sections done** the same day: a section's parameters come first in each definition in it, its models are opened for each statement and proof, and its earlier definitions are applied to its parameters; a definition in a section has no implicit parameters of its own, and its recursive calls pass the section's parameters unchanged. The slices' review, the same day, added: a law states an evident proposition, an equation between elements of a sort, `Unit`, `Void`, a proposition sort, or `forall`, `->` and `and` over those (E818); `Unit` and `Void` are reserved names, with the keywords of terms and statements (E175); and generated homomorphisms name their models and maps apart from the theory's own names. Evidence: `cubist-tests/theories.cubist`, `cubist-tests/theory_morphisms.cubist`, `cubist-tests/theory_sections.cubist`, `tests/theories.test.mjs`, the reference's [theories and models](../../web/reference/theories.html). **L2.4 is complete**; structure identity and displayed models are L2.4b | L1.1, L1.5 projections, L2.5a for h-level fields | L |
| L2.4c | Theory syntax revision, **decided** on 2026-10-05 ([core theories](core-theories.md#revision-l24c)): carriers as fields with an h-level, `M : set U;`, `P : prop U;` or `M : U;`, replacing `sort`; the universe, and parameters that homomorphisms keep fixed, named in the header, `theory Monoid(U < UU0)`, `theory Module(U < UU0, R : CommRing(U))`; the theory's name as the type of its models, `G : Monoid(U0)`, retiring `T.Model`; theory families, `F(A : set U) : set U` for a monad on sets, relations among them as families of propositions indexed by carriers, so that homomorphisms of preorders are the monotone maps; homomorphisms that push covariant inputs forward and pull contravariant inputs back, and none for mixed inputs; independent theories combined without changing either, carriers merging by name and other clashes ambiguous only where used, reachable through their parents' labels; and qualified operators, `a G.(+) b`. Migrated in two commits, the old forms parsing until every source moves. **First slice done** on 2026-10-06: carriers `M : set U;`, `P : prop U;` and `M : U;`, one universe named in the header, and `Monoid(U0)` as the type of models; `sort` (E180) and `T.Model` (E396) refused, every source moved with the library's terms identical, and earlier revisions read in the new forms. **Second slice done** the same day: several universes and parameters in the header, kept fixed by homomorphisms and taken by a child by name (`cubist-tests/theory_headers.cubist`). **Third slice done** the same day: homomorphisms by variance, inputs with no carrier kept, covariant ones pushed forward, contravariant ones pulled back, none for mixed inputs (`cubist-tests/theory_variance.cubist`). **Fourth slice done** the same day: theory families with set-indexed evidence, relations as families of propositions with notation, homomorphisms mapping each family at each index, and no isomorphisms for a family of sets indexed by a carrier; the identity monad is a `Monad` (`cubist-tests/theory_families.cubist`). **Fifth slice done** the same day: independent parents, carriers merging by name and kind, other clashes ambiguous where used and reached through labels (`cubist-tests/theory_independent.cubist`). **Sixth slice done** the same day: `use m;` in blocks and at a file's top level, `m.(e)`, and qualified operators `a m.(*) b` and `m.(*)`, a parent's through its label (`cubist-tests/theory_use.cubist`); `open` migrates to `use`. **L2.4c is complete** | L2.4 | M |
| L2.4d | Morphisms by opt-in ([categories](categories.md)), **proposed** on 2026-10-07: `deriving (isomorphisms)`, generated by transport, so that a field of any variance, a family indexed by a carrier and a topology's open sets move across; and `deriving (morphisms)`, today's variance rule, with the default category `T.cat` once L3.4 exists, implying `isomorphisms`. An opt-in that cannot be honoured refuses the declaration, naming the field; naming `T.Hom` or `T.Iso` without it is refused at the use; `free` requires the checked `morphisms, free` capability, and `initial` accepts that or `morphisms, initial`; recursors alone confer neither capability. L2.4b and L3.3 require `isomorphisms`. Two-commit migration: opt in every theory whose morphisms are used, verify identical terms, then stop deriving by default | L2.4c; L3.4 for `T.cat`; L3.1 for untruncated carriers | M |
| L2.4e | User-defined morphisms, `morphisms where …`, **proposed and deferred**: a proposition on maps of carriers closed under identities and composites, with the standardness obligation (HoTT book §9.8) that keeps `T.cat`'s invertible morphisms equal to `T.Iso`. Continuous, measurable and short maps; no current library client | L2.4d; a first metric or topological client | M |
| L2.11 | Laws proved propositions, **proposed** on 2026-10-07: the law check accepts a statement the `hlevel` solver proves a proposition, equations in a parameter's carriers and `IsContrMap(…)` among them; the syntactic check stays the fast path. Universal properties (L3.5) and theories over parameters need it. Propositionhood does not prove the law in a generated model: initial/free derivation must discharge it separately | L2.5b | S |
| L2.12 | Implicit arguments in theory operations and derived operations, **proposed** on 2026-10-07: `comp{{x, y, z : Ob}}(g : Arr(y, z), f : Arr(x, y)) : Arr(x, z) notation g ∘ f`, inferred as L4.1b infers a definition's, with notation over the explicit arguments (E810 and E170 refuse both today) | L4.1b | M |
| L2.6 | Initial and free objects as checked capabilities, **revised and decided** on 2026-10-07 in [core theories](core-theories.md#initial-and-free-models-l26): `deriving (morphisms, free)` requests a generic construction and universal equivalence relative to the selected morphisms and carrier-forgetting functor; it supplies `initial` on `Void`. The weaker `deriving (morphisms, initial)` requests initiality alone. Both may fail. `morphisms` alone provides `T.IsInitial`, an ordinary predicate for manual proofs about existing models, also used by generated certificates. A single-carrier H1 equational construction is the first strategy; additional laws, including `zero != one`, require checked proofs. Unsupported cases and outstanding obligations are distinct from proved nonexistence; `Field` has morphisms but no initial object across all characteristics. Five slices: opt-in/registry; H1 construction and fold; uniqueness and universal proofs; extra-law evidence; higher coherences. Only complete checked proofs register a capability; untruncated recursors remain ordinary inductive constructions. The construction prototype of 2026-10-06, `initial N : T(…);` and `free W(A : U0) : T(…) on A;` (`cubist-tests/initial_models.cubist`), is retained as the second slice's evidence and registers no capability | L2.2, L2.4d; L2.11 for general laws; H1 for the first strategy | M |
| L2.8 | Squares and `cell` face syntax with boundary inspection (HoTT E2). **First slice** done on 2026-10-06: the implementation plan's box notation, `compose j in A from b { on i = 0 => x; on i = 1 => q @ j; }` and `fill j in A from b at k { … }`, lowers to `comp` and `fill`, faces being formulas of equations with `and` and `or`; a composition prints as its box. Evidence: `cubist-tests/box_notation.cubist`. **Second slice** done the same day: `library/squares.cubist` names a square's edges by its corners, `Square(a0_, a1_, a_0, a_1)`, and builds by conversion the reflexive and naturality squares, transposition and both flips, double composition and its filler (`trans` its case with a constant first edge), and horizontal and vertical composition; the inspector shows a square's edges and corners. Evidence: `cubist-tests/square_constructions.cubist`. **Third slice** done the same day: two squares on the same three sides have equal tops (`top_unique`), which gives the conversions between a square and an equation of composites both ways (`square_to_path`, `path_to_square`, through the diagonal and `retop`), and the library's `naturality_path` and `cong_trans`, the statements of the archive's `homotopy_naturality` and `map_concat`. Open: the archive's raw `comp` lemmas (`homotopy_natural`, `map_concat`, `transport_concat`) re-derived through them, a migration of archive proofs | L2.1; face/source metadata from L1.2r | M |
| L2.9a | Expected-value patterns for `evaluate`. **Done** on 2026-10-06: an expected value with a hole `_` is a pattern, matched against the normal form part by part (`web/translator/evaluation.mjs`): a hole matches anything; a pair, an injection or a constructor of the part's declared type applied to patterns matches a value built so, in the kernel's argument order; `typed(T, p)` matches as `p` where `T` is the part's type; any other expression is elaborated at the part's type and compared by normal form. `left`, `right` and `typed` are the builtins only where the module does not bind them, and a builtin's or a constructor's arguments are written out as elaboration requires, a hole aside (E701, E378, E379). A mismatch names the differing part (E477), and a hole inside another function's arguments is refused (E478). Evidence: `cubist-tests/evaluate_patterns.cubist` | L0.1; own pattern contract and L4.1a infrastructure | S |
| L2.9b | Closed truncation witness readout: a closed computable input, a checked error certificate, and the extracted witness's type specified under transported truncations, which its tests include. Native truncation alone supplies no approximation result. **Done** on 2026-10-06: `print(witness(t));`, and the REPL's `witness TERM;`, read the witness off a closed, computable truncation's normal form, `point(w)` under formal compositions, with its type (`web/translator/evaluation.mjs`). A witness under a composition whose type changes is refused (E481), so the witness has the truncated type's own parameter; transported along a path of types, it is of the type at the path's end. A certificate is part of the witness the kernel checked. Evidence: `cubist-tests/truncation_readout.cubist` | Native H1 `Trunc`, K2.5, L0.1 | M |
| L2.10 | Explicit notation views and literals: select a view before elaborating an operator, use declared operand views for literals and subexpressions, and preserve that meaning when printing. `v.(e)` and `use v;`, now one selection form that also works at a file's top level and replaces today's `open` (decided later the same day, with `using v;` dropped), extend explicit structure scope, with qualified operators `a G.(+) b`; existing `open` and section semantics remain compatible during migration. **Direction adopted** in the [notation roadmap](notation.md), with **decisions** recorded on 2026-10-05: no name-based operators or numerals, so that an operator or literal outside any view is an error (L2.10j); `~` for path and coordinate reversal so that `-` is arithmetic, with `@`, `~`, `&` and `|` binding tighter than any view's operator (L2.10i); notation declared as it is used; sections and `open` selecting their model's view, innermost first; literals read by the library's total parsers from their `Lexeme` and checked by evaluation (L2.10c); and a partial field inverse (L2.10k). **L2.10i done** on 2026-10-06: `~p` and `~i` reverse, prefix `-` is refused (E176) and kept for arithmetic, and a historical source is read with `~` for its prefix `-`. **L2.10k done** on 2026-10-06: `Field` states invertibility as a truncated law, which the law check accepts as a declared proposition; `inv` and `mul_inv` are derived by unique choice in any field, and the rationals' inverse computes. **L2.10a done** the same day for `+`, `*`, `<` and `<=`: named notations (`notation nat { … }` in `library/nat.cubist`), complete selections by `use`, `v.(e)` and qualified operators. **L2.10b done** the same day: `-`, `/`, `^`, unary `-`, `>` and `>=`, operand recipes such as `x ^ nat.(n)`, and derived operations in theories (the library's rings get `-x` and `x - y`). **L2.10c done** the same day: numeric tokens, `library/lexemes.cubist`, numeral and literal rules, a theory's `notation numeral`, and the rationals' parser (`rationals.(1/2)`). **L2.10d done** the same day: printing in the selected notation, qualified elsewhere, literals as written. **L2.10e done** the same day: the roadmap's pilots check (`cubist-tests/notation_pilots.cubist`), costing one selection per expression and one `nat.(…)` per natural argument of an ordinary function. **L2.10j done** the same day: every source selects `nat` (or `binary`, the archive's notation for binary literals), and an operator or numeral outside any selection is an error that suggests `use nat;`; L2.10f–h stay deferred. L2.10i comes first; L2.10a–e are the primary slices, beginning with small library pilots; type-based automation needs separate evidence later. L2.10f (large numerals), L2.10g (independent `decide`) and L2.10h (notation rules, proposed) stay deferred | L2.4 | L |
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
tiny theory whose law and homomorphism preservation are checked (L2.4, done:
`cubist-tests/theory_morphisms.cubist`);
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
| L3.4 | Categories in the library ([categories](categories.md)), **proposed** on 2026-10-07: `Precategory(U, V)`, `IsUnivalent`, `Category`, `C.op`, functors, natural transformations, a `category` simp set, and each opted-in theory's `T.cat` | L2.4d, L2.11, L2.12 | M |
| L3.5 | Generic predicates `IsInitial`, `IsTerminal`, `IsLimit`, `IsColimit`, `IsProduct`, `IsPullback`, `IsEqualizer` and their duals for supplied objects/cones, independently of construction opt-ins; `T.IsInitial` specializes the category predicate. Universal constructions as parameterized theories, **proposed**: terminal objects, products, equalizers, pullbacks and generic limits over diagrams that are maps of graphs, finite or infinite, each algebraic (pairing as an operation, computing) and by contractibility (a proposition); colimits as limits in `C.op`, and colimits of types as one higher inductive type over a graph; `ext` into limits; `deriving (limits)` for theories whose limits are computed carrier by carrier | L3.4; L3.1 for the contractibility form | L |
| L3.6 | The abelian tower, **proposed**: `Preadditive(C)` as structure; `IsAdditive`, `IsPreabelian` and `IsAbelian` as propositions; `deriving (… additive …)` up to `abelian` for linear theories, whose other operations return carriers and are additive jointly in their carrier inputs, `AbelianGroup` and `Module(U, R)` first, with `CommRing` and rings without a unit refused; lifting operations through set quotients for cokernels | L3.5; L2.4b for the properties to be propositions | L |

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
  slice, both delivered. A monad's laws are equations in `F(B)`, not in a
  carrier, so L2.4's law check refuses them; L2.4c's theory families,
  decided on 2026-10-05, admit them, so N1 follows L2.4c
  ([computation roadmap](computation-notation-roadmap.md)). No initial
  model or generated structure identity is required.
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

## Runtime evaluation track

Added on 2026-10-07. The [runtime evaluation roadmap](runtime-evaluation-roadmap.md)
owns EVAL0–EVAL8 and the early numerical packages NUM0–NUM2. EVAL0 is
done (2026-10-08): `tools/evaluation-baseline.mjs` records the
[baseline](runtime-evaluation-roadmap.md#measurements), which
`tests/evaluation-baseline.test.mjs` keeps current. No other package is
implemented. The versioned scratch evaluator's prime projections are
feasibility observations, not full normal forms or kernel evidence. This
track is independent of
computation notation N0–N5. Its planned library scope is NUM0–NUM2 and
EVAL7's binary divisibility/search pilot; R1's further order and canonical
presentation work remains deferred.

- EVAL1's removal of redundant REPL self-comparison comes next: in EVAL0's
  baseline it takes 400 of the 435 ms of `evaluate euclid(3)`. EVAL2's
  full-normalization cache can follow independently, with exact keys and
  rollback/compaction coverage.
- Start NUM0/NUM1 early: define explicit `UNat` and canonical `BNat`, direct
  binary arithmetic, their checked commutative-semiring isomorphism and
  `UNat =[U0] BNat` by computational univalence, with transport agreement,
  cancellation and no-zero-divisors. NUM1 also supplies dependent strong
  induction and recursion from all smaller binary values through an H1
  bit-structured Peano view and a `Below` function, with checked coherence
  and computation equations and factorial as a computing example. This
  larger package does not depend on H2's indexed accessibility families.
  When binary naturals become the default `Nat`, the retained equivalence is
  `UNat` ↔ `Nat`. NUM2 builds new `Z` from pairs of `BNat` and new `Q`
  from that integer ring, including literals and numerical casts. Prove
  their ring/domain/field laws and embeddings within the new hierarchy;
  comparison maps and universe paths to the old integers and rationals
  are outside this track. Later numerical constructions default to `BNat`;
  these foundations do not wait for a new runtime evaluator or
  packed-integer specialization.
- NUM2 owns the new carriers and algebraic APIs. The
  [reals roadmap's R1](reals-roadmap.md#milestones) owns their further
  decidable orders, ordered-ring/field laws, `PosRat` and Archimedean
  property. That work targets the new `Z` and `Q` and still awaits first
  action 8's scope decision; it is not a NUM2 prerequisite.
- Design EVAL3's lazy closure evaluator and EVAL4's explicit stack together.
  EVAL5 specifies observation and typed readback; a successful
  `euclid(4).1` does not close the failure of full `euclid(4)`.
- EVAL6's packed binary arithmetic follows NUM0–NUM2 and profiling; EVAL7's
  checked BNat search improvements are a separate computation pilot, keeping
  the archived algorithm fixed for evaluator comparisons and broader
  mathematics paused. EVAL7 supplies its binary divisibility and
  prime-search modules in `library/`, without imports from the archive.
- EVAL8's applicable semantic review, instruction isolation, canonicity and
  resource checks gate production integration. A query result does not
  establish equality merely because its type checks.

## Frontend generation track

**2026-10-09 addition, planned on top of PR #188 at `00d4ecce`.** The
[frontend generation roadmap](frontend-generation.md) uses that PR's
failures as evidence for shared contracts. The
[gap inventory](../reports/frontend-generation-gaps.md) pins eleven remaining
findings (G1–G6 and G8–G12) and distinguishes them from fixed examples,
historical symptoms and L2.6's incomplete planned capabilities. These
packages do not mark implementation complete or resume paused mathematics.

Follow-up FG0–FG5 fixing commits and distinguishing tests are recorded in
the inventory. The [FG6 report](../reports/frontend-generation-fg6.md)
records the implemented deterministic/mutation gate, validation and the
remaining unidentified historical skipped-mutation evidence. No new L2.6
deriving capability is implied by those frontend changes.

| ID | Package and exit evidence | Depends on | Size |
| --- | --- | --- | --- |
| FG0 | Reproductions, public-interface manifests and independent meaning checks; every open gap has an expected outcome | #188's captured-syntax baseline | S |
| FG1 | Shared declaration ownership, dependency state and publication groups; collisions and failures preserve existing checked state | FG0 | L |
| FG2 | Complete declaration telescopes, dependency/support analysis, value/type call classification and notation-scope consolidation; meaning and supported calls survive expansion | FG0; FG1 for publication | L |
| FG3 | Universe inference from complete generated telescopes; Hom/Iso clients and genuine lowering refusals | FG1, FG2 | M |
| FG4 | Checked evidence and recursion state follow scope refinements; eligible wildcard fallback preserves primary errors on failure; nested matches check without new assumptions | FG1, FG2; focused fallback fix can land after FG0 | M |
| FG5 | Separate alias keys, labels and exact source origins; binder/use links, refusal ranges and public interfaces survive transformation | FG0, FG2; FG1 for publication metadata | M |
| FG6 | Deterministic cross-transformation tests, distinguishing mutations and measured resource costs | Starts with FG0; complete gate needs FG1–FG5 | L |

Start FG0 and prioritize G11's silent capture alongside FG1's ownership
fix. G8–G10's focused fixes and regression checks can land on #188 before
the broader dependency/publication work; update their evidence status when
fixed. Complete FG2's call classification (G12) and notation-alias audit.
FG3 and the broader FG4 work follow those contracts; FG5's
focused lint fix can land earlier with its checked-client regression.
FG6 accumulates alongside every slice. The complete gate precedes
publication of new deriving capabilities under L2.4d/L2.6 and extensions
of generated interfaces. It supplements their proof obligations; it does
not delay unrelated fixes or replace uniqueness and universal proofs.

## Release checks and documentation

Every language package includes parser/formatter round trips, original source
spans, generated-term inspection, native acceptance/rejection, and browser/CLI
agreement. Transactions discard failed generated declarations, rules and
signature registrations; import changes invalidate affected caches. Complete
terms contain no unresolved goals or metavariables.

For frontend generation, apply the [FG6 semantic gate](frontend-generation.md#fg6-make-preservation-tests-and-measurements-a-release-gate):
renaming, imports, inheritance, inlining and supported lint rewrites must
preserve the specified interface and meaning. Kernel acceptance alone
does not discharge this obligation. Migrate and review every consumer of a
changed syntax representation, including diagnostics and inspection.

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

Resumed and done on 2026-10-05 ([first actions](#first-actions)): the natural numbers'
arithmetic, quotients, the integers, the rationals as a quotient, and the
algebraic hierarchy from semigroups to fields. The rest of B3 and B4 stays
deferred, except for the new binary foundations explicitly scheduled as
NUM0–NUM2 in the [runtime evaluation track](#runtime-evaluation-track).

Small h-level/equivalence definitions and language acceptance fixtures are
part of their owning language packages. They do not commit to proving all
results from the corresponding library area.

## Planning corrections

**Second revision of 2026-10-05** (against `b6aa6e5`):

- Record L2.4's completion with its review's additions, the library's
  foundations (the previous first actions 1, 2 and 4), the notation
  roadmap's decisions, and the archive baseline at this revision.
- Replace the completed first actions with a sequence led by L2.10i and
  L2.10k, which are small and need no view, then the views' pilots.
- Propose the order on the integers and rationals as library work beyond
  the resumed scope, for the maintainer to accept or defer.

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

Revised again on 2026-10-05, against `066ca77`. Done since the audit:
instruction isolation (I1.2a), H1's release scope and integration, with its
release on 2026-10-02 and its merge into `main`, the checker's retirement
(I1.2b), face restriction (I1.2c), argument inference (L4.1a, L4.1b,
2026-10-04), and the rest of explicit matching with the `cases` migration
(L2.2a, 2026-10-04). On 2026-10-05, the previous revision's first actions
1–4, the notation decisions and the theory syntax revision's:

- **One module for the natural numbers** (#150, #151): `nat`, in today's
  syntax, imported by every module that uses the natural numbers, numerals
  included. The archive's copies of its arithmetic are gone, and so is its
  `sets`, which `hlevels` replaces.
- **Effective quotients** (#152): for an equivalence relation valued in
  propositions, related elements are exactly those with equal classes,
  through `propositions`' `Prop(U)` and propositional extensionality.
- **Core theories, L2.4** (#153–#155): all four slices, with the review's
  additions recorded in L2.4's row.
- **The algebraic hierarchy, the integers and the rationals** (#156–#158):
  `library/algebra.cubist` from `Semigroup` to `Field`, with `Nat`'s two
  monoids; `Z`, pairs of naturals with the same difference, a commutative
  ring with decidable equality; and `Q`, the field of fractions of any
  commutative ring with decidable equality, no zero divisors and zero not
  one, written once in a section and applied to the integers. Every
  operation computes on closed values. The reference documents them (#159).
- **The notation roadmap's decisions** (#160–#162), listed in L2.10's row.
- **The roadmaps refreshed** (#163), and **the theory syntax revision
  decided** (#164), listed in L2.4c's row. Its review made two
  corrections: a monad's family is indexed by sets, so that the identity
  monad is a model, and a set family indexed by a carrier gets no `T.Iso`
  until its round trip, after a transport, is specified.

**2026-10-07 addition:** L2.4d's opt-in and L2.11's propositional-law
check precede publication of L2.6's checked capabilities. L2.12's implicit
operation arguments precede the categorical library L3.4–L3.6. The first
H1 construction may be developed separately, but a type and fold alone
must not register `free` or `initial`. This supplements the ordering below;
the other categorical and homological proposals do not resume paused work.

**2026-10-09 addition:** start [FG0 and FG1](#frontend-generation-track)
from PR #188's remaining failures before extending its generators. The
track's shared contracts and semantic gate precede publication of new
deriving capabilities. This supplements the ordering below; L2.6's
universal-property work remains separately required.

Suggested next, in order:

1. **L2.10i, `~` for reversal (S). Done** on 2026-10-06, in two commits,
   as the retirement of `cases` was: `~p` and `~i` accepted beside `-`,
   and the 25 uses in `library/` and `cubist-tests/` moved, identical by
   `node tools/verify-proof-migration.mjs` while `-` still parsed; then
   `-` refused, with a message naming `~` (E176). The goal printer, the
   tests and the reference's `cubical.html` and `paths.html` moved with
   it.
2. **L2.4c, the theory syntax revision (M).** As
   [decided](core-theories.md#revision-l24c): carriers as fields with an
   h-level, the universe named in the header, `Monoid(U)` as the type of
   models, theory families, the combination of independent theories, and
   qualified operators. First, because L2.10k needs the named universe and
   N1 the families, and because the library's theories are few today.
3. **L2.10k, a partial field inverse (M).** First the gap in theories
   it names that L2.4c leaves: the law check accepts a type declared at
   `prop`, as `Trunc` is. Then `Field` states
   invertibility as a truncated law, `inv` is derived by unique choice,
   the rationals supply the law with `merely`, and `Field.Hom` becomes
   `CommRing`'s. It does not depend on views.
4. **The views' pilots, L2.10a–e (L).** Settle the
   [notation roadmap](notation.md)'s remaining grammar and elaboration
   contracts first, then pilot them on the library: two models on one
   carrier, `Nat`'s two monoids; `integers.(x + y = y + x)`; literals read
   from their `Lexeme` by the library's parsers and checked by evaluation,
   as `rationals.(1/2 + 1/3 = 5/6)`, where `1/2` is one literal; and
   faithful printing. Existing `open` and sections keep their meaning.
5. **L2.10j, retiring name-based operators and numerals (M),** once the
   `nat` view exists: every module that relies on the fallback gains
   `use nat;`, checked while the fallback still works; then an operator
   or numeral outside any view is an error that suggests `use nat;`.
   **Done** on 2026-10-06.
6. **Equivalences, then structure identity (L3.1, L3.2, L2.4b).**
   Composition and the Π, Σ and product equivalences, `equiv_eq`, and the
   `ua` builtin on `ContrEquiv`; then Σ and universe `ext`; then each
   theory's generated `T.equality : (M = N) ≃ T.Iso(M, N)`, beginning with
   groups: the first result to use theories and univalence together.
7. **h-level rules, L2.5b's remainder (M).** `hlevel_rule` registration, so
   that `hlevel` proves a registered carrier, such as `Z` or `Q`, a set and
   fills a model's setness field; then quantified hints, one layer of
   unfolding for registered definitions, `Truncate`, and the inspector's
   record of the witnesses chosen. **Registration, quantified hints and
   setness fields done** on 2026-10-06.
8. **The order on the new numbers (M). Proposed; it extends the resumed
   library scope, so it waits for the maintainer's decision.** Ordered
   commutative rings and fields as theories with `<` and `<=`; the
   NUM2 integers' and rationals' orders, decidable; positive rationals
   `PosRat`; and the Archimedean property with binary natural bounds.
   The [reals roadmap](reals-roadmap.md)'s R1 owns this work, and its R2
   interface needs them; no language package does. Rationals in lowest
   terms, which print reduced, wait for L2.7's canonical quotients.
9. **Runtime evaluation and binary numerical foundations.** The
   [runtime evaluation track](#runtime-evaluation-track) has EVAL0's
   baseline (2026-10-08); it continues with EVAL1's one-pass REPL
   evaluation and NUM0/NUM1's unary/binary foundations and H1 strong
   induction, followed by NUM2's new binary-backed `Z` and `Q`. This
   includes library work and proceeds independently of action 8's proposed
   order extension. The `Nat` spelling decision below gates the public-name
   transition, not these constructions.
10. **Independent language work.** The universal-property contract before
   L2.6 and L2.3's `universal` slice; L1.3's worker cancellation; N0, and
   N1's checked operation and law records on L2.4c's theory families, then
   N2/N4. L2.9a's expected-value patterns and L2.9b's closed witness readout
   are done (2026-10-06, [#181](https://github.com/KanHarI/cubist-math/pull/181)
   and [#182](https://github.com/KanHarI/cubist-math/pull/182)); their
   full-normalization cost is covered by EVAL5. Keep canonical quotient and
   view examples finite and computable.
11. **K2.5's remaining archive remedies,** and in the library one module for
   the classical assumptions over the computing `Trunc`. The two
   H2-dependent tower declarations stay deferred; complete removal of the
   legacy truncation assumptions is not required.
12. **H2, then the H3 research gate.** Specify the representation and
   computation changes (K4.2, K5.2) before implementing them. H2's indexed
   families will need implicit indices, which L4.1b supplies. Keep the full
   Cauchy reals deferred; the reals roadmap's corrected R2 interface and R3
   obligations give later work a usable contract.

Learned-search phases 3–5 may proceed separately; they do not block this
language sequence. H4, E1/E2, trained
search, transport regularity (G4) and interval normalization (G5) keep
their concrete-use and performance gates. Concrete mathematical development
beyond the library's foundations remains paused.

## Open decisions

These wait for the maintainer. Three are needed before the work they name;
the rest stay open without blocking any scheduled slice, whose contract
keeps a conservative behavior until a design is chosen.

**Needed before the named work**

1. **The order on the numbers** (first action 8) extends the resumed
   library scope: ordered commutative rings and fields, NUM2's new integers'
   and rationals' decidable orders, positive rationals and the Archimedean
   property. The reals roadmap's R1 and R2 need it; NUM0–NUM2 and the
   language packages do not.
2. **Whether notation keeps the word "view"**
   ([notation](notation.md#open-questions), question 2), which MMT, OBJ
   and L2.7 use otherwise: before L2.10a, since renaming costs least while
   nothing is implemented.
3. **The public `Nat` transition.** Decide when the binary carrier becomes
   `Nat`, and specify constructor names, notation and imports for existing
   unary clients. Until then, expose explicit `UNat` and `BNat`; new `Z`
   and `Q` use `BNat` regardless of the public spelling. This decision gates
   the alias/import switch, not NUM0–NUM2's construction work.

3. **The composition operator**
   ([categories](categories.md#open-questions), question 1): before
   L2.12's notation acceptance and L3.4. The categorical roadmap's other
   open questions stay with the packages they constrain.

**Open, not blocking**

Each slice ships with the behavior in parentheses until the question is
decided.

- L2.4c's questions ([core theories](core-theories.md#open-questions)):
  - whether the header's universe binder is required (a carrier names a
    universe the header binds);
  - how a qualified operator's operands are read, also notation's
    question 3 (where they stand, as decided);
  - whether a child can drop a parent's notation without giving another
    (it renames it);
  - homomorphisms of carriers with no h-level (none, E817);
  - how an index's evidence is given at a use, as `Nat`'s setness in
    `G.F(Nat)` (the author writes it);
  - the round trip of a set family indexed by a carrier (no `T.Iso`).
- Notation rules, L2.10h, proposed: nothing in L2.10a–e or i–k needs them.
- Whether `do using M` and `match … using view` take `use`'s word
  (notation's question 4): before N2 and L2.7 fix their syntax.
