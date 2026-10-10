# H1 specification: history

The [H1 specification](../h1-signature-specification.md) states H1 as it is.
This file keeps the parts of it that recorded how H1 got there, moved here
on 2026-10-02 as they stood: its status and release record, its review
rounds and decisions, the marker contract of the experimental mode, and
K2.4's representation map. Section numbers, such as 5.7 or Q16, refer to the
specification, except that section 7 and its subsections are below.

## Status and release record

The specification's opening, as it read on 2026-10-02 after the release.
Its dated paragraphs were added at the top as each step happened.

The [release evidence](h1-release-evidence.md) it links now records the
revision merged into `main`: item 5 was run again on 2026-10-03 at
`8229181`, after the refactors of #120–#132, and every check passed. The
first record, of `581e03c`, is that file as commit `cb0b0dd` wrote it.

2026-10-02 release. With checklist items 1–4 approved and item 6 retired as
a gate, the experimental option is removed and default admission granted:
the kernel admits declared types by default (5.7), no CLI, workbench or
program option remains, and results no longer carry the
`kernel extension: H1` marker (6.4). Acceptance case T2 states the
released behaviour. Item 5's run at the release's own revision, `581e03c`,
was recorded the same day, and every check in it passed: the
[release evidence](h1-release-evidence.md).

2026-09-30 implementation update: at the user's request, source checking now
enables H1 by default and imports an ordinary source-defined Nat. W is also
source-defined; both primitive C implementations have been retired. This
changes the deployment default while the mathematical release review below
remains pending. It does not discharge the release checklist. Statements
below about retaining primitive W refer to the earlier implementation; the
[migration record](../h1-program-types.md) describes the current universe limits.

2026-10-01 decisions and update, by the maintainer:

- **Sums stay native.** `A or B` keeps its kernel primitive at every level,
  tier-1 arguments included. The wider retirement of 7.4 and work-plan K2.4c
  no longer covers sums, even if the tier-parametric proposal is adopted.
- **Pushouts are a declared type.** `Pushout` is an ordinary H1 declaration
  with the path constructor `push(c) : inl(f(c)) = inr(g(c))`, in
  [`pushout.cubist`](../../../archive/first-library/pushout.cubist). Its
  primitive formation, constructors, eliminator and computation rules have
  been retired, and their tags and ABI slots reserved, as for Nat and W. So
  the assumed baseline of 4.1 no longer contains pushouts: they are covered
  by the H1 model and canonicity arguments instead. Statements below about
  the native pushout describe the earlier implementation; the
  [migration record](../h1-program-types.md) describes the current API.

Status: approved on 2026-09-27 for experimental implementation; reviewed
against `02a57ef` on 2026-09-28 by the
[work-plan audit](audits/2026-09-28-audit.md). Written on 2026-09-27 as
work-plan items K2.1 (the H1 fragment and its soundness note) and K2.5
(G2's truncation and resizing policy, with its migration ledger). It is the
contract that K2.2 (instructions), K2.3 (driver and bridges), K2.4
(differential fixtures) and L2.1 (the `inductive` declaration) implement,
on the `h1-signatures` branch. Its statuses are distinct:

- **Decided:** every question of section 11, on 2026-09-27.
- **Released** on 2026-10-02: the fragment of sections 1–3 and the
  families of section 5, admitted by default (5.7). Implemented: K2.2's six
  families (ABI 3), K2.3 (section 6), L2.1 (section 9) and L2.2a's first
  `match` slice. Before the release, in the experimental mode of 5.7, every
  result carried the `kernel extension: H1` marker; now none does.
- **Approved:** the checklist's mathematical items. Lemma H2 and the
  critical-pair check on 2026-09-30 (item 2); the model construction, D1,
  D4 and D5, and canonicity on 2026-10-02 (items 1 and 3). They are relative
  to the assumed baseline of 4.1 and to premise P1 of the model draft. Other
  entries of 4.5 keep their status, and implementation and passing tests
  discharge none of them.
- **Migration evidence:** K2.4a's representation option and archive replay
  are implemented, historical evidence since 2026-10-02 rather than a
  release gate (checklist item 6), with the X2 remainder in the
  [differential record](h1-differential-evidence.md). K2.5 has an exact
  ledger verifier and [scoped migrations](../h1-truncation-migration.md).

**Release checklist for finite-level H1.** The experimental option is
removed, and default admission granted, only when every item has evidence
and a review decision. With items 1–4 approved and item 6 retired as a gate,
both were done on 2026-10-02, and item 5's run was repeated at that
revision the same day:

1. D1, D4 and D5 written out and reviewed (4.2, 4.3).
   **Approved on 2026-10-02:** the [model construction](../h1-model.md);
2. Lemma H2's full case analysis, and the critical-pair check of 3.7.
   **Approved on 2026-09-30:** the [case analysis and overlap
   table](h1-critical-pairs.md);
3. canonicity (4.4) reviewed, relative to the assumed baseline of 4.1.
   **Approved on 2026-10-02:** the [canonicity argument](../h1-canonicity.md);
4. the acceptance matrix of 10.10 complete, K10 and K11 included. Every
   case is now traced; X2 retains the remainder listed below;
   `tests/acceptance-matrix.test.mjs` checks the matrix against the tests.
   **Approved on 2026-10-02:** the [matrix](../h1-signature-specification.md#1010-coverage-of-the-acceptance-cases)
   as traced; its X2 remainder belongs to item 6;
5. a recorded run of the whole suite at a pinned revision, repeated at
   the release's own. The first was CI run 36472206548, at `bef00e3` on
   2026-09-28, where all seven jobs passed; the verifier's marker
   comparison (6.4) and the inspection of 6.5 were delivered the same day.
   `node tools/release-evidence.mjs` records such a run: the revision, its
   build stamp, each local check's command and outcome, run in a fresh
   checkout of it, and the jobs of the CI runs dispatched on that commit.
   **Recorded on 2026-10-02** at the release revision `581e03c`: the
   [release evidence](h1-release-evidence.md), where every local check
   passed and all seven jobs of CI run 37028834426, dispatched on that
   commit;
6. K2.4a's differential fixtures X1–X4 and X6–X8. The work plan's
   isolation correction I1.2a, on which 4.1's baseline relies, was
   delivered on 2026-09-28. **Retired as a gate on 2026-10-02:** the
   fixtures were to justify retiring the hand-coded types through τ, but
   Nat and W (2026-09-30) and pushouts (2026-10-01) were retired by
   declaring them in source, and sums stay native. X1–X8 are recorded as
   historical evidence (7.4). Their tests were removed with the historical
   kernel they ran against, later the same day.

The evidence for items 1–3, the mathematical ones, and what a review
decision on each still needs are gathered in the
[review evidence](h1-review-evidence.md) (2026-09-29). Review drafts of the
three arguments followed on 2026-09-30: the [model](../h1-model.md), the
[critical pairs](../h1-critical-pairs.md) and [canonicity](../h1-canonicity.md).
The model and canonicity drafts were revised the same day after their
first review, which found three substantive issues, and again after the
second, on 2026-10-01. The maintainer approved both on 2026-10-02.

Not on the checklist: the classification of each instruction into the
cases (i)–(v) of 2.3. It belongs to the deferred tier-parametric proposal
(Q16), not to the finite-level fragment. Normalization and decidable
conversion are not claimed (4.5); a canonicity fixture is not a proof of
them.

## Revisions after review

A review of the first draft (PR #53) found one blocking and four further
defects. This version corrects them:

- **Level-erased instances** (2.3, 3.1, 5.3, 7.2). The native formers carry
  no level, and the archive relies on it: a generic definition instantiated
  at `U1` accepts a sum built at `U0`. Level-abstracted declared constants
  could not translate that. Instances of a declared sort now carry no level,
  and H1 admits only level-parametric signatures, where this is sound (D9).
- **Path abstraction in boundaries** (1.4). `S2`'s outer endpoints are
  `⟨j⟩ base`, which the first grammar could not generate.
- **Commit keeps signatures** (5.1). `cc_kernel_commit_checkpoint` keeps new
  definitions and relocates their syntax; admitted signatures are kept the
  same way. Only rollback removes them.
- **UU-tier arguments** (2.3, 7.2). Native formers accept them. The first
  revision let every level-parametric signature without a tier-1 constant
  read any tier; the second review narrowed that (below).
- **The ledger's remedies** (8.3, 8.4). Raising the tower's quantifier moves
  membership up a universe each time, and the same holds for the union of
  independent sets. Those remedies are replaced, and the Cauchy root is
  identified as an artifact of a wrapper's fixed universe.
- **Open obligations** (4.3, 4.5) are marked as such for D1, D4, D5 and
  Lemma H2.

A second review, of that revision, found one blocking and two further
defects:

- **Hidden tier bounds** (2.3, 3.1, 5.2, 5.3, D9, Q8, Q16). A signature can
  inherit a level bound from a signature or definition it uses, as `Outer`
  does from `Tag(A : UU0)`, without a tier-1 constant of its own. Instances
  now read finite levels, the range admission checked. That revision let a
  syntactically checked class of tier-parametric signatures read tier-1
  levels; the third review found a hole in the class (below).
- **Levels inside parameter terms** (2.4, D8, Lemma H2). Level substitution
  recurses through parameters, motives and clauses: `Trunc(U(x))` at `0` is
  `Trunc(U(0))`.
- **Propositions against witness types** (8.2, 8.4). `LEM` resizes
  propositions only. Group 7 needed no resizing at all, only double negation
  at `U1`, which a local check on the archive confirms. Groups 4 and 6 now
  name the propositions they resize and keep their witness types.

A third review found that the syntactic class of the second revision still
admitted a hidden bound, in the constructor of a parameter-free signature
(`Outer2` over `Big : UU1 { pack(B : UU0); }`). This version:

- **States the criterion semantically** (2.3): a signature reads tier-1
  levels only if its admission is derivable without the finiteness of its
  level parameters.
- **Checks the derivation, not the text.** Three rules on the recorded
  admission derivation, closed transitively over the signatures it uses,
  parameter-free ones included, implement the criterion. Their sufficiency
  is proved in outline by induction on the derivation; each instruction's
  classification into the proof's cases is a K2.2 review item.
- **Makes the extension optional** (Q16). The recommended first release has
  instances at finite levels only, and keeps the native sum, W and pushout
  instructions for tier-1 arguments, which no archive or library
  declaration uses today. Rejection fixture V19 covers the new
  counterexample.

A fourth review found two consistency defects, now fixed:

- **The walk's coverage** (2.3, 5.2). The closed former judgement ends in
  a prenex of `LevelPi` and `Pi`, in `U(ω)`, which rules 1 and 2 would
  reject. The walk now starts below that prenex, from the parameter types'
  judgements, `U(ℓ)` and the constructor judgements, and still refuses
  level quantification within them.
- **τ's guarantees under the conservative option** (7.2–7.4). They hold
  for finite-tier declarations only. A mixed-tier call, such as
  `big_id(Nat, small)` with `big_id(A : UU0, x : A or A)`, has no image,
  and the migration verifier rejects it (fixture X8). No such call exists
  today.

## Decisions

The user decided every open question on 2026-09-27, and section 11
records each as decided. Q8, Q15, Q16 and Q18 were decided as below;
Q1–Q7, Q9–Q14 and Q17 were accepted as recommended.

- **Q16: finite levels only.** The conservative first release. Instances
  read and carry finite levels. The native sum, W and pushout instructions
  stay for arguments at tier-1 levels, and K2.4 retires only the `Nat`
  instructions. The tier-parametric extension of 2.3 is a later proposal,
  not a pending choice.
- **Q8: per universe parameter.** An erased parameter only bounds parameter
  types, and instances are one term at every universe (D9). A recorded
  parameter occurs in a constructor type or cannot be read; instances
  carry it, and are distinct at different levels, as standard universe
  polymorphism (D8). Admission classifies each parameter by an occurrence
  check, and the kernel checks the classification (1.1, 5.2).
- **Q15: level-dependent signatures are admitted,** with the parameter
  recorded. `inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }`
  checks.
- **Header universes** (9). The result position after the colon accepts a
  universe wherever it accepts `type`, as in `inductive Flag : U1 { … }`,
  `: next(U)`, or `: prop U` together with an h-level. A written universe
  is the declared level, checked as an upper bound; without one, the least
  level is inferred. When in doubt, the user writes the universe.
- **Q18: truncation levels in HoTT's numbering.** A sort may be truncated
  at any level `n ≥ -1`, written `trunc(n)`; `prop` is `trunc(-1)`, `set` is
  `trunc(0)`, and `type` is untruncated (1.6). The header words `type`,
  `set`, `prop` and `trunc` are contextual: keywords only in the result
  position, ordinary names elsewhere (9).

## Before the release: the marker contract (6.4)

What the specification's 6.4 required while H1 was experimental. Since the
release no result carries the marker.

### 6.4 The `kernel extension: H1` marker

- A declaration whose checked term or type mentions a sort, constructor or
  eliminator of a signature admitted in experimental mode carries the marker.
  It propagates through definitions, as non-computing dependencies do, and
  is tracked separately from them.
- `computable def` accepts it. `inspect`, the CLI and the workbench list it
  apart from assumptions. The migration verifier must compare it too: the
  marker is not an axiom, so an `axioms` comparison cannot establish this
  contract.
- Tests: direct use; use through a definition; `computable` with the marker
  accepted; `computable` with the marker and `LEM` rejected, naming `LEM`;
  the marker absent once H1 is on by default.

**Implementation.** The elaborator computes each result's extensions beside
its assumptions (`extensionsOf` in `web/cubical-elaborator.mjs`): an
instance or eliminator of a signature the kernel admitted experimentally,
or a definition that carries the marker. The program reports them as
`extensions`, apart from `axioms`. The CLI's `inspect` prints
"kernel extension: H1", and the workbench shows it beside the axioms used.
`computable` reads only the assumptions. `tests/inductive-declarations.test.mjs`
covered the first four tests before the release. Since the release of
2026-10-02 no signature is admitted experimentally, so no result carries the
marker: the same tests now check the last, the marker absent with H1 on by
default, and `computable` still refuses an assumption, naming it. The
machinery stays for any later extension under review.
The migration verifier (`tools/proof-migration.mjs` and
`tools/verify-proof-migration.mjs`) compares each declaration's
`extensions` apart from its `axioms`, and refuses a migration that adds or
removes one (`Kernel extensions changed: none -> H1`, before the release);
until K2.3 it compared `axioms` only (audit of 2026-09-28, finding 7). It
does not yet compare a module that declares a type: the edited copy's
signature is another one, since signatures are generative (Q10), so such a
declaration is refused by name. Comparing signatures, and mapping the edited
copy's onto the original's when their normal forms agree, is K2.4a's
tooling. `tests/proof-migration.test.mjs` covers both.

## Before the release: the open obligations (4.5)

The status paragraph that followed the table of 4.5.

**Status on 2026-09-28.** No open obligation above has been discharged
since the approval of 2026-09-27; the isolation defect is an implementation
fix, not one of them. The implementation's tests are evidence for the
specified behaviour, not for these claims, and the header's release
checklist maps each to its evidence and review decision. On 2026-09-30 the
maintainer approved Lemma H2 and the critical-pair check (checklist item 2),
and on 2026-10-02 the model (D1, D4, D5) and canonicity (items 1 and 3).

## 7. K2.4: representation map and differential contract

### 7.1 The declared counterparts

| Native | Declared | Notes |
| --- | --- | --- |
| `Nat`, `zero`, `succ(n)` | `N : U(0)`; `zero`; `succ(n : s)` | |
| `NatRec(M, z, s, n)` | `elim_{M, [z, s]}(n)` | the native step is `Π (n). Π (h : M(n)). M(succ(n))`, the clause type |
| `Sum(A, B)`, `inl`, `inr` | `Plus(A, B)`; `inl(a : A)`, `inr(b : B)` | no level, as native |
| `SumRec(M, l, r, v)` | `elim_{M, [l, r]}(v)` | |
| `W(x : L). B`, `sup(l, c)` | `Tree(L, λ x. B)`; `sup(l : L, c : Π (b : B(l)). s)` | the arity is `(λ x. B)(l)`, one `Beta` from `B[l/x]` |
| `WRec(M, step, v)` | `elim_{M, [step]}(v)` | same clause shape up to that `Beta` |
| `Pushout(C, A, B, m)` and its points and paths | `Push(C, A, B, m)`; `inl`, `inr`, `push(c) : Path(s, inl(fst(m)(c)), inr(snd(m)(c)))` | one maps parameter, as native; `push^r(c)` is `push(c) @ r` |
| `PushElim(M, l, r, b)` | `λ (z). elim_{M, [l, r, b]}(z)` | native is unapplied; `App(PushElim, z)` maps to the saturated eliminator |
| `HComp`, `Trans` at a pushout | the same nodes at `Push` | |

`Unit`, `Void` and their eliminators are not in K2.4's oracle. They may be
declared for comparison; retiring them is a separate decision (Q11).

### 7.2 The translation τ

- τ is a map on terms. Native formers carry no level, and the K2.4
  counterparts have only erased parameters, so their instances carry none
  either (3.1). τ adds no level and involves no coercion or lifting: `τ(Sum(A, B)) = Plus(τ(A), τ(B))`. τ is the identity on every
  other node.
- **Native and declared forms are not convertible.** `Nat` and `N` are
  different types. No conversion rule, no `Lift` and no coercion relates
  them, and a term mixing them is a type error. Migration is a rewrite by
  τ, checked by the strict migration verifier.
- **Native equalities across universes, at finite levels.** A native term
  used at several universes is one term, and so is its image. In the
  example of 2.3, `small : Nat or Nat` built at `U0` and passed to
  `sum_id(U1, Nat, …)` translates to `small : Plus(N, N)` passed where
  `sum_id`'s parameter type `A or A` has become `Plus(A, A)` with `A := N`.
  The two types are the same term, `Plus(N, N)`, so the application checks,
  as native. A native `Lift` translates to a `Lift` of the image, with the
  same levels.

A native former may occur at an argument in a tier-1 universe, and Q16
decided that instances read finite levels only. Call a declaration
*finite-tier* when neither it nor anything it uses, transitively, contains
a native sum, W type or pushout whose instance would read a tier-1 level.
The K2.4 counterparts have only erased parameters, so τ never needs a
recorded level.

- τ keeps each native sum, W type or pushout whose instance would read a
  tier-1 level, and maps every other occurrence; `Nat` has no parameters
  and always maps. Which occurrences stay native depends on the levels in
  the derivation. So τ commutes with substitution only on finite-tier
  declarations, where every level read stays finite before and after
  substitution, and its guarantees are stated for them only:
  - on finite-tier declarations, τ preserves typing and conversion, native
    equalities across universes and `Lift`, as above;
  - a declaration that is not finite-tier keeps its tier-1 occurrences
    native. A *mixed-tier call*, which passes a finite-tier term where a
    native tier-1 type is expected, has no image. For example:

    ```text
    def big_id(A : UU0, x : A or A) : A or A := x;
    def small : Nat or Nat := left(0);
    def call := big_id(Nat, small);
    ```

    `call` checks natively. After τ, `big_id`'s parameter type stays the
    native `A or A`, which becomes `Nat or Nat` with `Nat` mapped to `N`,
    while `small` has type `Plus(N, N)`. The application fails, and the
    migration verifier reports it; it does not migrate the declaration in
    part (X8);
  - no archive or library declaration uses a tier-1 universe as a type:
    all 43 archive mentions of `UU0`, and the library's 4, are universe
    binders `U < UU0`. So every existing declaration is finite-tier, and
    no mixed-tier call exists.
- If the later tier-parametric proposal is adopted, the four counterparts
  qualify: their derivations use only their parameters, universes at their
  level parameters, `Π`, `Σ`, projections and path types. τ then becomes
  purely syntactic and total, commuting with binders, substitution, level
  substitution and interval substitution everywhere, and
  `def big_sum(A, B : UU0) : UU0 := A or B;` becomes `Plus(A, B)`, reading
  `ω`, in `UU0`.

X1–X3 test the preservation rule by rule, and X4 and X6–X8 test it on the
archive and on the examples above.

### 7.3 Differential fixtures

| ID | Comparison | Pass condition |
| --- | --- | --- |
| X1 | Every `Nat`, sum, W and pushout case of `kernel/tests/test_instructions.c`, replayed through τ with the declared signatures | Same verdict; accepted types related by τ, up to the W arity's `Beta` |
| X2 | Weak head and normal forms of the terms those cases derive, and of each archive definition's value | `τ(nf(t))` is alpha-equal to `nf(τ(t))`, up to that `Beta` |
| X3 | Composition, homogeneous composition and transport at each type, including pushout bridges | Reducts related by τ |
| X4 | The archive, elaborated with declared forms for the four types (a driver option) | 0 gaps; every stored definition derives again; each declaration's assumptions unchanged; canonicity fixture and `evaluate` results equal |
| X5 | Cost of X4 against the native run: archive check time, re-derivation time, kernel steps, arena peak | Recorded with revision, machine and limits |
| X6 | Native terms used at two finite universes: `sum_id(U1, Nat, small)` of 2.3, and the same with W, pushout and `Nat`-valued generic definitions instantiated at `U2` | Under both options, native and image both check; the image is one instance term at both universes |
| X7 | Native formers at UU-tier arguments: `big_sum`, and a W type and a pushout over types in `UU0` | τ leaves them native and they check unchanged (Q16). Under the later proposal, native and image would both check, the image in `UU0` |
| X8 | A mixed-tier call: `big_id(Nat, small)` of 7.2, and the same through a W type and a pushout | The image fails to check, and the migration verifier rejects the declaration, naming the call (Q16). Under the later proposal, native and image would both check |

### 7.4 Retirement criterion

The hand-coded instructions retire in one change when:

1. X1–X4 and X6–X8 pass;
2. X5's gap is recorded, and either accepted by the maintainer or closed by
   specialised reduction paths for hot signatures (Q14);
3. the archive is migrated by τ under the strict verifier, with every
   public type equal after τ and every assumption list unchanged. This
   requires every archive declaration to be finite-tier (7.2), which they
   all are today; a declaration that is not is left on native formers and
   reported, not migrated in part.

As Q16 decided, the change removes the `Nat` instructions only: `Nat`,
`Zero`, `Succ` and `NatElim`, and their node kinds, whose tags stay
reserved; the ABI version changes. The sum, W and pushout instructions stay
for arguments at tier-1 levels, and the elaborator emits the declared forms
everywhere else. They stay trusted code, and X1–X3 stay as their regression
tests. A native and a declared sum of the same components are then
different types, so τ's guarantees cover finite-tier declarations only, and
a mixed-tier call has no image (7.2, X8). Nothing does that today.

If the later tier-parametric proposal is adopted, a further change removes
`Sum`, `Inject`, `SumElim`, `W`, `Sup`, `WElim`, `Pushout`, `PushPoint`,
`PushPath` and `PushElim`, without changing any finite-level term.

`Unit` and `Void` stay (Q11).

**Status on 2026-09-28.** No X fixture, no τ driver option and no cost
record exists. The work plan schedules them as K2.4a, the `Nat` retirement
above as K2.4b, and the wider retirement of the previous paragraph as
K2.4c, deferred with the tier-parametric proposal. At the source boundary,
a program with a mixed-tier call keeps its native formers and the verifier
reports it; it is never migrated in part. The archive coverage run is
compatibility evidence for the native forms, not X4.

**Decision on 2026-10-02.** The differential fixtures no longer gate the
release (checklist item 6). Their purpose was to justify retiring the
hand-coded instructions through τ, under the criterion above. Instead Nat
and W (2026-09-30) and pushouts (2026-10-01) were retired by declaring them
in source, and sums stay native at every level. So no shipped term passes
through τ, and X1–X8 are kept as historical evidence for those retirements.
Their tests were removed later that day, with the pinned historical kernel
they compared against, the representation option and τ itself:

- X2's literal criterion is left as written. Its counterexample, the
  η-contracted image of a sum eliminator, concerns only τ's declared
  stand-in for sums, which nothing uses; the two forms are convertible.
- X4's purpose, that the archive still checks, is served for the current
  kernel by G3's corpus test, which checks every archive declaration in CI.
- X5's cost records stay as observations.
