# Work-plan history through 2026-10-05

Historical snapshot of the revision notes and superseded first-action list
at `cb525f07`. Package IDs and relative links refer to the active
[work plan](../work-plan.md), which owns current status and scheduling.
The dates and instructions below record earlier decisions, not new work.

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
specify L2.4 in [core theories](../core-theories.md) and schedule it before the
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

Suggested next, in order:

1. **L2.10i, `~` for reversal (S). Done** on 2026-10-06, in two commits,
   as the retirement of `cases` was: `~p` and `~i` accepted beside `-`,
   and the 25 uses in `library/` and `cubist-tests/` moved, identical by
   `node tools/verify-proof-migration.mjs` while `-` still parsed; then
   `-` refused, with a message naming `~` (E176). The goal printer, the
   tests and the reference's `cubical.html` and `paths.html` moved with
   it.
2. **L2.4c, the theory syntax revision (M).** As
   [decided](../core-theories.md#revision-l24c): carriers as fields with an
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
   [notation roadmap](../notation.md)'s remaining grammar and elaboration
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
   The [reals roadmap](../reals-roadmap.md)'s R1 owns this work, and its R2
   interface needs them; no language package does. Rationals in lowest
   terms, which print reduced, wait for L2.7's canonical quotients.
9. **Runtime evaluation and binary numerical foundations.** The
   [runtime evaluation track](../work-plan.md#runtime-evaluation-track) has EVAL0's
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
