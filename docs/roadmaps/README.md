# Development roadmaps

These describe the intended developments, their limits, and remaining
obligations. Read the linked checkpoint before resuming work. Do not treat a
target statement or a supplied theorem parameter as an already proved result.

## At a glance

Revised on 2026-10-05, after PR #164; the runtime and numerical track was
added on 2026-10-07. The [work plan](work-plan.md) is the scheduling
authority; this summarizes it.

- **Done.**
  - **Kernel.** The trusted checker is the instruction kernel, with every
    search decision in an untrusted driver; the term checker is retired.
    Universe-generic checking (G0) is done.
  - **Inductive types.** H1, released on 2026-10-02: one-sort and higher
    inductive declarations, `match`, structural recursion and truncation
    clauses.
  - **Proof ergonomics.** `rw`, `calc`, `simp`, `let`, holes, implicit
    parameters, argument inference, and `hlevel`'s first slice.
  - **Core theories (L2.4).** Theories, models, `open`, sections,
    `extends`, `Hom` and `Iso`.
  - **The library's foundations.** `nat`, effective quotients, the algebraic
    hierarchy, the integers and the rationals, h-levels and univalence.
    Every archived declaration still checks.
- **Decided, not implemented.**
  - **The theory syntax revision (L2.4c).** `M : set U` in place of
    `sort`, the universe in the header, `G : Monoid(U0)`, theory families
    (a monad on sets), relations as families of propositions, homomorphisms
    only where they compose, and independent theories combined unchanged.
  - **Notation (L2.10).** `~` for reversal, one selection form `use` in
    place of `open`, qualified operators `a G.(+) b`, explicit views,
    literals read by the library's parsers, and a partial field inverse.
- **Next,** in the work plan's [first actions](work-plan.md#first-actions):
  1. `~` for reversal (L2.10i);
  2. the theory syntax revision (L2.4c);
  3. the partial field inverse (L2.10k);
  4. the views' pilots (L2.10a–e);
  5. `use nat;` in place of name-based operators and numerals (L2.10j);
  6. equivalences, then structure identity (L3.1, L3.2, L2.4b);
  7. the rest of the h-level solver (L2.5b);
  8. the order on NUM2's new numbers, if the maintainer extends the library's
     scope;
  9. runtime evaluation and binary numerical foundations (EVAL0–EVAL8,
     NUM0–NUM2), including H1 strong induction and the new `Z` and `Q`;
  10. independent language work, monadic `do` and arrows (N0–N4) among it;
  11. K2.5's archive remedies;
  12. H2's indexed families, then the H3 research gate.
- **Later.**
  - Indexed declarations (stage 4, H2) and inductive-inductive ones
    (stage 5, H3).
  - The rest of HoTT automation: `Path` induction, `ext`, transport rules
    and identity systems.
  - Learned search may proceed at any time; nothing waits on it.
- **Paused.** Galois theory, complex analysis, RH and the reals. The reals
  need the order on the numbers first, and the Cauchy reals H3 too. The
  first library in `archive/` is a reference.
- **Open decisions** are listed in the work plan's
  [open decisions](work-plan.md#open-decisions).

## Plan and designs

- [Work plan](work-plan.md): the staged, dependency-ordered plan across all
  roadmaps. Start here. The active scope is language features and their
  kernel support, and since 2026-10-05 the library's foundations: the
  natural numbers, quotients, the integers and rationals, and the algebraic
  hierarchy, all done that day. Its first actions suggest what comes next,
  starting with `~` for reversal and the theory syntax revision, and its
  open decisions list what waits for the maintainer. Other mathematical
  development is paused.
- [Work-plan audit of 2026-09-28](audits/2026-09-28-audit.md): the baseline
  revision (`02a57ef`) and findings behind the current statuses, including
  the instruction-isolation defect, corrected the same day (work-plan I1.2a).
- [Historical plans and specifications](historical/README.md): completed
  work, currently G0. Its specification remains linked as a contract.
- [Higher inductive-inductive types](higher-inductive-types-design.md): the
  adopted kernel design. One signature format covers data, indexed, higher
  and inductive-inductive types, with computability expressible and
  preserved.
- [H1 specification](h1-signature-specification.md): the design's first
  stage, one-sort data and higher inductive types (K2.1), with G2's
  truncation and resizing policy and its migration ledger (K2.5).
  Implemented (K2.2, K2.3, L2.1, L2.2a) and released on 2026-10-02 after
  review of its model, critical pairs and canonicity. Its
  [history](h1-history.md) holds the release checklist and its record, the
  review rounds and the retired differential contract.
- [Language features for theories and inductive declarations](inductive-language-features.md):
  the adopted language proposal: theories, cells, relations and bundles,
  canonical quotients, presentations and derived declarations. One-sort
  `inductive`, explicit `match` and `obligations` are released with H1 on
  2026-10-02, and core theories (L2.4) on 2026-10-05; the rest is proposed,
  with three promises corrected by the audit.
- [Notation views and literals](notation.md): work-plan L2.10's roadmap for explicit
  notation views, declared operand views, literals read by the library's
  parsers and faithful printing, without instance search. The direction and
  its decisions are recorded: no name-based operators or numerals, `~` for
  reversal with the cubical operators tightest, notation declared as used,
  one selection form, `use`, which replaces `open`, with sections, and
  qualified operators such as `a G.(+) b`, `Lexeme` literals and a partial
  field inverse. Notation rules remain open, and the remaining grammar and
  elaboration contracts are draft.
- [Core theories](core-theories.md): the contract of work-plan L2.4,
  theory declarations, models, scoped notation, sections, extension,
  homomorphisms and isomorphisms, specified and implemented on 2026-10-05.
  The library's algebraic hierarchy is written in it. A revision, L2.4c,
  is decided: `M : set U` in place of `sort`, the universe named in the
  header, `Monoid(U)` as the type of models, theory families, and
  independent theories combined without changing either.
- [Results of the first library](../library-results.md): what the archived
  library established, in mathematical English.
- [Kernel instructions](kernel-instructions.md): the trusted kernel since
  2026-09-26, a THTH-style forward kernel whose rules are instructions.
  Every search decision is in an untrusted driver, and the kernel's state is
  two hash graphs, explorable in the workbench. Every later kernel item is a
  set of instructions. The audit of 2026-09-28 found the separation from
  the old conversion checker incomplete; work-plan I1.2a corrected it the same
  day.
- [Learned search](learned-search.md): a design for a small policy and value
  network over the kernel's graphs, trained against the instruction kernel,
  that steers the driver's conversion search toward cheaper derivations.

## Language tooling

- [Mathematical proof concision](vision/mathematical-proof-concision.md): the
  eventual language goal, Galois and contour evidence, and proposed
  acceptance criteria for expressing complete mathematical arguments.
- [Language enhancement proposals](language-enhancement-proposals.md):
  considered and deferred features, each with what would justify it: level
  constraints (E1) and generic definitions at tier 1 (E2).
- [Computation notation: monadic do and arrows](computation-notation-roadmap.md):
  planned explicit computation blocks, checked monad and arrow interfaces,
  mathematical examples, and staged elaboration without new kernel rules.
- [Runtime evaluation and binary numerical foundations](runtime-evaluation-roadmap.md):
  proposed after the `euclid(4)` syntax-depth failure, with EVAL0's
  recorded measurement baseline done: one-pass REPL evaluation,
  normalization caches, lazy closures, an explicit evaluation stack, typed
  readback and checked search improvements. Early numerical
  foundations define `UNat` and `BNat`, prove their semiring isomorphism
  and equality in `U0` with transport laws, and provide strong induction
  and recursion over smaller binary values. New `Z`, `Q` and later
  numerical constructions use binary naturals, with checked algebraic laws.
  Separates prime projection, lazy observation and full normalization, with
  semantic review and resource limits governing integration.
- [Simplification and shorter proofs](proof-ergonomics-roadmap.md):
  - Delivered: `rw`, `calc`, `rfl`, `simp`/`simpa` with registered rule sets
    and conditional rules, cubical path shorthand, dependency tracking,
    `computable` and exact-value `evaluate`.
  - Delivered since: argument inference and implicit parameters (5,
    2026-10-04; `apply` and `refine` withdrawn), explicit `match` with
    several values and nested patterns (7), and core theories, notation and
    sections (6, 2026-10-05).
  - Remaining: initial and free models, algebraic normalization and
    structure identity (6), the rest of inductive declarations and pattern
    matching (7), plus expected-value patterns and closed truncation readout
    from milestone 8.
  - The [concrete implementation plan](proof-ergonomics-implementation-plan.md)
    adds PR-sized steps, lowering contracts, cubical notation proposals, and
    checked current-language sample expansions.
- [HoTT and cubical proof automation](hott-automation-roadmap.md):
  - Delivered: A7 (baseline, regressions and canonicity fixture), the A5
    goal-layer core, A4/A6 deterministic fuel with residual-goal
    diagnostics, D0a's h-level definitions and the first slice of D1's
    `hlevel` solver; see the
    [checkpoint](../tactical/hott-automation-handoff.md).
  - Planned: remaining goal-layer metadata/clients; folded path operations;
    `Path` induction; type-directed `ext`; transport and path-algebra rules;
    the rest of the h-level solver; identity systems; dependent paths and
    squares; structure identity and transfer.
  - B0, B2, B5, F3 and A9 are superseded by the kernel's item H and
    ergonomics milestone 7.
- [Kernel extensions for computation](cubical-kernel-roadmap.md): G0 delivered;
  H1 released on 2026-10-02 after its review; H2–H4 and the other
  extensions planned. Each is a set of instructions, governed by the
  requirement that computability is expressible and preserved:
  - G0, universe-generic checking over tiered universes (done: K1.2–K1.4 and
    L1.1);
  - H1–H4, one signature mechanism for inductive, indexed, higher and
    inductive-inductive types;
  - G2's resizing policy, certified interval normalization and optional
    transport regularity.

## Mathematics

The first library is archived. The Galois, complex-analysis and RH roadmaps
describe unfinished developments in it. They and the broad library rebuild
remain paused while language work proceeds. Language milestones do not
automatically resume mathematics; the [work plan](work-plan.md) retains the
deferred backlog.

- [Galois theory](galois-roadmap.md): Artin's theorem and the core finite
  correspondence were checked in the first library. The correspondence takes
  a supplied algebraically closed target and embedding. Read the
  [Galois checkpoint](../tactical/galois-handoff.md).
- [Complex analysis](complex-analysis-roadmap.md): algebraic closure, the
  residue theorem, and Great Picard. Read the
  [complex-analysis checkpoint](../tactical/complex_analysis_handoff.md).
- [Real numbers](reals-roadmap.md): the rebuild's number systems. The
  library's integers and rationals, done on 2026-10-05, are quotients: pairs
  of naturals by their difference, and the field of fractions. Reals are the
  Cauchy completion (kernel H3), with Dedekind reals as the fallback; both
  need the rationals' order first. The first library's constructions are
  described as archived.
- [RH and the prime-counting error](rh-prime-counting-roadmap.md): a planned
  proof that RH for zeta implies a prime-counting error of
  \(O(\sqrt{x}\log x)\) relative to the logarithmic integral. Planning only.

See the [documentation index](../README.md) for supporting notes and guides.
