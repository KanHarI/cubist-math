# Development roadmaps

These describe the intended developments, their limits, and remaining
obligations. Read the linked checkpoint before resuming work. Do not treat a
target statement or a supplied theorem parameter as an already proved result.

## Plan and designs

- [Work plan](work-plan.md): the staged, dependency-ordered plan across all
  roadmaps. Start here. The active scope is language features and their
  kernel support, and since 2026-10-05 the library's foundations: the
  natural numbers, quotients, the integers and rationals, and the algebraic
  hierarchy. Other mathematical development is paused.
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
  `inductive` and explicit `match` are released with H1 on 2026-10-02; the
  rest is proposed, with three promises corrected by the audit.
- [Notation views and literals](notation.md): work-plan L2.10's roadmap for explicit
  notation views, declared operand views, literals read by the library's
  parsers and faithful printing, without instance search. The direction and
  its decisions are recorded: no name-based operators or numerals, `~` for
  reversal with the cubical operators tightest, notation declared as used,
  sections and `open` as view selections, `Lexeme` literals and a partial
  field inverse. Notation rules remain open, and the remaining grammar and
  elaboration contracts are draft.
- [Core theories](core-theories.md): the contract of work-plan L2.4,
  theory declarations, models, scoped notation, sections, extension,
  homomorphisms and isomorphisms, specified on 2026-10-05.
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
- [Simplification and shorter proofs](proof-ergonomics-roadmap.md):
  - Delivered: `rw`, `calc`, `rfl`, `simp`/`simpa` with registered rule sets
    and conditional rules, cubical path shorthand, dependency tracking,
    `computable` and exact-value `evaluate`.
  - Remaining: argument inference and `apply`/`refine` (5), theories (6),
    the rest of inductive declarations and pattern matching (7), whose
    one-sort declarations and explicit `match` were released with H1 on
    2026-10-02, plus expected-value patterns and closed truncation readout
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
- [Real numbers](reals-roadmap.md): the rebuild's number systems. Integers
  are an inductive type, rationals a canonical quotient, and reals the Cauchy
  completion (kernel H3), with Dedekind reals as the fallback. The first
  library's constructions are described as archived.
- [RH and the prime-counting error](rh-prime-counting-roadmap.md): a planned
  proof that RH for zeta implies a prime-counting error of
  \(O(\sqrt{x}\log x)\) relative to the logarithmic integral. Planning only.

See the [documentation index](../README.md) for supporting notes and guides.
