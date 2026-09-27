# Development roadmaps

These describe the intended developments, their limits, and remaining
obligations. Read the linked checkpoint before resuming work. Do not treat a
target statement or a supplied theorem parameter as an already proved result.

## Plan and designs

- [Work plan](work-plan.md): the staged, dependency-ordered plan across all
  roadmaps. Start here. The active scope is language features and their
  kernel support; concrete mathematical development is paused.
- [Historical plans and specifications](historical/README.md): completed
  work, currently G0. Its specification remains linked as a contract.
- [Higher inductive-inductive types](higher-inductive-types-design.md): the
  adopted kernel design. One signature format covers data, indexed, higher
  and inductive-inductive types, with computability expressible and
  preserved.
- [Language features for theories and inductive declarations](inductive-language-features.md):
  the adopted language proposal: theories, cells, relations and bundles,
  canonical quotients, presentations and derived declarations.
- [Results of the first library](../library-results.md): what the archived
  library established, in mathematical English.
- [Kernel instructions](kernel-instructions.md): the trusted kernel since
  2026-09-26, a THTH-style forward kernel whose rules are instructions.
  Every search decision is in an untrusted driver, and the kernel's state is
  two hash graphs, explorable in the workbench. Every later kernel item is a
  set of instructions.
- [Learned search](learned-search.md): a design for a small policy and value
  network over the kernel's graphs, trained against the instruction kernel,
  that steers the driver's conversion search toward cheaper derivations.

## Language tooling

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
    inductive declarations and pattern matching (7), plus expected-value
    patterns and closed truncation readout from milestone 8.
  - The [concrete implementation plan](proof-ergonomics-implementation-plan.md)
    adds PR-sized steps, lowering contracts, cubical notation proposals, and
    checked current-language sample expansions.
- [HoTT and cubical proof automation](hott-automation-roadmap.md):
  - Delivered: A7 (baseline, regressions and canonicity fixture), the A5
    goal-layer core, and A4/A6 deterministic fuel with residual-goal
    diagnostics; see the
    [checkpoint](../tactical/hott-automation-handoff.md).
  - Planned: remaining goal-layer metadata/clients; folded path operations;
    `Path` induction; type-directed `ext`; transport and path-algebra rules;
    h-levels and their solver; identity systems; dependent paths and
    squares; structure identity and transfer.
  - B0, B2, B5, F3 and A9 are superseded by the kernel's item H and
    ergonomics milestone 7.
- [Kernel extensions for computation](cubical-kernel-roadmap.md): G0 delivered;
  H and the other extensions planned. Each is a set of instructions, governed
  by the requirement that computability is expressible and preserved:
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
