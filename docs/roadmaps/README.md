# Development roadmaps

These describe the intended developments, their limits, and remaining
obligations. Read the linked checkpoint before resuming work. Do not treat a
target statement or a supplied theorem parameter as an already proved result.

## Language tooling

- [Simplification and shorter proofs](proof-ergonomics-roadmap.md): first release delivered: `rw`, `calc`, `rfl`, `simp`/`simpa` with registered rule sets and conditional rules, and cubical path shorthand. Remaining here: argument inference, `apply`/`refine`, and structure and notation features.
  The [concrete implementation plan](proof-ergonomics-implementation-plan.md) adds PR-sized steps, lowering contracts, cubical notation proposals, and checked current-language sample expansions.
- [HoTT and cubical proof automation](hott-automation-roadmap.md): A7 (baseline, regressions and canonicity fixture) is delivered; see the [checkpoint](../tactical/hott-automation-handoff.md). The rest is planned. The follow-on to the ergonomics roadmap, owning its remaining dependent, cubical and induction work and the shared goal, fuel and diagnostics infrastructure: library changes that use existing kernel computation (eliminators with PathP bridges, numeric h-levels, a conversion audit), folded path operations, congruence-line witnesses and deterministic fuel, then goal-derived path induction, type-directed `ext`, transport and path-algebra rules, an h-level solver, identity systems, and filler-based dependent rewriting.
- [Kernel extensions for computation](cubical-kernel-roadmap.md): planning only. Changes to the trusted kernel, governed by the requirement that every result using no truncation or other assumption computes: computational truncation and quotients first, then resizing, certified interval normalization, closed-type regularity and an optional strict-J identity type.

## Mathematics

- [Galois theory](galois-roadmap.md): Artin's theorem and the core finite correspondence are checked; the correspondence takes a supplied algebraically closed target and embedding. Finite index, normal quotient, and bundled homotopy results remain. Infinite extensions are deferred. Read the [Galois checkpoint](../tactical/galois-handoff.md) for the current resumption point.
- [Complex analysis](complex-analysis-roadmap.md): algebraic closure, the residue theorem, and Great Picard. Read the [complex-analysis checkpoint](../tactical/complex_analysis_handoff.md) for the paused state and validation commands.
- [Real numbers](reals-roadmap.md): constructive Dedekind cuts, classical Boolean cuts, and Cauchy quotients. The final section lists the remaining construction proofs; candidate carriers do not yet constitute complete ordered fields.
- [RH and the prime-counting error](rh-prime-counting-roadmap.md): a planned proof that RH for zeta implies a prime-counting error of \(O(\sqrt{x}\log x)\) relative to the logarithmic integral, with the little-o bound as an optional corollary. Includes analytic dependencies and possible uses of homotopy; no implementation has started.

See the [documentation index](../README.md) for supporting notes and guides.
