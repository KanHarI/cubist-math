# Development roadmaps

These describe the intended developments, their limits, and remaining
obligations. Read the linked checkpoint before resuming work. Do not treat a
target statement or a supplied theorem parameter as an already proved result.

## Language tooling

- [Simplification and shorter proofs](proof-ergonomics-roadmap.md): checked first slice of `rw`, `calc`, `simp only`, and expected cubical paths, with further argument inference and HoTT/cubical requirements in progress.
  The [concrete implementation plan](proof-ergonomics-implementation-plan.md) adds PR-sized steps, lowering contracts, cubical notation proposals, and checked current-language sample expansions.
- [HoTT and cubical proof automation](hott-automation-roadmap.md): planning only. The follow-on to the ergonomics roadmap: library changes that use existing kernel computation (eliminators with PathP bridges, numeric h-levels, a conversion audit), folded path operations, congruence-line witnesses and deterministic fuel, then goal-derived path induction, type-directed `ext`, transport and path-algebra rules, an h-level solver, identity systems, and filler-based dependent rewriting.

## Mathematics

- [Galois theory](galois-roadmap.md): Artin's theorem and the core finite correspondence are checked; the correspondence takes a supplied algebraically closed target and embedding. Finite index, normal quotient, and bundled homotopy results remain. Infinite extensions are deferred. Read the [Galois checkpoint](../tactical/galois-handoff.md) for the current resumption point.
- [Complex analysis](complex-analysis-roadmap.md): algebraic closure, the residue theorem, and Great Picard. Read the [complex-analysis checkpoint](../tactical/complex_analysis_handoff.md) for the paused state and validation commands.
- [Real numbers](reals-roadmap.md): constructive Dedekind cuts, classical Boolean cuts, and Cauchy quotients. The final section lists the remaining construction proofs; candidate carriers do not yet constitute complete ordered fields.
- [RH and the prime-counting error](rh-prime-counting-roadmap.md): a planned proof that RH for zeta implies a prime-counting error of \(O(\sqrt{x}\log x)\) relative to the logarithmic integral, with the little-o bound as an optional corollary. Includes analytic dependencies and possible uses of homotopy; no implementation has started.

See the [documentation index](../README.md) for supporting notes and guides.
