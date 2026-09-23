# Development roadmaps

These describe the intended developments, their limits, and remaining
obligations. Read the linked checkpoint before resuming work. Do not treat a
target statement or a supplied theorem parameter as an already proved result.

## Language tooling

- [Simplification and shorter proofs](proof-ergonomics-roadmap.md): staged `rw`, `calc`, `simp`, argument inference, and other ways to reduce verbosity, with HoTT and cubical requirements. Planning only; no implementation is claimed.

## Mathematics

- [Galois theory](galois-roadmap.md): finite Galois theory and its homotopy interpretation. Infinite extensions are deferred. Read the [Galois checkpoint](../tactical/galois-handoff.md) for the current resumption point.
- [Complex analysis](complex-analysis-roadmap.md): algebraic closure, the residue theorem, and Great Picard. Read the [complex-analysis checkpoint](../tactical/complex_analysis_handoff.md) for the paused state and validation commands.
- [Real numbers](reals-roadmap.md): constructive Dedekind cuts, classical Boolean cuts, and Cauchy quotients. The final section lists the remaining construction proofs; candidate carriers do not yet constitute complete ordered fields.
- [RH and the prime-counting error](rh-prime-counting-roadmap.md): a planned proof that RH for zeta implies a prime-counting error of \(O(\sqrt{x}\log x)\) relative to the logarithmic integral, with the little-o bound as an optional corollary. Includes analytic dependencies and possible uses of homotopy; no implementation has started.

See the [documentation index](../README.md) for supporting notes and guides.
