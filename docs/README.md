# Documentation and resumption guide

Read the relevant roadmap and checkpoint before extending a mathematical
development. Roadmaps describe goals and boundaries; tactical notes explain the
current implementation, verification commands, and next steps. Check statements
against the current source: some notes retain historical implementation details.
Moving these documents does not change their recorded status or resume paused work.

## Mathematical roadmaps

| Development | Roadmap | Checkpoint and supporting notes |
| --- | --- | --- |
| Galois theory | [Finite Galois development](roadmaps/galois-roadmap.md) | [Resumption checkpoint](tactical/galois-handoff.md), [symmetries as loops](tactical/galois.md), [polynomial algebra](tactical/polynomial-algebra.md), [finite dimension](tactical/finite-dimension.md) |
| Complex analysis | [Algebraic closure, residues, and Picard](roadmaps/complex-analysis-roadmap.md) | [Paused-development checkpoint](tactical/complex_analysis_handoff.md), [complex curves](tactical/complex_curves.md), [limits](tactical/analysis_limits.md) |
| Real numbers | [Real-number constructions](roadmaps/reals-roadmap.md) | The roadmap includes the shared interface, checked constructions, assumptions, and remaining construction proofs. |
| Analytic number theory | [RH and prime-counting error](roadmaps/rh-prime-counting-roadmap.md) | Planning only: precise conditional statement, analytic dependencies, and potential homotopy interpretations. No proof implementation or tactical checkpoint yet. |

## Language tooling roadmap

- [Simplification and shorter proofs](roadmaps/proof-ergonomics-roadmap.md): first release of explicit rewriting, calculations, `simp`/`simpa` and cubical path syntax delivered; argument inference and structure work remain.
  See the [implementation plan](roadmaps/proof-ergonomics-implementation-plan.md) and [checked/proposed examples](examples/proof-ergonomics/README.md) for concrete work packages and cubical language designs.
- [HoTT and cubical proof automation](roadmaps/hott-automation-roadmap.md): A7 (baseline, regressions and canonicity fixture) is delivered; see the [checkpoint](tactical/hott-automation-handoff.md). The rest is planned. It follows the ergonomics roadmap and reorders its remaining work around path operations, path induction, transport, h-levels and dependent paths.
- [Kernel extensions for computation](roadmaps/cubical-kernel-roadmap.md): planning only. Trusted-kernel changes, led by computational truncation, under the requirement that assumption-free results compute.
  Its [conversion probes](examples/hott-automation/README.md) record what the kernel already computes and which laws it rejects.

## Other sections

- [Roadmaps](roadmaps/README.md): intended scope and unfinished mathematical and language-tooling goals.
- [Tactical notes](tactical/README.md): handoffs, implementation details, and checked proof developments.
- Guides: [CLI](guides/cli.md), [kernel](guides/kernel.md), and [deployment](guides/deployment.md).
- [Cubical implementation notes](cubical/): kernel constructions, performance, browser integration, and migration history. Start with the [benchmark](cubical/benchmark.md) and [checking optimizations](cubical/checking-optimizations.md) for performance work.
- [Language reference](../web/language.html): current user-facing syntax. The [older language design notes](guides/mathscript.md) are historical.

When handing off work, record what was checked, its assumptions and limitations,
the commands used to verify it, and the next unfinished obligation. Update both
the relevant roadmap and its tactical checkpoint so the next contributor can
continue from a known state.
