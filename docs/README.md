# Documentation and resumption guide

Read the relevant roadmap and checkpoint before extending a mathematical
development. Roadmaps describe goals and boundaries; tactical notes explain the
current implementation, verification commands, and next steps. Check statements
against the current source: some notes retain historical implementation details.
Moving these documents does not change their recorded status or resume paused work.

## Plan

- [Work plan](roadmaps/work-plan.md): staged, dependency-ordered work across the
  kernel, the language, the library rebuild and the language reference.
- [Results of the first library](library-results.md): the frontier and iconic
  theorems of the archived library in mathematical English, with their
  logical assumptions. It is the specification the rebuild starts from.
- Adopted designs:
  - [higher inductive-inductive types](roadmaps/higher-inductive-types-design.md)
    (kernel);
  - [theories and inductive declarations](roadmaps/inductive-language-features.md)
    (language).
- Experimental designs:
  - [kernel instructions](roadmaps/kernel-instructions.md): the THTH-style
    forward kernel, with every search decision in an untrusted driver;
  - [learned search](roadmaps/learned-search.md): a small policy and value
    network, trained against that kernel, for cheaper derivations.

## Mathematical roadmaps

The Galois, complex-analysis and RH developments belong to the first library.
They stay paused until the rebuild reaches their prerequisites.

| Development | Roadmap | Checkpoint and supporting notes |
| --- | --- | --- |
| Galois theory | [Finite Galois development](roadmaps/galois-roadmap.md) | [Resumption checkpoint](tactical/galois-handoff.md), [symmetries as loops](tactical/galois.md), [polynomial algebra](tactical/polynomial-algebra.md), [finite dimension](tactical/finite-dimension.md) |
| Complex analysis | [Algebraic closure, residues, and Picard](roadmaps/complex-analysis-roadmap.md) | [Paused-development checkpoint](tactical/complex_analysis_handoff.md), [complex curves](tactical/complex_curves.md), [limits](tactical/analysis_limits.md) |
| Real numbers | [Number systems for the rebuild](roadmaps/reals-roadmap.md) | Integers, rationals as a canonical quotient, Cauchy reals at kernel H3; the first library's constructions described as archived. |
| Analytic number theory | [RH and prime-counting error](roadmaps/rh-prime-counting-roadmap.md) | Planning only: precise conditional statement, analytic dependencies, and potential homotopy interpretations. No proof implementation or tactical checkpoint yet. |

## Language tooling roadmap

- [Language enhancement proposals](roadmaps/language-enhancement-proposals.md):
  deferred features, each kept with what would justify taking it up.
- [Computation notation: monadic do and arrows](roadmaps/computation-notation-roadmap.md):
  planned blocks for existence proofs, free-algebra substitution and arrow
  composition, with explicit structures and checked elaboration.
- [Simplification and shorter proofs](roadmaps/proof-ergonomics-roadmap.md):
  - Delivered: rewriting, calculations, `simp`/`simpa` and cubical path
    syntax.
  - Remaining: argument inference, theories, inductive declarations with
    pattern matching, and computability checking.
  - See the [implementation plan](roadmaps/proof-ergonomics-implementation-plan.md)
    and [checked/proposed examples](examples/proof-ergonomics/README.md).
- [HoTT and cubical proof automation](roadmaps/hott-automation-roadmap.md):
  - Delivered: A7 (baseline, regressions and canonicity fixture); see the
    [checkpoint](tactical/hott-automation-handoff.md).
  - Planned: path operations, path induction, transport, h-levels, dependent
    paths, structure identity and transfer.
- [Kernel extensions for computation](roadmaps/cubical-kernel-roadmap.md):
  planning only. G0 (universe-generic checking), then H1–H4 (inductive
  signatures), under the requirement that computability is expressible and
  preserved. Its [conversion probes](examples/hott-automation/README.md)
  record what the kernel already computes and which laws it rejects.

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
