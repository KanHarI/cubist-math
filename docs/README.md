# Documentation and resumption guide

Read the relevant roadmap and checkpoint before extending a mathematical
development. Roadmaps describe goals and boundaries; tactical notes explain the
current implementation, verification commands, and next steps. Check statements
against the current source: some notes retain historical implementation details.
Moving these documents does not change their recorded status or resume paused work.

## Plan

- [Work plan](roadmaps/work-plan.md): staged, dependency-ordered work across the
  language, its kernel support and the language reference. Broad mathematical
  rebuilding is deferred.
- [Work-plan audit of 2026-09-28](roadmaps/audits/2026-09-28-audit.md): the
  baseline revision and findings behind the current statuses.
- [Historical plans and specifications](roadmaps/historical/README.md):
  completed work, including the implemented G0 universe specification.
- [Results of the first library](library-results.md): the frontier and iconic
  theorems of the archived library in mathematical English, with their
  logical assumptions. It is the specification the rebuild starts from.
- Adopted designs:
  - [higher inductive-inductive types](roadmaps/higher-inductive-types-design.md)
    (kernel);
  - [theories and inductive declarations](roadmaps/inductive-language-features.md)
    (language).
- Released specifications:
  - [H1 signatures](roadmaps/h1-signature-specification.md): one-sort data and
    higher inductive types, their soundness note, and the truncation and
    resizing policy. Released on 2026-10-02 after review of its model,
    critical pairs and canonicity: declared types are on by default, with no
    experimental option or marker. Nat, W and pushouts are source
    declarations; see the [migration record](roadmaps/h1-program-types.md)
    for the current behavior, validation and limits of the historical
    comparison fixtures, and the [history](roadmaps/h1-history.md) for the
    release checklist, the review rounds and the retired differential
    contract.
- The trusted kernel:
  [kernel instructions](roadmaps/kernel-instructions.md), the THTH-style
  forward kernel with every search decision in an untrusted driver, merged
  on 2026-09-26. Every later kernel item is a set of instructions; the
  [work plan](roadmaps/work-plan.md#the-instruction-kernel-and-this-plan)
  records what that changes. The audit of 2026-09-28 found the separation
  from the old conversion checker incomplete; work-plan I1.2a corrected it
  the same day.
- Experimental designs:
  - [learned search](roadmaps/learned-search.md): a small policy and value
    network, trained against that kernel, for cheaper derivations.

## Mathematical roadmaps

The Galois, complex-analysis and RH developments belong to the first library.
They and broad library rebuilding stay paused during the language work;
finishing a language milestone does not automatically resume them.

| Development | Roadmap | Checkpoint and supporting notes |
| --- | --- | --- |
| Galois theory | [Finite Galois development](roadmaps/galois-roadmap.md) | [Resumption checkpoint](tactical/galois-handoff.md), [symmetries as loops](tactical/galois.md), [polynomial algebra](tactical/polynomial-algebra.md), [finite dimension](tactical/finite-dimension.md) |
| Complex analysis | [Algebraic closure, residues, and Picard](roadmaps/complex-analysis-roadmap.md) | [Paused-development checkpoint](tactical/complex_analysis_handoff.md), [complex curves](tactical/complex_curves.md), [limits](tactical/analysis_limits.md) |
| Real numbers | [Number systems for the rebuild](roadmaps/reals-roadmap.md) | The library's integers and rationals, built on 2026-10-05 as quotients; their order, canonical rationals and the Cauchy reals (kernel H3) are open. The first library's constructions are described as archived. |
| Homological algebra | [Synthetic and algebraic homological algebra](roadmaps/homological-algebra.md) | Proposed on 2026-10-07, not started: Eilenberg–MacLane spaces and cohomology that computes, then modules, chain complexes, homology and Ext without the axiom of choice. |
| Analytic number theory | [RH and prime-counting error](roadmaps/rh-prime-counting-roadmap.md) | Planning only: precise conditional statement, analytic dependencies, and potential homotopy interpretations. No proof implementation or tactical checkpoint yet. |

## Language tooling roadmap

- [Morphisms, categories and universal constructions](roadmaps/categories.md):
  opt-in morphisms and checked initial/free derivations, which may fail;
  general propositional laws and the proposed categorical library. The
  [L2.6 contract](roadmaps/core-theories.md#initial-and-free-models-l26)
  separates theory admission from constructing and proving a free object.

- [Language enhancement proposals](roadmaps/language-enhancement-proposals.md):
  deferred features, each kept with what would justify taking it up.
- [Computation notation: monadic do and arrows](roadmaps/computation-notation-roadmap.md):
  planned blocks for existence proofs, free-algebra substitution and arrow
  composition, with explicit structures and checked elaboration.
- [Simplification and shorter proofs](roadmaps/proof-ergonomics-roadmap.md):
  - Delivered: rewriting, calculations, `simp`/`simpa`, cubical path
    syntax, dependency tracking, `computable` and `evaluate` with patterns
    and truncation readout, argument inference and implicit parameters,
    explicit `match`, theories and explicit notation.
  - Remaining: the rest of initial and free models, algebraic
    normalization and structure identity, and the rest of inductive
    declarations (`deriving`, proof-first h-levels).
  - See the [implementation plan](roadmaps/proof-ergonomics-implementation-plan.md)
    and [checked/proposed examples](examples/proof-ergonomics/README.md).
- [HoTT and cubical proof automation](roadmaps/hott-automation-roadmap.md):
  - Delivered: A7 (baseline, regressions and canonicity fixture), the A5
    goal-layer core, A4/A6 deterministic fuel with residual-goal
    diagnostics, D0a's h-level definitions, D1's `hlevel` solver with
    registered rules and quantified hints, and E2's box notation and squares
    library; D0b is started. See the
    [checkpoint](tactical/hott-automation-handoff.md).
  - Planned: remaining goal-layer work, path operations,
    path induction, transport, the rest of the h-level solver, dependent
    paths, structure identity and transfer.
- [Kernel extensions for computation](roadmaps/cubical-kernel-roadmap.md):
  G0 (universe-generic checking) delivered; H1 (inductive signatures)
  released on 2026-10-02 after its mathematical review; H2–H4 and optional
  extensions planned, under the requirement that computability is
  expressible and preserved. Its [conversion probes](examples/hott-automation/README.md)
  record what the kernel already computes and which laws it rejects.

## Other sections

- [Roadmaps](roadmaps/README.md): intended scope and unfinished mathematical and language-tooling goals.
- [Tactical notes](tactical/README.md): handoffs, implementation details, and checked proof developments.
- Guides: [CLI](guides/cli.md), [kernel](guides/kernel.md), and [deployment](guides/deployment.md).
- [Cubical implementation notes](cubical/): kernel constructions, performance, browser integration, and migration history. Start with the [benchmark](cubical/benchmark.md) and [checking optimizations](cubical/checking-optimizations.md) for performance work.
- [Language reference](../web/language.html): current user-facing syntax. The [older language design notes](guides/cubist.md) are historical.

When handing off work, record what was checked, its assumptions and limitations,
the commands used to verify it, and the next unfinished obligation. Update both
the relevant roadmap and its tactical checkpoint so the next contributor can
continue from a known state.
