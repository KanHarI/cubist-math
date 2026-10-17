# Documentation and resumption guide

Read the relevant roadmap and checkpoint before extending a mathematical
development. Roadmaps describe goals and boundaries; tactical notes explain the
current implementation, verification commands, and next steps. Check statements
against the current source: some notes retain historical implementation details.
Moving these documents does not change their recorded status or resume paused work.

## Plan

Progress reconciled on 2026-10-17 against main `e729c2d5`. The
[roadmap overview](roadmaps/README.md#at-a-glance) records delivered work and
remaining packages; the [branch record](roadmaps/work-plan.md#branch-work)
distinguishes the merged CB/RC stacks from the unmerged Hydra draft.

- [Work plan](roadmaps/work-plan.md): staged, dependency-ordered work across the
  language, its kernel support and the language reference. Runtime optimization
  and naturals/integers/rationals come first, with binary `Nat` made the default
  when ready and ordered-ring/field definitions included. Reals stay paused.
  After performance work, return to language development through categories,
  monads, algebraic homology and synthetic cohomology; broad mathematical
  rebuilding is deferred.
- [Work-plan audit of 2026-09-28](roadmaps/historical/audits/2026-09-28-audit.md): the
  baseline revision and findings behind the current statuses.
- [Historical plans and specifications](roadmaps/historical/README.md):
  completed and superseded plans, the G0 specification, closed H1 release
  evidence and dated audits. Current specifications and unfinished work
  remain in the active roadmap directory.
- [Results of the first library](library-results.md): the frontier and iconic
  theorems of the archived library in mathematical English, with their
  logical assumptions. It is the specification the rebuild starts from.
- Adopted designs:
  - [higher inductive-inductive types](roadmaps/hott/higher-inductive-types-design.md)
    (kernel);
  - [theories and inductive declarations](roadmaps/high-level-abstractions/inductive-language-features.md)
    (language).
- Released specifications:
  - [H1 signatures](roadmaps/hott/h1-signature-specification.md): one-sort data and
    higher inductive types, their soundness note, and the truncation and
    resizing policy. Released on 2026-10-02 after review of its model,
    critical pairs and canonicity: declared types are on by default, with no
    experimental option or marker. Nat, W and pushouts are source
    declarations; see the [migration record](roadmaps/historical/h1-program-types.md)
    for the current behavior, validation and limits of the historical
    comparison fixtures, and the [history](roadmaps/historical/h1-history.md) for the
    release checklist, the review rounds and the retired differential
    contract.
- The trusted kernel:
  [kernel instructions](roadmaps/kernel/kernel-instructions.md), the THTH-style
  forward kernel with every search decision in an untrusted driver, merged
  on 2026-09-26. Every later kernel item is a set of instructions; the
  [work plan](roadmaps/work-plan.md#the-instruction-kernel-and-this-plan)
  records what that changes. The audit of 2026-09-28 found the separation
  from the old conversion checker incomplete; work-plan I1.2a corrected it
  the same day.
- Experimental designs:
  - [learned search](roadmaps/kernel/learned-search.md): a small policy and value
    network, trained against that kernel, for cheaper derivations.

## Mathematical roadmaps

The Galois, complex-analysis and RH developments belong to the first library.
They and broad library rebuilding stay paused during the language work;
finishing a language milestone does not automatically resume them.

| Development | Roadmap | Checkpoint and supporting notes |
| --- | --- | --- |
| Galois theory | [Finite Galois development](roadmaps/mathematics/galois-roadmap.md) | [Resumption checkpoint](tactical/galois-handoff.md), [symmetries as loops](tactical/galois.md), [polynomial algebra](tactical/polynomial-algebra.md), [finite dimension](tactical/finite-dimension.md) |
| Complex analysis | [Algebraic closure, residues, and Picard](roadmaps/mathematics/complex-analysis-roadmap.md) | [Paused-development checkpoint](tactical/complex_analysis_handoff.md), [complex curves](tactical/complex_curves.md), [limits](tactical/analysis_limits.md) |
| Real numbers | [Number systems for the rebuild](roadmaps/mathematics/reals-roadmap.md) | The library's integers and rationals, built on 2026-10-05 as quotients; their order, canonical rationals and the Cauchy reals (kernel H3) are open. The first library's constructions are described as archived. |
| Homological algebra | [Synthetic and algebraic homological algebra](roadmaps/mathematics/homological-algebra.md) | Selected on 2026-10-17 as a language testbed; HA0–HA6 remain unimplemented. Categories and monads, modules and complexes, and synthetic cohomology develop the language together, with checked proofs and explicit assumptions. |
| Universal algebra | [Clones, their models, and groups as a pushout of theories](roadmaps/mathematics/universal-algebra.md) | Proposed on 2026-10-17; UA0–UA6 remain unimplemented. Three checked probes, not fixtures: the equivalence of groups with the pushout presentation's models, abstract clones with free models and their category laws, and the cyclic group of order three as a pullback element. |
| Analytic number theory | [RH and prime-counting error](roadmaps/mathematics/rh-prime-counting-roadmap.md) | Planning only: precise conditional statement, analytic dependencies, and potential homotopy interpretations. No proof implementation or tactical checkpoint yet. |

## Language tooling roadmap

The [roadmap categories](roadmaps/README.md) group active work by subject.
Completed CB/FG/RC plans and migrations are archived; the
[frontend contract index](roadmaps/frontend/README.md) links their continuing rules.

- [Correct capture and bindings](roadmaps/historical/capture-bindings.md): implemented
  binding identities, complete interfaces, frontend generation and REPLs
  inside local scopes. CB0–CB7 and their cleanup are complete; the
  [PR comparison](reports/capture-bindings-pr-comparison.md) records the
  historical adoption decisions.
- [Refactoring and source-level tests](roadmaps/historical/refactoring-and-testing.md):
  agreed scope and cleanup merged in #243–#263, including publication ownership,
  parsed Cubist test contracts, actual test migrations and shared tooling.
- [Frontend generation](roadmaps/historical/frontend-generation.md): current generation
  contracts and semantic acceptance criteria, with the original FG schedule
  superseded by CB0–CB7. The [gap inventory](reports/frontend-generation-gaps.md)
  records failures at its pinned revision; the CB completion records describe
  their resolution.
- [Induction hypothesis syntax](roadmaps/historical/induction-hypothesis-syntax.md):
  constructor fields and induction hypotheses separated by `with`,
  implemented on 2026-10-11 with the old spelling still read and a checked
  migration tool.
- [Morphisms, categories and universal constructions](roadmaps/high-level-abstractions/categories.md):
  opt-in morphisms and checked initial/free derivations, which may fail;
  general propositional laws and the proposed categorical library. The
  [L2.6 contract](roadmaps/high-level-abstractions/core-theories.md#initial-and-free-models-l26)
  separates theory admission from constructing and proving a free object.

- [Language enhancement proposals](roadmaps/kernel/language-enhancement-proposals.md):
  deferred features, each kept with what would justify taking it up.
- [Computation notation: monadic do and arrows](roadmaps/high-level-abstractions/computation-notation-roadmap.md):
  planned blocks for existence proofs, free-algebra substitution and arrow
  composition, with explicit structures and checked elaboration.
- [Runtime evaluation and binary numerical foundations](roadmaps/runtime/runtime-evaluation-roadmap.md):
  Euclid failure evidence and a recorded evaluation baseline, evaluator and
  search improvements, and early `UNat`/`BNat` foundations with checked
  semiring isomorphism, equality in `U0`, strong induction over smaller
  binary values and new binary-backed `Z` and `Q`, with staged correctness
  and performance gates.
- [Simplification and shorter proofs](roadmaps/high-level-abstractions/proof-ergonomics-roadmap.md):
  - Delivered: rewriting, calculations, `simp`/`simpa` and cubical path
    syntax, dependency tracking, `computable` and exact-value `evaluate`.
  - Also delivered: argument/level inference, implicit parameters, core
    theories and their syntax revision, named notation, H1 matching,
    evaluation patterns and closed truncation readout, box notation and squares.
  - Remaining: checked initial/free capabilities, structure identity,
    advanced rewriting and declaration interfaces. The construction prototype
    and computing folds are integrated; checked universal capabilities remain open.
  - The old [implementation sequence](roadmaps/historical/proof-ergonomics-implementation-plan.md)
    is historical; its [remaining contracts](roadmaps/high-level-abstractions/proof-ergonomics-roadmap.md#remaining-implementation-contracts)
    have active owners. Keep the [checked/proposed examples](examples/proof-ergonomics/README.md).
- [HoTT and cubical proof automation](roadmaps/hott/hott-automation-roadmap.md):
  - Delivered: A7 (baseline, regressions and canonicity fixture), the A5
    goal-layer core, A4/A6 deterministic fuel with residual-goal
    diagnostics, D0a's h-level definitions, two slices of D1's
    `hlevel` solver and three square/box-notation slices; see the
    [checkpoint](tactical/hott-automation-handoff.md).
  - Planned: remaining goal-layer work, path operations,
    path induction, transport, the rest of the h-level solver, dependent
    paths, structure identity and transfer.
- [Kernel extensions for computation](roadmaps/kernel/cubical-kernel-roadmap.md):
  G0 (universe-generic checking) delivered; H1 (inductive signatures)
  released on 2026-10-02 after its mathematical review; H2–H4 and optional
  extensions planned, under the requirement that computability is
  expressible and preserved. Its [conversion probes](examples/hott-automation/README.md)
  record what the kernel already computes and which laws it rejects.

## Other sections

- [Roadmaps](roadmaps/README.md): intended scope and unfinished mathematical and language-tooling goals.
- [Tactical notes](tactical/README.md): handoffs, implementation details, and checked proof developments.
- Guides: [CLI](guides/cli.md), [kernel](guides/kernel.md), and [deployment](guides/deployment.md).
- [Cubical implementation notes](cubical): kernel constructions, performance, browser integration, and migration history. Start with the [benchmark](cubical/benchmark.md) and [checking optimizations](cubical/checking-optimizations.md) for performance work.
- [Language reference](../web/language.html): current user-facing syntax. The [older language design notes](guides/cubist.md) are historical.

When handing off work, record what was checked, its assumptions and limitations,
the commands used to verify it, and the next unfinished obligation. Update both
the relevant roadmap and its tactical checkpoint so the next contributor can
continue from a known state.
