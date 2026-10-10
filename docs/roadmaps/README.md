# Development roadmaps

These describe current contracts, unfinished work and its limits. The
[work plan](work-plan.md) owns scheduling. A target statement or supplied
theorem parameter is not an already proved result. Paused mathematics does
not resume when a language milestone ships.

## At a glance

Reconciled on 2026-10-10 against main `cb525f07` (2026-10-08). Delivered
means merged into main; the open PR stack is identified separately.

| Track | Delivered on main | Still open |
| --- | --- | --- |
| Kernel and universes | Instruction-kernel stages 1–5; checker retirement; G0; face restriction; checking/bridge optimizations #194–#197 | Remaining stage-6 performance/certificate work; optional E1/E2 |
| Inductive declarations | H1 released: one-sort data and higher types, matching, structural recursion and automatic clauses | Derivations/views; H2 indexed families; H3 companion sorts; H4 on demand; archive truncation remedies |
| Proof ergonomics | Rewriting, simplification, `let`, holes, inference, implicit parameters, cubical shorthand, two h-level solver slices, evaluation patterns/readout, box notation and squares | Folded path rules, constructor descent, induction tooling, broader dependent rewriting, solver and square-migration remainders |
| Theories | L2.4 and all six L2.4c slices: models, families/relations, inheritance, `Hom`/`Iso`, `use` and qualified operators | Morphism opt-ins, general proposition laws, implicit operation arguments, checked initial/free capabilities, structure identity |
| Notation | L2.10a–e and i–k: named notation, operands, literals, printing, reversal, explicit selection and partial inverse | Shadowing/inspection/printing details; deferred large numerals and `decide`; proposed general notation rules |
| Evaluation/numbers | EVAL0 measurement harness and recorded outcomes | EVAL1–EVAL8; NUM0–NUM2 binary foundations. Existing `Z`/`Q` use unary naturals |
| Library/reference | Sixteen self-contained foundation modules; checked reference, explorer and quick reference | Higher-constructor chapter, classical-assumption consolidation and later mathematical coverage |
| Computation notation | Prerequisites: inference, matching, core theories and set-indexed theory families | N0–N5: checked interfaces, monadic `do` and arrows; design only |
| Learned search | Phases 1–2: explicit driver choices and work/trajectory measurement | Phases 3–5, conditional on demonstrated benefit |

**Branch work, not delivered on main:** [#188](https://github.com/KanHarI/cubist-math/pull/188)
has the initial/free construction-and-fold prototype; [#204–#211](https://github.com/KanHarI/cubist-math/pull/211)
have the frontend-generation roadmap and FG0–FG6 implementation;
[#212](https://github.com/KanHarI/cubist-math/pull/212) proposes RC0–RC11
refactoring and test migration. The homological-algebra proposal in
[#198](https://github.com/KanHarI/cubist-math/pull/198) merged into that
stack, not main. The [branch record](work-plan.md#branch-work) distinguishes
implementation, integration evidence and unfinished obligations.

Next language work: morphism opt-ins (L2.4d), general proposition laws
(L2.11), implicit operation arguments (L2.12), then L2.6's checked
capabilities and universal proofs. Squares/h-level remainders, derivations,
equivalences, structure identity and categories follow their dependencies.
EVAL1 and NUM0/NUM1 can advance independently. See
[first actions](work-plan.md#first-actions) and
[open decisions](work-plan.md#open-decisions).

## Plan and designs

- [Work plan](work-plan.md): active package status, dependencies and decisions.
- [Historical index](historical/README.md): completed G0, closed H1 history,
  release/review and differential evidence, the dated work-plan audit,
  and superseded scheduling/ergonomics sequences. Historical commands and
  timings describe their recorded revisions.
- [Higher inductive-inductive types](higher-inductive-types-design.md):
  adopted H1–H4 design. H1 is released; H2–H4 remain unimplemented.
- [H1 specification](h1-signature-specification.md),
  [model](h1-model.md), [canonicity](h1-canonicity.md) and
  [critical pairs](h1-critical-pairs.md): current rules and approved
  mathematical arguments. Release does not make these contracts obsolete.
- [Source-defined Nat, W and pushouts](h1-program-types.md): current source
  API and the migration's limits; sums remain native.
- [Truncation migrations](h1-truncation-migration.md): implemented ledger
  verifier and 17 pinned changes; the rest of K2.5 remains unfinished.
- [Language features](inductive-language-features.md): theories,
  declarations, relations, bundles, presentations and derived interfaces.
- [Core theories](core-theories.md): implemented L2.4/L2.4c contract and
  the unfinished checked initial/free capability contract.
- [Notation](notation.md): delivered explicit notation/literal slices,
  remaining tooling details and deferred extensions.
- [Categories](categories.md): proposed morphism opt-ins, general laws,
  categorical library, universal constructions and the abelian tower.
- [Kernel instructions](kernel-instructions.md): current trusted checker,
  driver boundary and remaining performance/certificate work. Its dated
  migration stages record earlier APIs.
- [Learned search](learned-search.md): delivered instrumentation and optional
  learning/deployment phases.

## Language tooling

- [Induction hypothesis syntax](induction-hypothesis-syntax.md): adopted
  `constructor(fields) with hypotheses` clause design; not implemented.
- [Proof ergonomics](proof-ergonomics-roadmap.md): shipped proof tools and
  remaining theory/declaration/automation work. Its
  [remaining implementation contracts](proof-ergonomics-roadmap.md#remaining-implementation-contracts)
  own the unfinished work from the archived implementation sequence.
- [HoTT automation](hott-automation-roadmap.md): remaining goals, paths,
  induction, equivalences, transport, h-levels and structure identity.
  [Checkpoint](../tactical/hott-automation-handoff.md).
- [Runtime evaluation and binary foundations](runtime-evaluation-roadmap.md):
  EVAL0 is complete; EVAL1–EVAL8 and NUM0–NUM2 remain planned.
- [Computation notation](computation-notation-roadmap.md): N0–N5, no
  implementation yet; its core theory/inference prerequisites are available.
- [Kernel extensions](cubical-kernel-roadmap.md): G0 and H1 delivered;
  H2–H4, remaining resizing migrations and optional computation extensions.
- [Language proposals](language-enhancement-proposals.md): deferred E1/E2,
  each requiring a concrete use case.
- [Proof-concision vision](vision/mathematical-proof-concision.md): eventual
  goals and acceptance evidence, not a list of implemented features.

## Mathematics

The first library is archived. Its checked results remain regression
evidence, not a claim that the new library has rebuilt those areas.

| Roadmap | Checked progress | Remaining scope |
| --- | --- | --- |
| [Galois](galois-roadmap.md) | Finite linear algebra, Artin's theorem and the core finite correspondence with a supplied algebraically closed target | Finite index/normality/quotient theorems and the full target; paused. [Checkpoint](../tactical/galois-handoff.md) |
| [Reals](reals-roadmap.md) | Current quotient integers/rationals | NUM owns binary replacements; this plan owns order, presentations, completeness interfaces and real constructions. Cauchy reals need H3; paused beyond existing foundations |
| [Complex analysis](complex-analysis-roadmap.md) | Algebra, limits, contour estimates and affine dyadic integral laws over supplied scalars | Topology and general integration bridges; FTA, residue theorem and Great Picard unproved; paused. [Checkpoint](../tactical/complex_analysis_handoff.md) |
| [RH and prime counting](rh-prime-counting-roadmap.md) | Statement and dependency plan only | All analytic-number-theory milestones; not started |

See the [results catalog](../library-results.md) and
[documentation index](../README.md) for supporting evidence and guides.
