# Development roadmaps

These describe current contracts, unfinished work and its limits. The
[work plan](work-plan.md) owns scheduling. A target statement or supplied
theorem parameter is not an already proved result. Paused mathematics does
not resume when a language milestone ships.

## At a glance

Roadmap status reconciled on 2026-10-17 against main `e729c2d5`, including
the merged CB and refactoring stacks. Delivered means present on main.
The linked specifications, mathematical approvals and dated measurements retain
their original evidence; this status audit does not rerun those reviews.

| Track | Delivered on main | Still open |
| --- | --- | --- |
| Kernel and universes | Instruction-kernel stages 1–5; checker retirement; G0; face restriction; checking/bridge optimizations #194–#197 | Remaining stage-6 performance/certificate work; optional E1/E2 |
| Inductive declarations | H1 released: one-sort data and higher types, matching, structural recursion and automatic clauses | Derivations/views; H2 indexed families; H3 companion sorts; H4 on demand; archive truncation remedies |
| Proof ergonomics | Rewriting, simplification, `let`, holes, inference, implicit parameters, cubical shorthand, two h-level solver slices, evaluation patterns/readout, box notation and squares | Folded path rules, constructor descent, induction tooling, broader dependent rewriting, solver and square-migration remainders |
| Theories | L2.4 and all six L2.4c slices: models, families/relations, inheritance, `Hom`/`Iso`, `use` and qualified operators | Morphism opt-ins, general proposition laws, implicit operation arguments, checked initial/free capabilities, structure identity |
| Notation | L2.10a–e and i–k: named notation, operands, literals, printing, reversal, explicit selection and partial inverse | Shadowing/inspection/printing details; deferred large numerals and `decide`; proposed general notation rules |
| Evaluation/numbers | EVAL0 measurement harness and recorded outcomes | EVAL1–EVAL8; NUM0–NUM2 binary foundations. Existing `Z`/`Q` use unary naturals |
| Library/reference | Seventeen self-contained foundation modules, including the universe-smallness proofs; checked reference, explorer and quick reference | Higher-constructor chapter, classical-assumption consolidation and later mathematical coverage |
| Computation notation | Prerequisites: inference, matching, core theories and set-indexed theory families | N0–N5: checked interfaces, monadic `do` and arrows; design only |
| Learned search | Phases 1–2: explicit driver choices and work/trajectory measurement | Phases 3–5, conditional on demonstrated benefit |
| [Frontend/bindings](historical/capture-bindings.md) | CB0–CB7, both cleanup passes, generated inspection and arbitrary-context REPLs | No CB packages remain; preserve the semantic and resource gates |
| [Refactoring/testing](historical/refactoring-and-testing.md) | Agreed RC scope and final cleanup, #243–#263: publication ownership, Cubist test pragmas/migrations and shared tooling | No agreed implementation slices remain; final remote mutation probe needs investigation. Instruction-driver reorganization is deferred; build prerequisites/native discovery are excluded |

**Frontend integration is complete:** initial/free construction and fold
behavior, CB0–CB7, cleanup and the agreed #224 refactoring ideas are on main.
The older #219–#225 and #227 proposals are closed as superseded;
[#242](https://github.com/KanHarI/cubist-math/pull/242) supplies the mutation CI hook.
Checked universal capabilities and their mathematical proofs remain unfinished.
The [branch record](work-plan.md#branch-work) separately tracks Hydra #233,
which remains an unmerged draft. Site publication succeeded; the
[RC verification record](historical/refactoring-and-testing.md#verification-record) records
the unresolved termination of the final CI mutation probe.

Next language work: morphism opt-ins (L2.4d), general proposition laws
(L2.11), implicit operation arguments (L2.12), then L2.6's checked
capabilities and universal proofs. Squares/h-level remainders, derivations,
equivalences, structure identity and categories follow their dependencies.
EVAL1 and NUM0/NUM1 can advance independently. See
[first actions](work-plan.md#first-actions) and
[open decisions](work-plan.md#open-decisions).

## HoTT

[hott/](hott/) contains proof automation and type-theoretic foundations:

- [HoTT automation](hott/hott-automation-roadmap.md): remaining path, induction,
  equivalence, transport, h-level and structure-identity work.
- [Higher inductive-inductive types](hott/higher-inductive-types-design.md):
  H1 delivered; H2 indexed families, H3 companion sorts and H4 remain planned.
- [H1 specification](hott/h1-signature-specification.md),
  [model](hott/h1-model.md), [canonicity](hott/h1-canonicity.md) and
  [critical pairs](hott/h1-critical-pairs.md): current normative rules and
  approved mathematical arguments. These remain active references after release.
- [Truncation migrations](hott/h1-truncation-migration.md) and their
  [ledger](hott/h1-truncation-ledger.json): 17 pinned changes and an implemented
  verifier; the rest of K2.5 remains unfinished.

## High-level abstractions

[high-level-abstractions/](high-level-abstractions/) owns the language above
those foundations:

- [Language features](high-level-abstractions/inductive-language-features.md):
  theories, declarations, relations, bundles, presentations and derived interfaces.
- [Core theories](high-level-abstractions/core-theories.md): L2.4/L2.4c's current
  contract and unfinished checked initial/free capabilities.
- [Categories](high-level-abstractions/categories.md): morphism opt-ins, general
  laws, categorical library, universal constructions and the abelian tower.
- [Proof ergonomics](high-level-abstractions/proof-ergonomics-roadmap.md): shipped
  proof tools and the remaining theory/declaration/automation contracts.
- [Notation](high-level-abstractions/notation.md): delivered notation/literal
  slices, remaining tooling and deferred extensions.
- [Computation notation](high-level-abstractions/computation-notation-roadmap.md):
  N0–N5, checked interfaces, monadic `do` and arrows; not yet implemented.

## Kernel

[kernel/](kernel/) covers trusted instructions and their untrusted driver:

- [Kernel instructions](kernel/kernel-instructions.md): current checker/driver
  boundary and remaining performance/certificate work.
- [Kernel extensions](kernel/cubical-kernel-roadmap.md): G0/H1 delivered;
  H2–H4, resizing migrations and optional computation extensions.
- [Language proposals](kernel/language-enhancement-proposals.md): deferred
  universe proposals E1/E2, each requiring a concrete use case.
- [Learned search](kernel/learned-search.md): phases 1–2 delivered; optional
  learning and deployment phases 3–5 remain.

## Frontend

[frontend/](frontend/README.md) indexes the continuing binding, generation,
publication, inspection and contextual-REPL contracts. The CB/FG/RC migrations
are complete; their plans and checkpoint records are in [historical/](historical/README.md).
The [work plan](work-plan.md#first-actions) retains the unresolved remote CI
mutation check as a validation follow-up.

## Runtime

[runtime/](runtime/) contains [evaluation and binary foundations](runtime/runtime-evaluation-roadmap.md):
EVAL0 is complete; EVAL1–EVAL8 and NUM0–NUM2 remain planned.

## Mathematics

[mathematics/](mathematics/) contains the library-development tracks.
The first library is archived. Its checked results remain regression
evidence, not a claim that the new library has rebuilt those areas.

| Roadmap | Checked progress | Remaining scope |
| --- | --- | --- |
| [Galois](mathematics/galois-roadmap.md) | Finite linear algebra, Artin's theorem and the core finite correspondence with a supplied algebraically closed target | Finite index/normality/quotient theorems and the full target; paused. [Checkpoint](../tactical/galois-handoff.md) |
| [Reals](mathematics/reals-roadmap.md) | Current quotient integers/rationals | NUM owns binary replacements; this plan owns order, presentations, completeness interfaces and real constructions. Cauchy reals need H3; paused beyond existing foundations |
| [Complex analysis](mathematics/complex-analysis-roadmap.md) | Algebra, limits, contour estimates and affine dyadic integral laws over supplied scalars | Topology and general integration bridges; FTA, residue theorem and Great Picard unproved; paused. [Checkpoint](../tactical/complex_analysis_handoff.md) |
| [RH and prime counting](mathematics/rh-prime-counting-roadmap.md) | Statement and dependency plan only | All analytic-number-theory milestones; not started |
| [Homological algebra](mathematics/homological-algebra.md) | Proposal and dependency plan only | HA0–HA6, synthetic and algebraic tracks; not started, awaiting an explicit start decision |

See the [results catalog](../library-results.md) and
[documentation index](../README.md) for supporting evidence and guides.

## Vision

[vision/](vision/) contains [mathematical proof concision](vision/mathematical-proof-concision.md):
long-term goals and proposed acceptance evidence, not a list of delivered features.

## Historical

[historical/](historical/README.md) holds exhausted implementation plans,
completed migration records, superseded sequences and dated validation:

- CB0–CB7 and their completion records; the FG generation plan, its earlier
  syntax-hygiene approach, and the completed RC refactoring/source-test plan.
- The completed induction-hypothesis syntax change and Nat/W/pushout migrations.
- G0's completed specification, H1 release/review history, retired differential
  evidence, older scheduling/ergonomics sequences and the dated work-plan audit.

Archiving a completed plan preserves its linked contracts, regression tests and
resource limits. Unfinished or paused work stays in its subject folder. Dated
measurements and review decisions retain their original revisions.
