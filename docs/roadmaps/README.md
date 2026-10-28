# Development roadmaps

These describe current contracts, unfinished work and its limits. The
[work plan](work-plan.md) owns scheduling. A target statement or supplied
theorem parameter is not an already proved result. Paused mathematics does
not resume when a language milestone ships.

**Current priority, directed on 2026-10-17:** runtime optimization and the
natural/integer/rational foundations, including ordered-ring/field definitions.
Public `Nat` became binary `BNat` on 2026-10-18 (#278), once its correctness
and compatibility gates passed. The reals roadmap stays paused. See the
[runtime roadmap](runtime/runtime-evaluation-roadmap.md).

**Sequence decided on 2026-10-26** ([first actions](work-plan.md#first-actions)):
1. Restore site publication.
2. Runtime and numbers:
   - B8 of the [debugging plan](runtime/rational-normalization-debug-plan.md),
     done on 2026-10-26;
   - the default binary `Z`/`Q`, gated on folded normal forms;
   - #289's runtime in the REPLs: value forms on 2026-10-26; constructor
     patterns and quotient point constructors remain;
   - typed readback;
   - all of the archive's number theory moved to the library and removed
     from the archive ([NT1–NT5](archive-retirement.md#number-theory-in-the-library)),
     with EVAL7's primality, divisibility and Euclid as NT2.
3. Alongside the runtime phase: K2.5's `axiom` definitions.
4. After it: simplicial ST0 and ST2, then the language direction below.

**Language direction selected on 2026-10-17:** develop the language through categories,
monads, algebraic homology and synthetic cohomology as a sustained testbed.
Both algebraic and HoTT constructions are central. Success includes reusable
theory interfaces, proof automation, notation, inference, inspection and
computation, with mathematical proofs validating those features. The
[progression](work-plan.md#first-actions) prioritizes that development rather
than the shortest route to a homology or cohomology theorem. The packages
below remain unfinished until their own acceptance evidence is delivered.

**Simplicial direction proposed on 2026-10-24:** a separate directed layer
alongside cubical equality, preserving ordinary universes, setness and
assumption scopes, with computing rules for the new layer. The
[simplicial roadmap](hott/simplicial-types.md) records the agreed
`x ->[C] y` spelling, proposed shape syntax and open semantic gates.
Ordinary categories and UA0–UA6 continue independently; this does not
change the runtime priority or claim a conservative extension is proved.
Since 2026-10-26, ST0 and ST2 are scheduled after the runtime phase, ahead of
the categorical progression.

## At a glance

Roadmap status reconciled on 2026-10-26 against main `7230825e`, after the
runtime and numerical stacks (#266–#297), the demand marks and folded normal
forms (#303–#310), the display and qualified-name changes (#311–#313) and the
binary rationals (#283). The linked specifications, mathematical approvals and
dated measurements retain their original evidence; this status audit does not
rerun those reviews.

| Track | Implemented | Still open |
| --- | --- | --- |
| Kernel and universes | Instruction-kernel stages 1–5; checker retirement; G0; face restriction; checking/bridge optimizations #194–#197. For the runtime track: the full-normalization cache (#269), explicit-stack normalization, weak-head, substitution and comparison traversals (#291, #292, #294, #297), resource failures preserved across APIs (#285) and the folded normal-form query (#309); workbench reduction controls (#298); kernel reference chapters 14–17 (#301) | Remaining stage-6 performance/certificate work; composition, Glue and HIT tube helpers still recurse natively; optional E1/E2 |
| Inductive declarations | H1 released: one-sort data and higher types, matching, structural recursion and automatic clauses | Derivations/views; H2 indexed families; H3 companion sorts; H4 on demand; legacy truncation removal (K2.5), completed by the archive retirement (I0.5) |
| Proof ergonomics | Rewriting, simplification, `let`, holes, inference, implicit parameters, cubical shorthand, two h-level solver slices, evaluation patterns/readout, box notation and squares | Folded path rules, constructor descent, induction tooling, broader dependent rewriting, solver and square-migration remainders |
| Theories | L2.4 and all six L2.4c slices: models, families/relations, inheritance, `Hom`/`Iso`, `use` and qualified operators; inherited operations and laws implemented by a child theory (#268); the algebra lattice with ordered-ring and ordered-field interfaces (#267) | Morphism opt-ins, general proposition laws, implicit operation arguments, checked initial/free capabilities, structure identity |
| Notation | L2.10a–e and i–k: named notation, operands, literals, printing, reversal, explicit selection and partial inverse | Shadowing/inspection/printing details; deferred large numerals and `decide`; proposed general notation rules |
| Evaluation/numbers | EVAL0 harness; EVAL1 one-pass REPL evaluation (#266); EVAL2 full-normalization cache (#269); a first internal EVAL3/EVAL4 query for ordinary data, used by no checker or page yet (#289); EVAL5's observation contract: demand marks `!`/`!!` in patterns and printing (#303–#306), then `!!` the folded and `!!!` the full normal form (#307, #309, #310); explicit-evidence directives `evaluate nonempty/empty … by …` (#284). NUM0/NUM1 and public `Nat` as binary `BNat` (#272–#278); NUM2's binary integers (#279–#281) and the binary-rational API, released on folded normal forms (#283); public `Z`/`Q` as `BInt`/`BQ`, with binary ring numerals and casts, on the same gate | EVAL3/EVAL4 integration; EVAL5's typed readback; EVAL6–EVAL8. NUM2's full-normal-form targets for the rational inverses. The [debugging plan](runtime/rational-normalization-debug-plan.md)'s remaining phases, from B3 on (B8 is done) |
| Library/reference | Forty-three self-contained foundation modules, including the universe-smallness proofs, binary naturals, integers and rationals, ordered algebra, the continuum-hypothesis statements (#295), in `continuum_axioms` their optional assumptions, and excluded middle from the decidable one; checked reference, explorer and quick reference; kernel chapters 14–17 (#301) | Higher-constructor chapter, classical-assumption consolidation and later mathematical coverage |
| Computation notation | Prerequisites: inference, matching, core theories and set-indexed theory families | N0–N5: checked interfaces, monadic `do` and arrows; design only |
| [Simplicial types](hott/simplicial-types.md) | Design only; arrow spelling agreed | ST0–ST6: preservation and model, shared ordinary arrow syntax, directed shapes/extensions, synthetic categories, coherent diagrams and higher algebra |
| Learned search | Phases 1–2: explicit driver choices and work/trajectory measurement | Phases 3–5, conditional on demonstrated benefit |
| [Frontend/bindings](historical/capture-bindings.md) | CB0–CB7, both cleanup passes, generated inspection and arbitrary-context REPLs; one naming pass for every display (#311, #312); `module::name` references, which nothing shadows (#313) | No CB packages remain; preserve the semantic and resource gates. Two display read-back defects are recorded in [pr-312-todo](../reports/pr-312-todo.md) |
| [Refactoring/testing](historical/refactoring-and-testing.md) | Agreed RC scope and final cleanup, #243–#263: publication ownership, Cubist test pragmas/migrations and shared tooling. The remote mutation gate is green: all 16 probes passed in #264's CI and in every passing CI run since | No agreed implementation slices remain. Instruction-driver reorganization is deferred; build prerequisites/native discovery are excluded |

**Frontend integration is complete:** initial/free construction and fold
behavior, CB0–CB7, cleanup and the agreed #224 refactoring ideas are on main.
The older #219–#225 and #227 proposals are closed as superseded;
[#242](https://github.com/KanHarI/cubist-math/pull/242) supplies the mutation CI hook.
Checked universal capabilities and their mathematical proofs remain unfinished.
Hydra #233 was closed unmerged on 2026-10-26, to be re-developed when the
language is more mature ([branch record](work-plan.md#branch-work)). The
[RC verification record](historical/refactoring-and-testing.md#verification-record) records
the mutation probe's remote pass. **Site publication has failed since #278**
(2026-10-18): `npm run test:site` times out waiting for `seven : UNat` on
the types chapter, whose first example now defines `wide`
([pr-293-todo](../reports/pr-293-todo.md)). PR CI does not run that script,
and the published site is still #277's.

After the runtime phase, language work pairs morphism opt-ins (L2.4d), general proposition laws
(L2.11) and implicit operation arguments (L2.12) with categorical examples,
and path/induction tooling with low-degree synthetic examples. N0/N1's
monadic interfaces can start from their existing prerequisites. Categories,
equivalences, structure identity, checked free constructions and computation
notation then deepen both strands; full algebraic and synthetic developments
retain their individual dependencies. The runtime and numerical phase precedes
these language strands. See
[first actions](work-plan.md#first-actions) and
[open decisions](work-plan.md#open-decisions).

## HoTT

[hott/](hott/) contains proof automation and type-theoretic foundations:

- [HoTT automation](hott/hott-automation-roadmap.md): remaining path, induction,
  equivalence, transport, h-level and structure-identity work.
- [Simplicial types](hott/simplicial-types.md): proposed directed shapes and
  extensions alongside cubical equality, with explicit ordinary-fragment
  preservation gates, Cubist syntax and staged categorical applications.
- [Higher inductive-inductive types](hott/higher-inductive-types-design.md):
  H1 delivered; H2 indexed families, H3 companion sorts and H4 remain planned.
- [H1 specification](hott/h1-signature-specification.md),
  [model](hott/h1-model.md), [canonicity](hott/h1-canonicity.md) and
  [critical pairs](hott/h1-critical-pairs.md): current normative rules and
  approved mathematical arguments. These remain active references after release.
- [Truncation migrations](hott/h1-truncation-migration.md) and their
  [ledger](hott/h1-truncation-ledger.json): 17 pinned changes and an implemented
  verifier. Decided on 2026-10-20: the legacy assumptions are removed with the
  archive ([removal plan](hott/h1-truncation-migration.md#removing-the-legacy-assumptions)),
  and the remaining archive remedies are not pursued.

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
  boundary and remaining performance/certificate work. Its migration record,
  through the term checker's retirement, is
  [historical](historical/kernel-instructions-history.md).
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
The remote CI mutation check has passed. The index also lists display naming
and `module::name` references as continuing contracts.

## Runtime

[runtime/](runtime/) owns evaluation and the binary numerical foundations:

- [Runtime evaluation](runtime/runtime-evaluation-roadmap.md): EVAL0–EVAL2,
  NUM0, NUM1 and the default binary `Nat` are implemented; NUM2's binary
  integers and rationals are on main and are the default `Z`/`Q`.
  EVAL3/EVAL4's runtime computes the REPLs' value forms (#320), higher
  sorts' point constructors included (#324). EVAL5's observation contract
  has shipped; its typed readback is decided in
  [typed readback](runtime/typed-readback.md). EVAL6–EVAL8 remain.
- [Rational normalization debugging plan](runtime/rational-normalization-debug-plan.md):
  the attribution of the rational full-normalization cluster; D1 and B8 done.
- [Typed readback](runtime/typed-readback.md): EVAL5's readback of runtime
  values into kernel terms, proposed on 2026-10-28 for decision.

EVAL5's observation contract, the
[evaluation demand marks](historical/evaluation-demand-marks.md) (DM0–DM6,
#304–#306) and [folded normal forms](historical/folded-normal-forms.md)
(`!!` folded, `!!!` full; FN1/FN2, #309/#310), is complete and archived in
[historical/](historical/README.md); its rules remain in force.

## Mathematics

[mathematics/](mathematics/) contains the library-development tracks.
The first library is archived. Its checked results remain regression
evidence, not a claim that the new library has rebuilt those areas. The
archive itself is to be retired: [archive retirement](archive-retirement.md)
(I0.5, direction adopted on 2026-10-20) owns the follow-ups, including the
per-area decisions on what the library rebuilds before the archive is deleted.

| Roadmap | Checked progress | Remaining scope |
| --- | --- | --- |
| [Galois](mathematics/galois-roadmap.md) | Finite linear algebra, Artin's theorem and the core finite correspondence with a supplied algebraically closed target | Finite index/normality/quotient theorems and the full target; paused. [Checkpoint](../tactical/galois-handoff.md) |
| [Reals](mathematics/reals-roadmap.md) | Current quotient integers/rationals | NUM owns binary replacements; this plan owns order, presentations, completeness interfaces and real constructions. Cauchy reals need H3; paused beyond existing foundations |
| [Complex analysis](mathematics/complex-analysis-roadmap.md) | Algebra, limits, contour estimates and affine dyadic integral laws over supplied scalars | Topology and general integration bridges; FTA, residue theorem and Great Picard unproved; paused. [Checkpoint](../tactical/complex_analysis_handoff.md) |
| [RH and prime counting](mathematics/rh-prime-counting-roadmap.md) | Statement and dependency plan only | All analytic-number-theory milestones; not started |
| [Homological algebra](mathematics/homological-algebra.md) | Proposal and dependency plan only; selected as the language testbed | HA0–HA6 remain unimplemented. Algebraic homology and synthetic cohomology advance through the language-development progression |
| [Universal algebra](mathematics/universal-algebra.md) | Proposal with three checked probes, not fixtures: groups equivalent to the models of the pushout presentation of monoids and quasigroups over magmas; abstract clones with their models and free models; the cyclic group of order three in both forms | UA0–UA6 remain unimplemented. Theories as values (clones), the clone of an equational theory, and the pushout/pullback statements wait on L2.6 and the categories packages |

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
- The evaluation demand marks and folded normal forms, EVAL5's completed
  observation contract, with the marks' acceptance report and probes; the
  instruction kernel's migration record through the term checker's retirement.

Archiving a completed plan preserves its linked contracts, regression tests and
resource limits. Unfinished or paused work stays in its subject folder. Dated
measurements and review decisions retain their original revisions.
