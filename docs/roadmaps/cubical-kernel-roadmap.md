# Kernel extensions for computation in Cubist

Status: planning only, restructured on 2026-09-25. These items were split
out of the [HoTT and cubical automation roadmap](hott-automation-roadmap.md),
whose milestones A–F build on the existing kernel. G1–G5 keep their labels so
that references remain valid, although G1–G3 are now superseded.

- **G0** (universe-generic checking) and **H** (inductive signatures, stages
  H1–H4) were added on 2026-09-25. They serve the rebuild of the library,
  whose results are recorded in [library-results.md](../library-results.md).
- **H** implements the
  [higher inductive-inductive type design](higher-inductive-types-design.md).
- **G5** comes from the
  [proof ergonomics roadmap](proof-ergonomics-roadmap.md#architecture-and-invariants).

Every item changes the trusted C kernel or its query interface. So each needs
its own rule specification, native and reference implementations, and
review. The [work plan](work-plan.md) sequences these items with the language
and library work.

## Governing requirement: computability is expressible and preserved

Every closed term that checks without truncation or any other assumption must
reduce to a canonical value by kernel computation. This is a design priority,
not only a consistency property. It is invariant 10 of the
[HoTT roadmap](hott-automation-roadmap.md#invariants-added-to-the-ergonomics-requirements).
Since 2026-09-25 it has two halves:

- **Expressible.** A result that computes can be declared so and checked:
  - per-declaration non-computing dependencies;
  - `computable` declarations;
  - `evaluate` directives.

  These are owned by [ergonomics milestone 8](proof-ergonomics-roadmap.md#8-computability-as-a-checked-property).
  No mathematics in scope should need an axiom merely because the language
  lacks a computing formulation. Item H supplies computing truncation,
  quotients and identity families for that reason.
- **Preserved.** No kernel rule, elaboration feature or tool may silently lose
  computability. The kernel's part is that every rule ships with
  computation.

The current kernel has composition and transport rules for every type former:
`Nat`, `Unit`, sums, W types, pushouts, Glue, universes, Σ, Π and paths. Derived
path induction therefore computes on closed data, including along a closed
nonreflexive path. Its computation at `refl` is only propositional for open
terms, which the requirement permits.

Consequences for every item below:

- **Computation ships with every type former.** A new type former, or a
  generated rule of H, ships with composition, transport and constructor
  computation, including computation of its eliminator on formal
  compositions, in both the native and reference checkers.
- **No regularity for `Path`.** Nothing adds strict J computation or general
  regularity to `Path`. General regularity is not known to be compatible with
  Glue, which univalence uses (HoTT invariant 3). An identity type with strict
  J computation exists only as the separate declared family `Id` (H2).
- **Assumptions stay visible.** An assumption that remains, such as an
  explicit resizing axiom, is named and reported as a non-computing
  dependency. Results that use it are outside the requirement and do not
  compute.
- **Canonicity regression.** Closed assumption-free results are normalized to
  canonical values before and after each change. The regression exists as
  [canonicity.cubist](../examples/hott-automation/canonicity.cubist), checked
  by `tests/hott-automation.test.mjs`. Extend it with each new type former and
  each stage of H.

## Priority

1. **G0.** Universe-generic definitions are needed before H, because every H
   declaration is level-generic, and before the rebuild states anything
   generic.
2. **H1**, with G2's resizing policy. It adds the signature mechanism and its
   first class: data and higher inductive types. It makes truncation and set
   quotients computing declarations. On 2026-09-25, 1,266 of the 3,761 checked
   corpus declarations depended on the truncation assumptions. Of those, 455
   also used `LEM` and 3 used `Choice`; these can never compute. The rest would
   compute on a rebuilt foundation.
3. **H2**, indexed families, including `Id`.
4. **H3**, inductive-inductive types in which every sort is a set or a
   proposition. It is needed for Cauchy reals and for the syntax of type
   theory.
5. **G5**, when compact interval formulas block real proofs. It removes
   resource limits, not missing computation.
6. **G4**. It improves how open terms reduce; closed terms already compute.
7. **H4** only if a use appears.

G1 and G3 are superseded by H1 and H2. G2 remains as a policy that H1 applies.

## Items

- [ ] **G0. Check universe-generic definitions once, with `Uω` only as a type.**
  Today a declaration with a `U : Universe` parameter is a template. The
  elaborator specializes it at each universe where it is used, and the kernel
  checks only those copies. So a generic result is never itself a checked term,
  and it is unchecked at every level no one has used yet. G0 makes universe
  variables genuine kernel binders and checks each generic definition once, for
  every level.
  - **Specification.** [g0-universe-specification.md](g0-universe-specification.md) (K1.1): rules, consistency note, acceptance cases and open questions.
  - **Levels.** Level expressions are `0`, `ℓ + 1`, `max(ℓ, ℓ')` and universe
    variables, with `U(ℓ) : U(ℓ + 1)`. Two levels are equal when their normal
    forms agree: for each variable its largest offset, plus a constant. `ℓ ≤ ℓ'`
    is decided on those normal forms, so for example `max(x, x) = x` and
    `max(x + 1, x) = x + 1`. Existing cumulativity becomes symbolic:
    `U(ℓ) ≤ U(ℓ')` exactly when `ℓ ≤ ℓ'`, as in `U0 ≤ U(x) ≤ U(max(x, y))`.
  - **`Uω` is a type, never a term.** Its elements are the universes: `U0`,
    `U1`, universe variables and level expressions over them. `Uω` may only be
    the type of a binder (Π, λ or a declaration parameter). It cannot be an
    argument, occur in an expression, be compared, or have a type.
  - **Large types.** A Π over `Uω`, or a Π whose domain or codomain is large,
    is a large type. A large type may be the statement of a definition, or the
    type of a parameter (so a result can take a universe-generic function as an
    argument). It may be built further with Π. It is never an element of a
    universe, and never an argument to `Path`, `PathP`, Σ, W, Glue, composition
    or truncation. Large types are classified by a judgment, not by a universe,
    so no universe above `Uω` is needed. Nothing contains itself: in a model,
    levels are natural numbers, `U(n)` is the n-th of ω universes, and large
    types are sets above all of them that are never internalized.
  - **Instantiation** is application to a level expression. Its β-rule
    substitutes the level, avoiding capture of level binders.
  - **Cubical rules stay small-only.** `Path`, composition, transport and Glue
    work at `U(ℓ)` for every level expression; the CCHM rules are uniform in
    the level. Only level comparisons become symbolic, such as Glue's check
    that its partial types fit its base universe. Large types get no fibrancy
    structure, so G0 adds no composition rule.
  - **Computation.** Instantiation is β-reduction plus level substitution. Closed
    assumption-free results at small types still reduce to canonical values
    (invariant 10). A large type is never the type of a canonical value.
  - **Kernel scope.** Every typing rule now computes a concrete level: Π, Σ, W,
    Glue, pushouts and composition. Each must compute a level expression, or
    report "large". Conversion compares universes by level normal form.
    Serialization, the ABI and the reference checker gain level expressions
    and level binders.
  - **Language.** `U : Universe` becomes a real parameter of type `Uω`; the
    source spelling may stay `Universe`. Source gains level expressions, for
    example `next(U)` and `max(U, V)`, so that `Group(U)` can live in
    `next(U)`. Universe arguments stay explicit at first. Inferring them from
    level constraints belongs with argument inference in the ergonomics
    roadmap.
  - **What G0 deletes.** It removes schema specialization and the
    per-universe builtins (`builtin__ua__U<n>`). It also removes the
    per-universe assumption schemas (`Choice(U0)`, `Truncate(U1)`, …), the
    specialization bindings, template inspection, and the migration verifier's
    specialization probes. Univalence, function extensionality, choice,
    excluded middle and truncation each become one assumption or definition
    with a large type. With H1, truncation is the declaration
    `Trunc : ∀ U : Uω, U → U`, universe-preserving by construction.
  - **Precedent.** The Rust THTH kernel (`KanHarI/thth`) had universe variables
    `U_X : UUOmega` with `U0 ≤ U_X`. There, however, `UUOmega` was a term of a
    further universe `UUKappa`, and universe variables had no successor. G0
    removes the need for `UUKappa` by keeping `Uω` out of term position. It
    adds successor and `max`, which families such as groups over `U` need.
  - **Acceptance.**
    - Reject:
      - `Uω` as an argument, in an expression, or with a type;
      - a large type as a universe element, or as an argument to `Path`, Σ,
        Glue or truncation;
      - a universe variable used at a smaller universe;
      - downward lifting.
    - Check:
      - level normalization and symbolic cumulativity;
      - capture-avoiding level substitution under binders;
      - Glue and composition at a variable level;
      - computation of instantiated closed results in the canonicity fixture.
    - The native and reference checkers must agree on all of these.
    - Recheck the archived library's templates generically. Record each one
      that only checked at particular levels, rather than weakening the rules
      to accept it.
- [ ] **H. Inductive signatures: one mechanism for inductive, indexed, higher
  and inductive-inductive types.** The kernel checks a signature normal form
  and generates the rules. The
  [design](higher-inductive-types-design.md) specifies:
  - the normal form: sorts, data, positions as cubes, dimensions and
    boundaries;
  - one formal composition per sort, with index-line matching;
  - clause typing through the partial eliminator;
  - the proposed semantic route.

  Readable declarations are ergonomics milestone 7. The code is shared by all
  stages; the signature checker's gate widens one stage at a time.
  - **H1. One sort, no indices.** Data and higher inductive types: natural
    numbers, sums, W types, pushouts, suspensions, spheres, truncation
    `Trunc`, set quotients `Quotient`.
    - Reference checker first.
    - The hand-coded natural-number, sum, W and pushout rules are
      differential oracles. They retire only after typing, reduction and
      composition agree on the kernel tests and on the archived library.
    - Main obligation: transport along parameter lines with boundary
      correction.
  - **H2. One indexed sort.** Vectors, finite sets, well-typed syntax, and the
    identity family `Id`, whose J computes on `refl`. This replaces G3 without
    dedicated rules.
    - Main obligations: formal composition along varying indices, and
      stability of index-line matching under restriction to faces.
  - **H3. Several sorts, each a set or a proposition.** Quotient
    inductive-inductive types: Cauchy reals with closeness, the partiality
    monad, surreal numbers, the syntax of type theory.
    - Main obligations: induction-induction, and clause typing through the
      partial eliminator.
    - To our knowledge no system ships this class with full computation, so
      its soundness note is new work.
  - **H4. Several sorts, some untruncated.** Adopt only for a concrete use.
  - **Trust controls at every stage.**
    - A soundness note, reviewed before the stage's gate opens.
    - Until then, results that use a type the stage admits carry a
      `kernel extension: Hn` dependency. It is visible, but it is not a
      non-computing dependency.
    - Negative tests: positivity, boundaries that disagree on overlaps,
      boundary clauses, h-level misuse, index levels, forward references.
    - A canonicity statement, with fixture additions.
  - **Acceptance, per stage.**
    - The native and reference checkers agree on every generated rule.
    - Closed data results normalize, including through formal compositions.
    - The canonicity fixture computes the stage's showcase:
      - H1: the winding number of a loop in a declared circle;
      - H2: `J` on `refl` by `rfl`, and a vector append evaluated;
      - H3: a rational within 10⁻³ of √2 read from a closed real.
- [ ] **G1. Superseded by H1.** Computational truncation and set quotients are
  the declarations `Trunc` and `Quotient` at H1, with truncation also derivable
  as the quotient by the total relation. The three designs G1 compared are
  covered: dedicated constructors, a set quotient, and a construction from
  pushouts. The first two are H1 declarations. The third remains a library
  option, for comparing proof and computation cost.
- [ ] **G2. Resizing policy, applied by H1.** The archived library's
  [assumption schema](../../web/cubical-assumptions.mjs) declares
  `Truncate : U_l -> U0`, which includes universe lowering. `Trunc` at H1 is
  universe-preserving (`Trunc : ∀ U : Uω, U → U`) and provides no resizing.
  - The rebuilt library uses no resizing. Where the archive relied on it
    (`small_mere_eliminate`, large predicates, predicate-encoded quotients),
    the rebuild states results at the universe they need. Only if a result
    genuinely needs resizing does it use an explicitly named resizing
    assumption, reported as a non-computing dependency.
  - A quotient's level accounts for both its carrier and its relation
    universes. Small quotients avoid the predicate encoding's universe
    increase.
  - Acceptance: implicit downward resizing is rejected. For each archive
    result that used resizing, the rebuild records the universe changes and
    the assumptions removed or retained, separately from LEM and choice.
- [ ] **G3. Superseded by H2.** An identity type with strict J computation is
  the declared family `Id(A, a) : A -> type { refl }` at H2. Its J computes on
  `refl` because transport along a varying index stays a formal composition,
  so no dedicated kernel rules are needed. `Path`/`PathP` remain the primary
  equality interface. H2 must provide:
  - checked maps and comparison laws between `Id` and `Path`;
  - no UIP, and no identification of nontrivial loops;
  - documentation of which representation each tactic produces.
- [ ] **G4. Optional transport regularity for declared data types.** Let
  transport with an empty system along a literally constant family compute to
  its argument, including a neutral argument, for every H-declared type
  without path constructors. That covers natural numbers, sums, the unit and
  empty types, and user data types. Closed arguments already compute this way.
  - It would remove `transport_constant` corrections for such carriers. The
    archive has 23 such calls, for example `code_lower`'s at `Z`.
  - It is not strict J for `Path`, and it adds nothing for higher inductive
    types or neutral types.
  - It needs a soundness argument and implementations in both checkers, with
    interaction tests for Glue and formal composition. Rank it below H1–H3.
- [ ] **G5. Certified interval normalization.** The current native clause and
  work limits make exponential distribution fail promptly, and the elaborator
  simplifies constant-path reversal before checking. To accept general compact
  cubical expressions without raising those limits:
  1. Keep interval and face expressions as shared `join`/`meet`/`reverse` DAGs
     in the elaborator. Normalize only the parts needed by a conversion or face
     query, with memoization and a measured work budget.
  2. Emit a certificate of local De Morgan, substitution, absorption, and face
     entailment steps for each nontrivial query. Preserve dimension scope and
     distinguish interval equality from face entailment in the certificate.
  3. Add a small kernel verifier for those steps, then replace eager native DNF
     comparison at the certified call sites. Reject missing or oversized
     certificates; never trust the elaborator's claimed answer on its own.
  4. Test the 16-clause reversal on a genuinely nonconstant path, false face
     entailments, binder renaming, and adversarial shared DAGs before raising
     any resource limit. Compare checking time and proof size with the current
     guarded implementation.

## Validation

| Item | Must be rejected or preserved |
| --- | --- |
| G0 | `Uω` only as a binder's type; large types never universe elements or arguments to small type formers; level equality by normal form; symbolic cumulativity; capture-avoiding level substitution; instantiated closed results compute; both checkers agree |
| H1–H4 | Each stage's gate opens only with its soundness note; generated rules agree between checkers; hand-coded rules agree with H1 before retirement; positivity, boundary, h-level and index-level errors rejected; closed data results normalize through formal compositions; the stage showcase computes |
| G2 | Universe preservation distinguished from resizing; implicit downward resizing rejected; retained resizing named and reported |
| G3 (as H2's `Id`) | J computes on `refl`; checked connection to `Path`; no UIP or collapse of nontrivial loops |
| G4 if pursued | Neutral values of declared data types transport along constant families by conversion; neutral types and other type formers do not; both checkers agree |
| G5 if pursued | Missing, oversized or incorrect certificates rejected; interval equality distinguished from face entailment; dimension scope and binder renaming preserved; checking time and proof size compared with the guarded implementation |
| Every item | Closed assumption-free results normalize to canonical values; removed, retained and new assumptions recorded as non-computing dependencies |

Each item also needs `make test`, `make CC=clang sanitize`, independent
reference-checker tests, ABI/serialization checks and closed computation
examples for its kernel implementation. A documentation update alone does not
run these future implementation gates.
