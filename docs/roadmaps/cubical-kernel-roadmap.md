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

- [ ] **G0. Check universe-generic definitions once, over tiered universes.**
  Today a declaration with a `U : Universe` parameter is a template. The
  elaborator specializes it at each universe where it is used, and the kernel
  checks only those copies. So a generic result is never itself a checked term,
  and it is unchecked at every level no one has used yet. G0 makes universe
  variables genuine kernel binders and checks each generic definition once, for
  every level.
  - **Specification.** [g0-universe-specification.md](g0-universe-specification.md) (K1.1, revised on 2026-09-25 for tiered universes): rules, consistency note, acceptance cases and open questions.
  - **Tiered universes.** Universes are indexed by ordinals below ω². The
    constants are `U0, U1, …` (level `n`), `UU0, UU1, …` (level `ω + n`),
    `UUU0, UUU1, …` (level `ω·2 + n`), and so on, one more `U` per tier. A
    constant always carries its index. Names of the shape `U+[0-9]+` are
    reserved, and `U`, `UU` and `UUU` stay free for user variables. Every
    universe is an ordinary term: `U_n : U_{n+1}`, `UU0 : UU1`. Cumulativity
    crosses tiers: `U_n ≤ UU0 ≤ UU1 ≤ … ≤ UUU0 ≤ …`.
  - **Levels.** Level expressions are constants, `ℓ + 1`, `max(ℓ, ℓ')` and
    universe variables. A normal form is either a tier-0 constant plus an
    offset per variable, or a constant of tier 1 or above, which absorbs
    every variable. Equality and `ℓ ≤ ℓ'` are decided on normal forms, so for
    example `max(x, x) = x`, `max(x + 1, x) = x + 1` and `max(x, ω) = ω`.
    Existing cumulativity becomes symbolic: `U(ℓ) ≤ U(ℓ')` exactly when
    `ℓ ≤ ℓ'`, as in `U0 ≤ U(x) ≤ U(max(x, y)) ≤ UU0`.
  - **Universe binders.** `U < UU0` binds a universe variable that ranges
    over the universes below `UU0`: `U0, U1, …`. Examples are
    `def identity(U < UU0, A : U, x : A) := x;`, `forall U < UU0. B` and
    `fun (U < UU0) => t`. The bound is binder syntax, never a term, and only
    tier bases (`UU0`, `UUU0`, …) may be bounds. The word `Universe` is
    removed. G0 implements only `< UU0`, so universe variables denote natural
    numbers. `V < UUU0`, ranging over every `U_n` and `UU_n`, is admitted by
    the design and left as a later extension.
  - **Generic statements are ordinary types.** `forall U < UU0. B` lives in
    `UU0` when `U` occurs in the level of `B`, and at the level of `B`
    otherwise. So every type lives in some universe. A generic statement may
    be the statement or the value of a definition, the type of a parameter
    (so a result can take a universe-generic function as an argument), and an
    argument of Σ, `Path`, Glue, sums and composition.
  - **Instantiation** is application to a level expression below `UU0`. Its
    β-rule substitutes the level, avoiding capture of level binders.
    `identity(UU0, T, x)` is rejected.
  - **Cubical rules.** `Path`, composition, transport and Glue work at every
    level and tier; the CCHM rules are uniform in the level, so `UU0` is a
    fibrant universe like any other. One composition rule is added:
    composition at a level quantification is the level abstraction of
    composition at its body. It is sound because levels never vary along the
    interval. Otherwise only level comparisons become symbolic, such as the
    `max` of levels that Glue computes.
  - **Computation.** Instantiation is β-reduction plus level substitution. No
    reduction rule reads a level. Closed assumption-free results still reduce
    to canonical values (invariant 10), including results at UU-tier types
    and transports along lines of generic statements.
  - **Consistency.** Levels are modelled as ordinals below ω², with a
    Grothendieck universe for each, from ω² inaccessible cardinals. A level
    quantification is an ℕ-indexed product, which lies in `U_ω`. No binder
    ranges over all tiers and no bound is a term, so no universe above all
    tiers is needed.
  - **Kernel scope.** Every typing rule that computes a level (Π, Σ, W, sums,
    `Path`, Glue, pushouts, `U`) computes a level expression, and level
    quantification uses the rule above. Conversion compares universes by
    level normal form. Serialization, the ABI and the reference checker gain
    level expressions, bounds and level binders.
  - **Language.** `U < UU0` elaborates to a kernel level binder. Source gains
    `next(E)` and `max(E, F)`, so that `Group(U)` can live in `next(U)`.
    Universe arguments stay explicit at first. Inferring them from level
    constraints belongs with argument inference in the ergonomics roadmap.
  - **What G0 deletes.** It removes schema specialization and the
    per-universe builtins (`builtin__ua__U<n>`). It also removes the
    per-universe assumption schemas (`Choice(U0)`, `Truncate(U1)`, …), the
    specialization bindings, template inspection, and the migration verifier's
    specialization probes. Univalence, function extensionality, choice,
    excluded middle and truncation each become one assumption or definition,
    generic over `U < UU0`. `LEM`, `Choice` and `Truncate` have no instances
    at UU-tier universes. With H1, truncation is the declaration
    `Trunc(U < UU0, A : U) : U`, universe-preserving by construction.
  - **Precedent.** The Rust THTH kernel (`KanHarI/thth`) had universe variables
    `U_X : UUOmega` with `U0 ≤ U_X`. There, however, `UUOmega` was a term of a
    further universe `UUKappa`, and universe variables had no successor. In
    G0, `UU0 : UU1` is an ordinary successor inside the hierarchy. Because no
    binder ranges over all tiers, nothing needs a universe above them. G0 also
    adds successor and `max`, which families such as groups over `U` need.
  - **Acceptance.**
    - Reject:
      - a bound as a term, an argument or with a type; a bound that is not a
        tier base; the word `Universe`;
      - a generic statement in a universe below `UU0`;
      - instantiation at `UU0` or above, including `LEM` at `UU0`;
      - a universe variable used at a smaller universe;
      - downward lifting, within a tier and across tiers.
    - Check:
      - level normalization across tiers and symbolic cumulativity;
      - capture-avoiding level substitution under binders;
      - generic statements in `UU0` under Σ, `Path`, Glue and composition;
      - Glue and composition at a variable level and at `UU0`;
      - computation of instantiated closed results, and of a transport along
        a line of generic statements, in the canonicity fixture.
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
| G0 | Bounds only in universe binders, never terms; generic statements live in `UU0` or at their body's level; instantiation only below `UU0`; level equality by normal form across tiers; symbolic cumulativity across tiers; capture-avoiding level substitution; composition at a level quantification is pointwise; instantiated closed results compute; both checkers agree |
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
