# Kernel extensions for computation in Cubist

Status: planning only, 2026-09-25. These items were split out of the
[HoTT and cubical automation roadmap](hott-automation-roadmap.md), whose
milestones A–F build on the existing kernel. They keep their labels G1–G4 so
that references there remain valid. G5 comes from the
[proof ergonomics roadmap](proof-ergonomics-roadmap.md#architecture-and-invariants).
Every item here changes the trusted C kernel or its query interface, so each
needs its own rule specification, native and reference implementations, and
review. No tooling or library release waits for this roadmap.

## Governing requirement: assumption-free results compute

Every closed term that checks without truncation or any other assumption must
reduce to a canonical value by kernel computation. This is a design priority,
not only a consistency property. It is invariant 10 of the
[HoTT roadmap](hott-automation-roadmap.md#invariants-added-to-the-ergonomics-requirements).

The current kernel has composition and transport rules for every type former:
`Nat`, `Unit`, sums, W types, pushouts, Glue, universes, Σ, Π and paths. Derived
path induction therefore computes on closed data, including along a closed
nonreflexive path. Its computation at `refl` is only propositional for open
terms, which the requirement permits.

Consequences for every item below:

- A new type former ships with composition, transport and constructor
  computation, including computation of its eliminator on formal compositions,
  in both the native and reference checkers.
- Nothing adds strict J computation or general regularity to `Path`. General
  regularity is not known to be compatible with Glue, which univalence uses
  (HoTT invariant 3).
- An assumption that remains, such as an explicit resizing axiom, is named and
  reported. Results that use it are outside the requirement and do not compute.
- A canonicity regression normalizes closed assumption-free results to
  canonical values before and after each change.

## Priority

1. **G1.** It is the only item that extends computation to results that use
   truncation. On 2026-09-25, 1,266 of the 3,761 checked corpus declarations
   depended on the truncation assumptions. Of those, 455 also used `LEM` and
   3 used `Choice`; these can never compute. The rest would compute once
   truncation is a real higher inductive type with computing eliminators.
2. **G2** with G1: computational truncation does not provide the current
   universe-lowering signature, so every resizing use must be migrated or made
   an explicit assumption.
3. **G5** when compact interval formulas block real proofs. It removes resource
   limits, not missing computation.
4. **G4**. It improves how open terms reduce; closed terms already compute.
5. **G3** last. A separate identity type with strict J computes, but the
   requirement does not need it, and it adds a second equality interface.

## Items

- [ ] **G1. Choose computational truncation and quotient foundations.** Compare
  three concrete designs before committing to a general recursive HIT mechanism:
  - A universe-preserving propositional truncation with point and squash
    constructors, dependent elimination into proposition families, and computation.
  - A computational set quotient with class, relation-path and sethood
    constructors. It directly serves cosets and Cauchy quotients; investigate
    deriving propositional truncation as the quotient by the total relation.
    Its square constructor makes it a larger first kernel change.
  - A library construction from pushouts and sequential colimits. This avoids
    additional kernel constructors but requires substantial checked mathematics
    and a comparison of resulting proof and computation costs.
  - Prototype one representative elimination for each viable design, then choose
    using constructor computation, universe behavior, proof size and checking
    cost. Prefer a focused truncation or quotient implementation before an
    unrestricted recursive HIT declaration mechanism.
  - Sources: [CHM's computational HIT rules](https://simhu.github.io/papers/hitcubical.pdf)
    and [van Doorn's construction from nonrecursive HITs](https://arxiv.org/abs/1512.02274).
- [ ] **G2. Separate resizing and validate the chosen implementation.** The
  current [assumption schema](../../web/cubical-assumptions.mjs) declares
  `Truncate : U_l -> U0`; this includes universe lowering. Standard computational
  truncation has `Truncate_l : U_l -> U_l` and does not provide that resizing.
  - Introduce independent source and target levels for proposition elimination.
    Audit `small_mere_eliminate`, large predicates and quotient users. Migrate
    their statements or retain an explicitly named resizing assumption where
    required; do not silently build the old signature into a new kernel rule.
  - A quotient's level accounts for both carrier and relation universes. Test
    small quotients without the current predicate encoding's universe increase,
    while documenting deliberate changes to existing public types.
  - Existing `HComp` and `Trans` rules are restricted to pushouts. New HITs need
    specified composition, parameter transport, face restrictions and eliminator
    computation on boxes, together with serialization and browser integration.
  - Acceptance: both checkers agree on point, squash/path and nonempty-box
    computation; changing carriers and relations is covered; resulting terms
    recheck. Reject wrong boundaries, elimination lacking the required h-level
    evidence, and implicit downward resizing. Audit removed and retained logical
    assumptions separately, including LEM and choice.
  - Migrate one truncation consumer and one quotient consumer; record the change
    in public universes, computation and dependencies. Complete these checks
    before generalizing the implementation into a broader HIT schema.
- [ ] **G3. Optional cubical identity type with strict J computation.** Keep
  `Path`/`PathP` as the primary equality interface. Only pursue a distinct `Id`
  if measurements show that propositional J computation is a material obstacle.
  - Specify its constructors, eliminator and judgmental computation rule, then
    checked maps and comparison laws connecting it with paths. It must not add
    UIP, equality reflection or automatic identification of arbitrary loops.
  - Acceptance: J at reflexivity computes as specified; the Path/Id interface
    supports nontrivial loop examples; existing cubical path computation remains
    covered. Document which representation every tactic produces and benchmark
    the benefit against the cost of maintaining two equality interfaces.
  - [Cubical Agda's Id/J interface](https://agda.readthedocs.io/en/v2.6.4/language/cubical.html#cubical-identity-types-and-computational-hott-uf)
    demonstrates compatibility of a separate cubical identity type with paths;
    it does not justify adding strict J to this kernel's existing Path rules.
- [ ] **G4. Optional transport regularity for closed inductive types.** Let
  transport with an empty system along a literally constant family of `Nat`,
  `Unit`, `Void` or a sum of these compute to its argument, including a
  neutral argument. Closed arguments already compute this way. This would
  remove the `transport_constant` corrections for such carriers, such as
  `code_lower`'s at `Z`; the corpus has 23 `transport_constant` calls. It is
  not strict J for `Path`, and it adds nothing for other type formers or for
  neutral types. It needs a soundness argument and implementations in both
  checkers, with interaction tests for Glue and pushout composition. Rank it
  below G1 and G2.
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
| G1–G2 | Universe preservation distinguished from resizing; truncation/quotient eliminators obey h-level restrictions; C/reference computation agrees; removed and retained assumptions recorded |
| G3 if pursued | Separate Id has its specified J computation and checked connection to Path; no UIP or collapse of nontrivial loops |
| G4 if pursued | Neutral values of closed inductive carriers transport along constant families by conversion; neutral types and other type formers do not; both checkers agree |
| G5 if pursued | Missing, oversized or incorrect certificates rejected; interval equality distinguished from face entailment; dimension scope and binder renaming preserved; checking time and proof size compared with the guarded implementation |
| Every item | Closed assumption-free results normalize to canonical values; removed, retained and new assumptions recorded |

Each item also needs `make test`, `make CC=clang sanitize`, independent
reference-checker tests, ABI/serialization checks and closed computation
examples for its kernel implementation. A documentation update alone does not
run these future implementation gates.
