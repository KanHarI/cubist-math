# Homological algebra

Status: proposal merged in #198; HA0–HA6 remain unimplemented at main
`e729c2d5` on 2026-10-17. Proposed on 2026-10-07 at the maintainer's request.
On 2026-10-17 the maintainer selected categories, monads, algebraic homology
and synthetic cohomology as a sustained language-development testbed.
The [work plan](../work-plan.md#first-actions) owns its staged progression.
This selects the direction without claiming any HA milestone implemented;
the paused analysis, Galois and RH projects remain separate.

- **Algebraic side (HA1–HA3, HA5).** Builds on the
  [categories roadmap](../high-level-abstractions/categories.md).
- **Synthetic side (HA4).** Builds on what H1 and the library already
  provide, developing the path, induction, transport and h-level tools that
  its larger constructions need.

Both sides are central. The objective is to develop and test broad language
capabilities through substantial mathematics, rather than minimize the path
to a homology or cohomology result. A small explicit proof establishes a
baseline; the corresponding language feature must also make its intended
interface usable and support its stated fragment. Repeated boilerplate or
failed inference feeds the shared language design instead of becoming a
collection of theorem-specific workarounds.

## Why Cubist

- **Univalence removes the bookkeeping of "up to isomorphism".**
  - Isomorphic modules and complexes are equal, so every construction is
    invariant without being shown so.
  - In a univalent category, kernels, cokernels and biproducts are unique
    up to equality, so "the kernel" is well defined.
  - "Exact" is a proposition, not a choice of data.
- **Diagram chases match truncation.** A chase produces "a preimage merely
  exists" and concludes a proposition, exactness or an equation. That is
  exactly what eliminating a truncation into a proposition allows.
  - The snake lemma's connecting map lands in a quotient, where the class
    of a preimage is unique.
  - So it is extracted from mere existence without the axiom of choice,
    and it computes.
- **Computation.**
  - Cubical univalence computes here: the circle's winding number
    reduces by `rfl` ([winding](../../examples/h1/winding.cubist)).
  - Cubical Agda computes cohomology groups and rings in the same
    setting: Brunerie, Ljungström and Mörtberg, synthetic integral
    cohomology (CSL 2022); Ljungström and Mörtberg, cohomology rings
    (CPP 2023).
  - `computable` and `evaluate` would do the same for connecting maps and
    cohomology classes.
- **The synthetic route uses what exists.** Cohomology can be defined as
  `H^n(X; G) := ‖X → K(G, n)‖₀`, with Licata and Finster's
  Eilenberg–MacLane spaces (LICS 2014). That needs:
  - higher inductive types: suspensions and pushouts, and 2-cells (H1
    admits the square torus);
  - truncations: groupoids with `trunc(1)`, and sets;
  - the library's univalence.
- **Theories fit.** A chain complex is a theory with a module for each
  vertex of its shape and a linear differential along each edge, so it is
  a diagram over the shape. Its derived morphisms are exactly chain maps
  ([categories](../high-level-abstractions/categories.md), L2.4d). The abelian tower (L3.6) applies
  pointwise, and limits and colimits of complexes are computed index by
  index.

## Constraints

- **The axiom of choice is not assumed.**
  - Sets are projective only under it, so "enough projectives", injective
    resolutions and the Freyd–Mitchell embedding are out in general.
  - Ext is reached by routes that need no choice:
    - Yoneda extensions, formalised in univalent foundations by Flaten
      (ITP 2023);
    - free resolutions over ℤ of groups given with a finite presentation:
      Smith normal form diagonalizes the relation matrix, because ℤ has
      decidable equality;
    - the synthetic route.
  - **A presentation is data, not a property.** Constructively, a finitely
    generated group need not be finitely presented. For any proposition
    `P`, `ℤ/{k | k = 0 ∨ P}` is cyclic, and a finite presentation of it
    would decide `P`: Smith normal form would decide whether `[1] = [0]`
    ([Julian, Mines and Richman, §1](https://msp.org/pjm/1983/106-1/pjm-v106-n1-p10-s.pdf)).
    So HA5 takes a presentation, or a resolution, as input, and HA3's
    complexes are given by their matrices.
  - **Cellular cohomology is compared on finite complexes.** Buchholtz and
    Favonia's comparison covers finite CW complexes
    ([Cellular cohomology in HoTT](https://favonia.org/files/cohomology-lics2018.pdf),
    Theorem 7.1). Their wedge axiom asks the cells' index sets to satisfy
    choice, which finite sets provably do (§6). Infinite complexes are
    open there, and may need countable choice (§9), so HA6 defers them.
  - **Infinite limits need care.** The categories roadmap's diagrams may
    be infinite ([decision 10](../high-level-abstractions/categories.md#decisions)), but some
    classical facts about them need choice:
    - a tower of surjections between nonempty sets can have an empty limit
      without dependent choice. So "Mittag-Leffler implies lim¹ = 0" needs
      it, which is what makes lim¹ vanish in Milnor's sequence for
      infinite complexes;
    - a product of surjections is surjective only with choice, so infinite
      products of abelian groups are not exact;
    - set truncation commutes with a product over `I` only when `I`
      satisfies set-level choice, the wedge axiom's condition above.

    Such results are avoided, or stated with the choice they need as a
    hypothesis. The definitions do not change.
- **Indexing.**
  - The library's integers are a quotient of pairs of naturals, so
    `(n - 1) + 1 = n` holds only up to a path. Complexes indexed by
    `C(n - 1)` would need a transport at every differential.
  - Complexes are indexed by a **complex shape** instead: a graph on the
    indices in the categories roadmap's sense
    ([decision 10](../high-level-abstractions/categories.md#decisions)), whose edges are
    propositions, with at most one successor and one predecessor at each
    index.
    - **Examples.** Cochain complexes over ℤ take `E(i, j) := j = i + 1`.
      Chain complexes over ℕ take `E(i, j) := i = j + 1`, so `0` has no
      successor.
    - **Not a successor function.** A function would put an edge at every
      index: truncated predecessor on ℕ would add `0 → 0`. Then `X₀ = ℤ²`,
      with the higher modules zero and `d(a, b) = (b, 0)`, would satisfy
      `d ∘ d = 0` without being a chain complex.
    - **A complex is a diagram over its shape** in a preadditive category,
      with `d(j, k, e') ∘ d(i, j, e) = 0`. The differential
      `d(i, j, e) : X(i) → X(j)` takes a proof `e : E(i, j)`, and
      `X(j)` is indexed by `j` itself, so index arithmetic never meets a
      type.
    - **Chain maps** are morphisms of diagrams, and limits and colimits of
      complexes are computed index by index.
    - **mathlib's form is derived.** mathlib's `ComplexShape` gives
      `d(i, j)` for every `i` and `j`, with a law that it is zero unless the
      indices are related. The graph form needs neither that law nor a
      decidable relation. Where the relation is decidable, as on ℤ and ℕ,
      mathlib's form is derived from it. mathlib too keeps its relation
      apart from its convenience function `next`, whose fallback adds no
      edge.
- **Truncation levels are literal.**
  - `trunc(n)` needs an integer, not a variable (E114, checked on
    2026-10-07). So `K(G, n)` for every `n` needs the hub-and-spoke
    truncation (HoTT book §7.3), a one-sort higher inductive type with
    parameter `n`; whether H1 admits it is checked first in HA4.
  - Fixed low degrees, `K(G, 1)` and `K(G, 2)`, need only literal levels.
- **Composite boundaries are excluded.** H1 excludes a constructor whose
  boundary is a composite (its specification, Q3), so `K(G, 1)`'s cell
  `loop(g·h) = loop(g) · loop(h)` is written as a square.
  `library/squares.cubist` converts between the two forms (L2.8).
- **Cost.**
  - Cubical computations of cohomology can be expensive: the Brunerie
    number took years of work in Cubical Agda.
  - Large coefficients need binary numerals (notation L2.10f); unary
    naturals make them slow.
  - Real computations depend on the kernel's stage-6 performance work.

## Limits and colimits

The categories roadmap's diagrams, maps of graphs
([decision 10](../high-level-abstractions/categories.md#decisions)), serve both sides:

- **Complexes** are diagrams over their shapes, as above.
- **HA1.** Kernels and cokernels are L3.5's equalizers and coequalizers
  with the zero map, and an image is the kernel of a cokernel.
- **HA4.** Suspensions, pushouts, cofibers and wedges are instances of the
  higher inductive `Colim`, and fibers are limits of types.
  - `Colim` and `Lim` check with `hlevels` alone, so HA4 still waits for
    none of the categories packages.
  - HA4 keeps dedicated types, such as `Pushout` and the suspension, with
    conversions to `Colim`.
- **HA5.** The Baer sum, and Ext¹'s functoriality in each argument, use
  pullbacks and pushouts in the category of modules.
- **HA6.** Each stage of a CW complex is a pushout. An infinite complex is
  a sequential `Colim` over `Nat`, which HA6 defers.

## Milestones

| Milestone | Content | Acceptance | Depends on |
| --- | --- | --- | --- |
| **HA0** Prerequisites | Categories roadmap: L2.4d, L2.11, L2.12, L3.4–L3.6, with `Module(U, R)` and lifting operations through set quotients | Theirs | — |
| **HA1** Modules and exactness | Submodules as predicates; image, kernel, cokernel; `Exact(f, g)`; short exact sequences; the isomorphism theorems | First isomorphism theorem; the five lemma; the snake lemma, its connecting map computed by `evaluate` on a small example | HA0 |
| **HA2** Chain complexes | Complex shapes as graphs; complexes, diagrams over them, and chain maps derived from a theory; homology as a quotient module; chain homotopies; functoriality | The long exact sequence in homology of a short exact sequence of complexes; homotopy invariance; `H_1 ≅ ℤ` for a small complex of the circle | HA1 |
| **HA3** Computing homology | Smith normal form over ℤ, proved correct and `computable` | `evaluate` the homology of finite free complexes; torsion found, as `ℤ/2` for the real projective plane's complex | HA2; binary numerals |
| **HA4** Synthetic homotopy and cohomology | Library spheres and suspensions; `π_n` as truncated loop spaces; the long exact sequence of a fibration; `K(G, 1)`, then `K(G, n)`; `H^n(X; G)` with its group structure; Mayer–Vietoris from pushouts | `H^1(S^1; ℤ) ≅ ℤ` computes; `H^n(S^m)`; the torus | H1, the library's univalence and squares; mostly not HA0 |
| **HA5** Ext | Yoneda Ext; Ext and Tor over ℤ for finitely presented groups, given by their presentations, through free resolutions | Ext¹ classifies extensions; `Ext¹(ℤ/n, ℤ) ≅ ℤ/n` | HA1, HA3 |
| **HA6** The bridge | Cellular cohomology of finite CW complexes built from pushouts, agreeing with the synthetic definition, as Buchholtz and Favonia showed in HoTT (LICS 2018, Theorem 7.1); infinite complexes deferred | Agreement on spheres and the torus | HA2, HA4 |

Spectral sequences are later work. Exact couples are ordinary algebra, but
formalising spectral sequences is large. The Lean 2 HoTT library's
spectral sequences (van Doorn and others) show the scale.

## Order

Follow the [work plan's language progression](../work-plan.md#first-actions).
Categorical interfaces, monads and universal constructions develop alongside
HoTT proof tools and low-degree synthetic examples. Readiness of a short
synthetic route is not a reason to skip that language work; equally, synthetic
cohomology does not wait for the full abelian tower or chain-complex library.
Its first pilots retain the original mathematical targets:

1. The circle, suspensions and spheres in `library/`. Today they are test
   declarations.
2. `π_1(S^1) ≅ ℤ`, from the winding example.
3. `K(G, 1)` for an abelian group `G`, with the multiplication cell as a
   square.
4. `H^1(X; G)` and `H^1(S^1; ℤ) ≅ ℤ` by evaluation.

Use those pilots to exercise higher-inductive admission and elimination,
square boundaries, path induction, transport, truncation and computation.
Admission of the proposed `K(G, 1)` presentation and its proofs are gates;
the general `K(G, n)` construction keeps the open truncation question below.
None of these theorems is recorded as delivered merely because the required
kernel forms exist.

The algebraic side, HA1–HA3, follows the categories packages and exercises
theory families, derived maps, quotients and reusable diagram proofs. Monads
and their notation are companion language work, not new mathematical
prerequisites for HA1. HA5 follows HA1/HA3; HA6 compares the algebraic and
synthetic strands after HA2/HA4. Each retains the table's acceptance gates.

## Language work it drives

| Testbed | Language capability to develop and validate |
| --- | --- |
| Categories, modules and chain maps | Proposition laws, implicit operation arguments, theory families and inheritance, explicit morphism capabilities, universe-correct interfaces and composition notation |
| Monads and substitution | Lawful operation records, functors and natural transformations, L2.6's universal proofs, scoped `do`/arrow notation, exhaustive bind patterns and transparent dependencies |
| Kernels, cokernels, exactness and complexes | Quotient lifting, extensionality, structure identity, reusable diagram reasoning and dependent rewriting; complex shapes avoid unnecessary arithmetic transports |
| Spheres, `K(G, n)` and synthetic cohomology | Higher constructors and boundaries, induction motives, path algebra, transport, truncation, h-level automation and computational equivalences |
| Computed homology/cohomology and their comparison | Binary foundations, evaluation and kernel performance with preserved proof meaning and measured resource costs |

Every strand uses the existing source-test, inspection and contextual-REPL
facilities. Compare the intended notation and inferred proofs with explicit
checked versions, including meaningful refusals and dependency reports.
Promote shared proof patterns to reusable language/library interfaces and test
them on distinct instances. Proposed diagram views, grading notation or new
kernel features need a concrete example and their own acceptance contract;
the testbed does not automatically authorize every possible extension.

## Open questions

1. **Shapes or ℤ.** Indexing by complex shapes, graphs whose edges are
   propositions, is recommended. The alternative is a second, inductive
   integer type for indices, whose successor and predecessor are inverse
   by computation on canonical forms only.
2. **`K(G, n)` for every `n`.** The hub-and-spoke truncation, if H1 admits
   it, or fixed low degrees until a variable-level truncation exists.
3. **Large categories.** The category of modules over `R : CommRing(U)` has
   objects in `next(U)`. Generic definitions at tier 1 are refused today
   (E1 and E2, deferred), which may limit statements about categories of
   categories. For the same reason, limits at every size are not one
   statement, so completeness is stated relative to a universe
   ([categories](../high-level-abstractions/categories.md#decisions), decision 10).
