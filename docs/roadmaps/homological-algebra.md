# Homological algebra

Status: proposed on 2026-10-07, at the maintainer's request; nothing here
is implemented. This is a new mathematical track. Mathematics beyond the
library's foundations is paused, so when it starts is the maintainer's
decision ([work plan](work-plan.md#open-decisions)).

- **Algebraic side (HA1–HA3, HA5).** Builds on the
  [categories roadmap](categories.md).
- **Synthetic side (HA4).** Builds on what H1 and the library already
  provide.

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
    reduces by `rfl` ([winding](../examples/h1/winding.cubist)).
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
- **Theories fit.** A chain complex is a theory with a family of modules
  and linear differentials. Its derived morphisms are exactly chain maps
  ([categories](categories.md), L2.4d). The abelian tower (L3.6) applies
  pointwise.

## Constraints

- **The axiom of choice is not assumed.**
  - Sets are projective only under it, so "enough projectives", injective
    resolutions and the Freyd–Mitchell embedding are out in general.
  - Ext is reached by routes that need no choice:
    - Yoneda extensions, formalised in univalent foundations by Flaten
      (ITP 2023);
    - free resolutions over ℤ for finitely generated groups, which are
      constructive because ℤ has decidable equality;
    - the synthetic route.
- **Indexing.**
  - The library's integers are a quotient of pairs of naturals, so
    `(n - 1) + 1 = n` holds only up to a path. Complexes indexed by
    `C(n - 1)` would need a transport at every differential.
  - Complexes are indexed by a **shape** instead, as mathlib does with
    `ComplexShape`. `d(i, j)` exists for every `i` and `j`, and is zero
    unless the shape's relation `next(i) = j` holds, so index arithmetic
    never meets a type.
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

## Milestones

| Milestone | Content | Acceptance | Depends on |
| --- | --- | --- | --- |
| **HA0** Prerequisites | Categories roadmap: L2.4d, L2.11, L2.12, L3.4–L3.6, with `Module(U, R)` and lifting operations through set quotients | Theirs | — |
| **HA1** Modules and exactness | Submodules as predicates; image, kernel, cokernel; `Exact(f, g)`; short exact sequences; the isomorphism theorems | First isomorphism theorem; the five lemma; the snake lemma, its connecting map computed by `evaluate` on a small example | HA0 |
| **HA2** Chain complexes | Complex shapes; complexes and chain maps derived from a theory; homology as a quotient module; chain homotopies; functoriality | The long exact sequence in homology of a short exact sequence of complexes; homotopy invariance; `H_1 ≅ ℤ` for a small complex of the circle | HA1 |
| **HA3** Computing homology | Smith normal form over ℤ, proved correct and `computable` | `evaluate` the homology of finite free complexes; torsion found, as `ℤ/2` for the real projective plane's complex | HA2; binary numerals |
| **HA4** Synthetic homotopy and cohomology | Library spheres and suspensions; `π_n` as truncated loop spaces; the long exact sequence of a fibration; `K(G, 1)`, then `K(G, n)`; `H^n(X; G)` with its group structure; Mayer–Vietoris from pushouts | `H^1(S^1; ℤ) ≅ ℤ` computes; `H^n(S^m)`; the torus | H1, the library's univalence and squares; mostly not HA0 |
| **HA5** Ext | Yoneda Ext; Ext and Tor over ℤ for finitely generated groups through free resolutions | Ext¹ classifies extensions; `Ext¹(ℤ/n, ℤ) ≅ ℤ/n` | HA1, HA3 |
| **HA6** The bridge | Cellular cohomology of CW complexes built from pushouts, agreeing with the synthetic definition, as Buchholtz and Favonia showed in HoTT (LICS 2018) | Agreement on spheres and the torus | HA2, HA4 |

Spectral sequences are later work. Exact couples are ordinary algebra, but
formalising spectral sequences is large. The Lean 2 HoTT library's
spectral sequences (van Doorn and others) show the scale.

## Order

HA4 can start first. It depends almost only on what exists, and it shows
what is distinctive here: cohomology that computes. Its first slices:

1. The circle, suspensions and spheres in `library/`. Today they are test
   declarations.
2. `π_1(S^1) ≅ ℤ`, from the winding example.
3. `K(G, 1)` for an abelian group `G`, with the multiplication cell as a
   square.
4. `H^1(X; G)` and `H^1(S^1; ℤ) ≅ ℤ` by evaluation.

The algebraic side, HA1–HA3, follows the categories packages, and HA5 and
HA6 follow both sides.

## Language work it drives

- Complex shapes and families indexed by a shape's elements (HA2).
- Commutative-diagram reasoning: the `category` simp set (L3.4), `ext` into
  limits (L3.5), and perhaps a diagram view in the inspector, like its
  boundary panel for squares.
- Notation for gradings and signs.
- Performance of cubical computation on higher inductive types (kernel
  stage 6), and binary numerals (L2.10f).

## Open questions

1. **When the track starts.** HA4 can start independently of the
   categories packages.
2. **Shapes or ℤ.** Indexing by complex shapes is recommended. The
   alternative is a second, inductive integer type for indices, whose
   successor and predecessor are inverse by computation on canonical
   forms only.
3. **`K(G, n)` for every `n`.** The hub-and-spoke truncation, if H1 admits
   it, or fixed low degrees until a variable-level truncation exists.
4. **Large categories.** The category of modules over `R : CommRing(U)` has
   objects in `next(U)`. Generic definitions at tier 1 are refused today
   (E1 and E2, deferred), which may limit statements about categories of
   categories.
