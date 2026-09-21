# Finite mathematics: conversion hints and checked specialization

The native editions of `permutations`, `binomial_pascal`, and
`kernel_quotient_image` preserve their original public theorem statements and
assumptions. The legacy sources remain unchanged. The frontend source registry
must select the corresponding files under `web/proofs/cubical/`.

## Permutations

`permutation_split_join` uses selective unfolding of `sigma_first`,
`sigma_second`, `fst`, `snd`, `permutation_split`, and `permutation_join`.
This exposes the tuple wrappers while keeping the substantial bijection proofs
folded. Its applied pair-induction branch checks in 4,497 reduction steps instead
of exhausting ten million.

The selective converter must also retain the existing pair-eta comparison:
`(fst p, snd p)` and `p` are definitionally equal. Relegating that existing rule
to the unrestricted fallback caused unrelated permutation definitions to expand
first. Kernel checkpoint `226b18b` enables pair eta in the selective pass and
tests both the real permutation fixture and rejection of a wrong second
component. This is a strategy refinement, not a new equality axiom.

## Pascal's identity

`pascal_right` selects only `pascal_right_omitted`. The affected native fixture
checks in 4,304 reduction steps. The case split and both supplied branch proofs
are otherwise unchanged.

## Kernel quotient and image

`kernel_quotient_to_image_beta` selects `kernel_quotient_to_image` and
`left_coset`. The identical beta judgment checks in 8,577 reduction steps.
Its quotient recursor and image proofs remain named.

Building the final equivalence repeatedly elaborated a large inlined U1
specialization of the universe-polymorphic adjointification proof. A single
named specialization completed under the step budget, but exceeded the new
one-second declaration deadline. The native edition therefore checks the
counit, naturality, self-naturality, interchange, and inverse-cancellation
specializations separately. The original adjoint triangle proof is then checked
using these named lemmas, and the equivalence constructor assembles their
results. The forward map, inverse map, supplied unit, and corrected counit have
the same contracts as `equiv_from_inverse(U1, ...)`.

These local helper declarations avoid repeatedly expanding generic proofs
inside concrete quotient types. They add no assumptions. A future cache of
independently checked universe-schema specializations in the frontend could
replace this local factoring without changing the mathematics.

## Validation

Using the main native WASM checker and benchmark runner with an isolated source
loader, the combined import graph produced:

| Category | Count |
|---|---:|
| Checked within one second | 543 |
| Needs optimization | 0 |
| Blocked by another declaration | 0 |
| Failed checking | 0 |
| Universe templates, checked at specialization | 16 |

The factored adjoint triangle took about 549 ms in that run; other new local
specializations took less than 100 ms. Timings are machine-dependent and include
elaboration and native checking, with imports checked once. No normalization
request or old-kernel fallback was used.

The experimental kernel regression suite passes all 162 tests, including the
selective-unfolding and pair-eta fixtures. The focused unfolding suite also
passes against the UBSan native build.

Captured fixtures must preserve each prior definition's `unfoldingHints` from
`definitionViews` when replayed. Otherwise an earlier hinted theorem can exhaust
the replay budget before the reported target is even reached.

## Circle degree

The native `circle_degree` edition retains its public statements and supplies
two propositional computation paths that the legacy edition treated as
judgmental equalities. Rebasing a loop along reflexivity is identified with the
original loop using `transport_constant`. The single positive generating loop,
constructed as `refl(base)` followed by `loop`, is identified with `loop` using
`left_unit` before applying the contraction argument. The complete circle-degree
import graph checks 226 declarations within one second, with no slow, blocked,
or failed declarations and 16 universe templates.

## Embedded fields and analysis estimates

Five further native editions remove conversion or repeated-checking bottlenecks
without changing any original declaration's statement or assumptions:

- `embedded_composita` selects `AlgebraicField`, `EmbeddedCompositum`, and
  `embedded_compositum_subfield` in the commutativity proof. The carrier alias
  matters as well as the endpoints: the inferred congruence family contains
  `Structure(FieldData)`, whereas the declared family names `AlgebraicField`.
  Exposing that alias lets the selective pass finish in 4,035 reductions.
- `f4_embedding_images` selects `embedding_image_field` in the base-field
  identification. The image construction itself remains folded.
- `f4_embedded_composita` selects the same field/compositum aliases and
  `embedding_image_field` in its idempotence identification.
- `complex_norm_coordinates` divides the existing 55 ring rewrites into seven
  named, independently checked segments. The final norm-product proof composes
  these segments. This preserves every original ring rewrite while avoiding
  repeated checking of a single deeply nested proof; the final declaration
  took about 439 ms in the isolated run.
- `affine_partition_refinement` separates the per-piece endpoint conversion
  from fixed-mesh partition assembly. The continuity theorem supplies the mesh
  and calls the checked assembly lemma. The two helpers took about 218 ms and
  281 ms; all 437 declarations in its import graph passed the one-second limit.

These timings are representative observations, not fixed performance bounds.
The complex-norm import graph passed all 78 declarations. The compositum import
graph passed its assigned field declarations; four unrelated Galois-path
bottlenecks and their dependents were still being optimized separately when
this checkpoint was measured.
