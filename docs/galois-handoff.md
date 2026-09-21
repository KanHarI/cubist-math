# Galois development: resumption checkpoint

Updated 2026-09-21. Continue from this file and the
[full roadmap](galois-roadmap.md). All canonical proofs now use the cubical C
kernel and `.cubist` sources. The old Id/J engine, its proof exporters and
its reference-comparison commands are retired; older checkpoints describe
historical validation, not the current development workflow.

## Current increment

The general first group isomorphism theorem is checked:

```text
group_first_isomorphism(G, H, h) :
  GroupIsoAt(U1, KernelQuotientGroup(G, H, h),
    group_lift(ImageGroup(G, H, h)))
```

This is an isomorphism of bundled groups, including multiplication
preservation on arbitrary quotient elements. It reuses the previously
checked carrier equivalence and inverse maps without selecting preimages.
The quotient is represented in U1; its small image is explicitly repackaged
in U1. This is not a resizing argument.

| Module | Checked contribution |
| --- | --- |
| `group_universes` | `GroupAt(U)`, group laws, projections and `GroupIsoAt(U)` as universe schemas; the existing `Group` specializes this family at U0 |
| `quotient_sets` | General predicate-quotient setness via constant paths; dependent function setness via a pointwise square of paths |
| `quotient_operations` | Descent of binary operations, computation on classes, two- and three-variable propositional induction |
| `quotient_groups` | Multiplication, inversion, all group laws for arbitrary cosets, `QuotientGroup`, and `group_lift` |
| `group_first_isomorphism` | Multiplicativity of the existing quotient-to-image map and the bundled group isomorphism |

The generic group templates are checked at specialization. Regression tests
exercise U0, U1 and repackaging into U2. This does not claim a new primitive
universe-polymorphic term in the kernel.

## Constructivity and homotopy

No LEM, choice, new axiom, or kernel rule was added. Exact remaining axiom
families for the first isomorphism theorem are `Truncate`, `TruncateIntro`,
`TruncateElim`, and `TruncateProp`, specialized at U0 and U1. General quotient
setness only needs `Truncate`, `TruncateElim`, and `TruncateProp` at U1.
The construction of `QuotientGroup` additionally uses `TruncateIntro(U1)`.
The existing truncation interface itself retains its established universe
signature; this increment does not strengthen it.

Function extensionality and univalence are derived in the cubical kernel.
The existing `kernel_quotient_image_equality` identifies quotient and image
**carriers** via univalence. The new function-setness proof is an explicit
higher path (a square). Group laws are proposition-valued; arbitrary
representatives are never selected from truncation.

The structure identity equivalence for small `Group` remains available.
Its extension to `GroupAt(U1)` has not been proved: do not describe the new
large-group isomorphism as an equality of bundled groups yet. Carrier equality
alone is insufficient for that claim.

## Existing Galois development

Stage 1 of the roadmap has subgroups and subfields, normal kernels, subgroup
carriers, homomorphisms and images, generated subfields, intersections,
composita with specified embeddings, and Lang's distinguished-class interface.
Fixed fields and fixing subgroups form an order-reversing Galois connection.
Automorphisms are identified with loops of extension structures, acting by
transport. The F4/F2 automorphism group is identified with the cyclic group
of order two, and the decidable subobjects have a checked correspondence.

Useful modules: `galois_paths`, `galois_orders`, `f4_galois_correspondence`,
`distinguished_extensions`, `embedded_composita`, `field_embedding_image`,
`group_cosets`, `group_quotient_maps`, and `kernel_quotient_image`.
See [the development guide](galois.md) for the earlier constructions.

The general fundamental theorem of Galois theory is **not proved**. Finite
linear algebra and extension degree, polynomial theory, algebraic extensions,
separability, normal field extensions, and Artin's fixed-field theorem remain.
Algebraic closures and the infinite correspondence with Krull topology are
separate later stages. `AlgebraicField` is the unordered field interface; its
name does not assert that an extension is algebraic.

## Next work

1. Bundle quotient projection and descended maps as universe-polymorphic
   homomorphisms, and state the group universal property. Reuse
   `group_quotient_map_unique`; arbitrary-coset multiplication is now available.
2. Add a concrete non-normal subgroup example. The existing negative test
   rejects missing normality evidence syntactically; it is not that example.
3. Generalize structure identity to larger bundled groups where useful, so
   first-isomorphism results can be used as paths of complete structures.
   Preserve the coherent equivalence and its roundtrips.
4. Begin explicit finite linear algebra and degree as specified in stage 2.
   Keep constructive hypotheses visible; a finite carrier alone does not
   decide arbitrary proposition-valued subobject membership.

## Validation and workflow

Final validation of this increment: **248 tests passed**. The complete corpus
checked **2,522 concrete declarations and 32 universe templates**, with no
failed, blocked, or over-budget declarations at the regression deadline.
The browser landing regression also passed, including the new first
isomorphism theorem and its folded `KernelQuotientGroup` / `ImageGroup` names.
All seven changed mathematical sources pass the formatter. The all-source
formatter check still reports four pre-existing files (`bouquet_actions`,
`bouquet_cover`, `bouquet_generation`, and `primes`); they were not changed
in this increment.

Selected checks for this increment:

```sh
npm test -- quotient_groups group_first_isomorphism circle_group_identity
npm test -- tests/quotient-groups.test.mjs tests/proof-library.test.mjs
node tests/landing.browser.mjs
node tools/format-mathscript.mjs --check
```

The focused regression checks the general theorem, identity/trivial
homomorphism specializations, the U2 group specialization, truncation-only
assumptions, and rejection of missing normality and silent universe lowering.
The browser regression checks the circle and group-univalence landing links
and folded kernel inspection. A new registry regression checks that every
bundled source import is permitted by the browser worker: the new
`group_universes` import initially exposed this missing-registration bug.

Run the whole library once at the end of a mathematical batch, not after
every edit. `npm test` also runs the current native-kernel regressions.
Check exact assumptions as well as successful type checking.

Use `with unfolding [left_coset] { ... }` when class-constructor conversion
would otherwise expand the entire quotient recursor. Check generic
constructors against abstract carriers before specializing to large terms
(`group_iso_object_at` follows this pattern). These are elaborator hints;
the kernel still verifies all conversions.

Register new modules in `web/mathscript/modules.mjs` and
`web/proof-library.mjs` when introducing imports, so the live website remains
usable during development. Source comments supply inspector documentation.
Pushes to main publish the website; deployment checks are separate from
mathematical validation.
