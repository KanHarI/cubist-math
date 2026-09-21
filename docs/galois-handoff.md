# Galois development: resumption checkpoint

Updated 2026-09-21. Continue from this file and the
[full roadmap](galois-roadmap.md). All canonical proofs now use the cubical C
kernel and `.cubist` sources. The old Id/J engine, its proof exporters and
its reference-comparison commands are retired; older checkpoints describe
historical validation, not the current development workflow.

## Current increment

The bundled quotient universal property is now checked. For a small group
G, a normal subgroup S, any H : GroupAt(U1), and a homomorphism
h : GroupHomAt(U1, group_lift(G), H) killing S, there is a unique
factor : GroupHomAt(U1, QuotientGroup(G,S,normal), H). Its composite with
`quotient_projection` equals h as a complete homomorphism record.

`quotient_group_universal.cubist` contains:

- `quotient_projection`, `quotient_projection_kills`;
- `quotient_descend_map`, its beta and arbitrary-coset multiplication laws;
- `quotient_descend_hom`, `quotient_descend_triangle`, `quotient_descend_unique`;
- `quotient_group_universal`, packaging existence and uniqueness;
- `quotient_projection_epimorphism`;
- `quotient_descend_agrees_with_map`, compatibility with the earlier small-target recursor.

`group_hom_universes.cubist` supplies `GroupHomAt(U)`, projections,
composition, identity, and homomorphism extensionality. The original
`GroupHom` / `GroupHomLaws` now specialize this family at U0. Extensionality
constructs a cubical dependent pair path, using the proposition-valued law
field; it does not postulate proof irrelevance. Templates are tested at
U0, U1, U2, and U3.

The universal property needs only `Truncate(U1)`, `TruncateIntro(U1)`,
`TruncateElim(U1)`, and `TruncateProp(U1)`. No LEM, choice, new axiom, or
kernel change was introduced. Regression checks that descending the
projection to its own (genuinely U1) quotient gives the identity homomorphism.

## Previous increment

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

1. Add a concrete non-normal subgroup example. The negative test rejects
   missing normality evidence syntactically; it is not that example.
2. Generalize structure identity to larger bundled groups where useful, so
   first-isomorphism results can be used as paths of complete structures.
   Preserve the coherent equivalence and its roundtrips.
3. Begin explicit finite linear algebra and degree as specified in stage 2.
   Keep constructive hypotheses visible; a finite carrier alone does not
   decide arbitrary proposition-valued subobject membership.

The quotient construction still starts from a small source group and small
subgroup predicates. The universal-property target may be any group in U1.
No quotient universe lowering has been proved.

## Validation and workflow

Current final validation: **255 tests passed**. The complete corpus checked
**2,537 concrete declarations and 44 universe templates**, with no failed,
blocked, or over-budget declarations at the regression deadline. The browser
landing regression passes, including the quotient universal-property page
and folded `QuotientGroup` / `GroupHomAt` names.

All 415 concrete declarations in the quotient universal-property import
graph passed the focused 100ms benchmark, with 35 templates counted
separately. The U0–U3 schema checks, quotient-as-target identity test,
small-homomorphism compatibility, and rejection of a missing killing
hypothesis pass. All four changed mathematical sources pass the formatter.
The previously known all-source formatter issues in `bouquet_actions`,
`bouquet_cover`, `bouquet_generation`, and `primes` were not changed here.

Selected checks for the current increment:

```sh
npm test -- quotient_group_universal group_first_isomorphism circle_group_identity
npm test -- tests/quotient-universal.test.mjs tests/quotient-groups.test.mjs tests/proof-library.test.mjs
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

For a concrete quotient target, prefer proving that the descended projection
is the identity by `quotient_projection_epimorphism` and the bundled triangle.
Inlining propositional induction into homomorphism extensionality caused
expensive conversion of the nested quotient. The epimorphism proof checks
under the 1,000,000-step diagnostic budget without new conversion hints.
