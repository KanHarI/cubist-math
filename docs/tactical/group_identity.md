# Group isomorphism is equality

[Open the checked structure identity theorem](../../web/proof.html?proof=group_univalence).
[Open its application to the circle](../../web/proof.html?proof=circle_group_identity).

The formalization proves equality of the types themselves:

```text
group_isomorphism_is_equality(G, H) :
  GroupIso(G, H) =[U1] (G =[Group] H)
```

This applies univalence to the checked canonical equivalence
`group_structure_identity(G, H) : Equiv(U1, (G = H), GroupIso(G, H))`.
The notation `x =[T] y` specifies the carrier of an identity type. Suppressing
those annotations gives the landing-page formula `GroupIso(G, H) = (G = H)`.

Both results concern actual bundled groups `G` and `H`. The equivalence's forward function is the canonical
one: transport the identity isomorphism along a group equality. The inverse
constructs a group equality from an isomorphism. Both round trips are checked,
including the half-adjoint coherence required by our equivalence definition.
This is stronger than merely proving that isomorphic groups have equal carriers.

The source reference is Egbert Rijke's
[*Introduction to Homotopy Type Theory*, §19.3, Theorem 19.3.6](https://arxiv.org/pdf/2212.11082#page=275)
(printed p. 259). The book characterizes group identity by the canonical
identity-to-isomorphism map. Our proof builds the contractible family of groups
isomorphic to a fixed group, then applies a separately checked identity-system
argument. That follows the total-space approach underlying the book's structure
identity principle; we work directly with the repository's existing group
representation instead of first developing semigroups.

## Homomorphisms and normal subgroups

The subsequent group library uses this identity theorem in
[`normal_subgroups`](../../archive/first-library/normal_subgroups.cubist).
`group_conjugation_iso(G,g)` constructs the inner automorphism x ↦ gxg⁻¹.
`group_conjugation_path` turns it into a loop at G in `Group`, and
`group_conjugation_path_roundtrip` proves that decoding this loop returns that
same isomorphism. Inner automorphisms are not asserted to be identity maps.

[`group_operations`](../../archive/first-library/group_operations.cubist) projects inverse
witnesses already present in the laws and proves cancellation and conjugation
identities without axioms. The isomorphism constructor is a `def`, so its
forward map computes to conjugation. This separates computable structure data
from named proof obligations.

[`group_homomorphisms`](../../archive/first-library/group_homomorphisms.cubist) defines a
homomorphism as a multiplication-preserving map. Identity and inverse
preservation follow from the laws. Composition, identity maps and the trivial
map are explicit constructions; equality of homomorphisms uses function
extensionality and proof irrelevance of their preservation evidence.

[`subgroup_constructions`](../../archive/first-library/subgroup_constructions.cubist) supplies
the identity and whole subgroups, inclusion, inverse images and small-indexed
intersections with their universal properties. Inverse images respect
identity and composition as equalities of subgroup bundles. No global
membership decision is assumed.

`IsNormal(G,S)` means closure under conjugation by every element of G. Its
evidence is a proposition. Inverse images preserve normality, kernels are
normal, and intersections of normal subgroups are normal. Closure under
conjugation gives invariance in both directions, then univalent predicate
extensionality identifies the conjugated subgroup with the original bundle.
Transporting normality along a group equality uses path induction alone;
transporting it along an isomorphism first uses `group_isotoid`.

In [`f4_normal_subgroups`](../../archive/first-library/f4_normal_subgroups.cubist), the proof of
commutativity for the cyclic group of order two transports along
`f4_galois_group_equality` to prove `IsAbelian(F4GaloisGroup)`. Consequently all
subgroups of this Galois group are normal. This application uses univalence
and function extensionality, but no LEM or choice, and does not require
repeating the finite classification of automorphisms.

## What is equal?

`GroupLaws(A, unit, multiply)` is the type of group-law evidence.
`GroupStructure(A)` bundles operations and laws on a fixed carrier; `Group`
bundles the carrier as well:

```
Group = exists A : U0.
  exists unit : A.
    exists multiply : A -> A -> A.
      GroupLaws(A, unit, multiply)
```

Thus `G = H` includes the carrier, unit, multiplication and all law evidence.
`GroupIso(G,H)` uses multiplication-preserving bijections. Unit
preservation is derived; it is not silently added as a hypothesis. Inverses and
group-law evidence are proved unique where needed using the group laws and the
set condition on carriers.

`Group` lives in `U1` because its carrier ranges over `U0`. Consequently
its identity type is represented at that universe level too. The single
`Equiv(U, A, B)` definition takes an explicit universe parameter; the theorem
uses `U1`. Its underlying `IsEquiv(U, A, B, f)` is the same half-adjoint
equivalence data at every universe, and the derived `ua` operation accepts
it directly. No separate higher-universe equivalence definition remains.
This development bundles small groups; generalizing their carrier universe
is separate from generalizing equivalence itself.

Group equality is an identity type, not definitional equality or a truncated
claim of isomorphism. Different isomorphisms give different paths:
`group_isomorphism_paths_injective` proves that the inverse construction cannot
collapse them. The function used to generate these paths is
`group_isotoid`; its inverse is `group_idtoiso`.

## Checked modules

- [groups.cubist](../../archive/first-library/groups.cubist): named laws, bundled groups,
  projections, group induction, the identity isomorphism and `group_idtoiso`.
  This entire interface requires no axioms.
- [group_identity.cubist](../../archive/first-library/group_identity.cubist): uniqueness of
  inverses and law evidence, and preservation of units. Only uniqueness of
  function-valued law evidence needs function extensionality.
- [group_isomorphisms.cubist](../../archive/first-library/group_isomorphisms.cubist): an
  isomorphism is determined by its underlying function.
- [group_total_identity.cubist](../../archive/first-library/group_total_identity.cubist): the
  total space `exists H : Group. GroupIso(G,H)` is contractible, with center
  `(G, identity)`.
- [identity_systems.cubist](../../archive/first-library/identity_systems.cubist): a reusable
  identity-system construction, inverse laws, and an equivalence when the
  relation fibers are sets. These generic results require no axioms.
- [group_univalence.cubist](../../archive/first-library/group_univalence.cubist): isomorphism
  fibers are sets; the full group structure identity equivalence and both
  canonical inverse laws, followed by equality of the isomorphism and identity types.
- [circle_group_identity.cubist](../../archive/first-library/circle_group_identity.cubist): the
  already checked winding isomorphism yields `CircleLoopGroup =[Group] IntegerGroup`.
  The landing page links directly to the concise
  `circle_group_isomorphism : GroupIso(CircleLoopGroup, IntegerGroup)` theorem.
  `circle_loop_group_equals_integers` gives the subsequent equality.
  Decoding this equality recovers that same isomorphism.

The group equivalence and circle application use only the single univalence
axiom and function extensionality (`lib_univalence`, `lib_funext`).
The transport computation theorem is [derived from univalence](univalence.md). They use no excluded middle, choice, propositional
truncation, or theorem-specific axiom. The kernel implementation is unchanged.

## Canonical interface and reading order

Start with `groups.cubist`, then the law uniqueness arguments in
`group_identity.cubist`, then isomorphism extensionality. The total-space proof
is the only construction of group equality from isomorphism. The circle and
finite Galois examples both use it.

| Operation | Meaning | Assumptions |
| --- | --- | --- |
| `group_idtoiso(G, H, p)` | Transport the identity isomorphism along `p` | None |
| `group_isotoid(G, H, iso)` | Recover a group path from an isomorphism | Univalence, function extensionality |
| `group_isotoid_idtoiso(G, H, p)` | The path round trip equals `p` | Same |
| `group_idtoiso_isotoid(G, H, iso)` | The isomorphism round trip equals `iso` | Same |
| `group_structure_identity(G, H)` | Package these maps as an equivalence | Same |
| `group_isomorphism_is_equality(G, H)` | Identify the two types in `U1` | Same |

There is no second, independent `isomorphic_groups_equal` construction.
The `group_idtoiso`/`group_isotoid` names expose the directions, following the
`idtoequiv` convention. Earlier code called these `group_equality_iso` and
`group_identity_encode`. `GroupType` is now `Group`; the former `Group(A, ... )`
law predicate is now `GroupLaws(A, ...)`. These are source API changes;
the in-repository proofs, links, inspectors and examples have been migrated.

### Inverse data versus equivalence

`GroupIso` is represented by a forward map, an inverse, two inverse homotopies,
and multiplication preservation. On **sets**, the inverse evidence and law
proofs are propositions, so this presentation has the intended identity type.
`group_iso_ext` proves that equality of forward maps determines equality of
isomorphisms. No inverse witness is selected from a truncation.

For general homotopy types, quasi-inverse data alone is not our equivalence
representation. `IsEquiv(U, A, B, f)` in `paths.cubist` is a half-adjoint
equivalence with the explicit triangle law
`ap(U, A, B, f, g(f(x)), x, eta(x)) = epsilon(f(x))`.
`Equiv` bundles the map with that evidence. Univalence uses exactly this type.

`equiv_from_inverse_into_set(U, ...)` is the shared constructive conversion:
the supplied set condition proves the triangle law. Both `bijection_equiv`
and `identity_system_equivalence` use it. The latter currently requires
set-valued relation fibers; its encode/decode round trips do not. This is an
explicit restriction of that library lemma, not of the general identity-system
principle.

`based_induction(U, V, ...)` has separate universe parameters for the carrier
and the motive. It replaces separate small/higher copies, including motives
above the carrier universe. It is derived solely from path induction.
`is_set_prop` and `product_prop` are general proposition lemmas in
`bijection_equality.cubist`, shared by the group and field developments.

## Verification

Run only this development and its dependencies:

```
npm test -- archive/first-library/group_univalence.cubist archive/first-library/circle_group_identity.cubist
npm test -- tests/group-identity.test.mjs
```

The regression checks both inverse laws and assumption dependencies; constructs
an equality of full singleton-group records over different carriers (`Unit`
and `Unit × Unit`); checks the circle application; and rejects mutations that
remove multiplication preservation or replace the isomorphism round trip with
an unjustified reflexivity proof.

### Subgroups as groups

`subgroup_carriers` realizes a subgroup as the dependent sum of an ambient
element and its membership proof. The ambient group laws lift through subtype
extensionality, giving `subgroup_as_group` and the injective homomorphism
`subgroup_inclusion`. A homomorphism whose values belong to the subgroup has
a factor `subgroup_factor`; its inclusion triangle commutes, and this factor
is unique. The construction needs no axioms; equalities of homomorphisms use
function extensionality.

`equivalence_from_inverse` provides universe-polymorphic adjointification:
two inverse homotopies give the existing coherent `IsEquiv`, without requiring
the types to be sets. The counit is adjusted by path algebra; the supplied
forward map, inverse, and unit homotopy are retained. This uses no axioms.

### Images of homomorphisms

`subgroup_images` forms an image from truncated preimages, proves closure and
the image/inverse-image adjunction, and shows that direct image preserves
inclusion. `group_image_factor` is a homomorphism onto the realized image:
its inclusion triangle commutes and each image element merely has a preimage.
No representative is selected. `subgroup_image_identity` and
`group_image_trivial` identify the expected subgroups by univalence.
The construction and surjectivity use propositional truncation, without LEM
or choice; the triangle uses function extensionality, and subgroup equalities
also use univalence.
