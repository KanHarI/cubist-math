# Galois symmetries as loops

Development resumed on main from the [2026-09-20 checkpoint](galois-handoff.md).
The latest modules establish constructive quotient descent and identify the
kernel quotient with the image of a homomorphism:

```text
kernel_quotient_image_equiv(G, H, h) :
  Equiv(U1, KernelQuotient(G, H, h), GroupImageCarrier(G, H, h))

kernel_quotient_image_equality(G, H, h) :
  KernelQuotient(G, H, h) =[U1] GroupImageCarrier(G, H, h)
```

The inverse uses the entire fiber predicate, without selecting preimages.
Univalence identifies the carriers, and setness transports from the image to
the quotient. This establishes the carrier part of the first isomorphism
theorem. A bundled quotient `GroupIso` still requires a universe-polymorphic
group interface and quotient operations. The [checkpoint](galois-handoff.md)
records validation and the exact next step; the [roadmap](galois-roadmap.md)
retains the complete target.

For planned work, see [requirements for full Galois theory](galois-roadmap.md),
including Lang's distinguished classes. That document is a roadmap, not a
claim that the general correspondence is already proved.

[Explore the concrete Galois group](../web/proof.html?proof=f4_galois_group&name=f4_galois_is_cyclic_two).
[Inspect the root-exchanging loop](../web/proof.html?proof=f4_galois&name=f4_loop_exchanges_roots).
[Read the general identity theorem](../web/proof.html?proof=field_extensions&name=galois_automorphisms_are_loops).

The development proves the following equality of types:

```text
galois_automorphisms_are_loops(K, E) :
  Galois(K, E) =[U1] (E =[FieldExt(K)] E)
```

Here `K` is a bundled field, `E` is a field extension with a specified embedding
of `K`, and `Galois(K, E)` is the type of bijective field maps from `E` to itself
that fix that embedding. It is defined algebraically, before any reference to
loops. The right side is the type of paths from the extension back to itself.

The equality follows from the canonical structure identity equivalence. Its
forward map transports the identity isomorphism along a path of extensions;
its inverse turns an isomorphism into a path. Both round trips and half-adjoint
coherence are checked. Univalence then identifies these two types themselves.
The Galois group is also bundled as `GaloisGroup(K, E)` with its group laws.

## What the paths do

The carrier of each field is a set: two proofs that particular field elements
are equal agree. The *type of field extensions* can nevertheless have nontrivial
loops. Those loops live at the level of complete mathematical structures,
including their operations, field-law evidence, and base-field embedding.

For a symmetry `e`, write `p = extension_iso_path(K, E, E, e)`. The theorem
`galois_loop_action` proves

```text
transport(extension_carrier(K), E, E, p, x)
  = extension_iso_forward(K, E, E, e, x)
```

Thus moving an element around the loop applies the field automorphism to it.
`galois_composition_is_concatenation` identifies composition of automorphisms
with concatenation of their loops. `galois_identity_is_reflexivity` identifies
the identity automorphism with the reflexive path. Path reversal supplies the
inverse, and both inverse laws are checked in the algebraic automorphism type.

Composition is ordered chronologically throughout this development:
`galois_compose(K, E, e, d)` means first `e`, then `d`, so its forward function
is `d(e(x))`. This agrees with `trans(p, q)` meaning first `p`, then `q`.

## The finite example

The concrete fields have carriers `Fin(2)` and `Fin(4)`. Their elements and
operations are defined explicitly. The labels in the four-element field are

| Source name | Mathematical element | Frobenius `x -> x*x` |
|---|---|---|
| `f4_0` | 0 | 0 |
| `f4_1` | 1 | 1 |
| `f4_2` | alpha | alpha + 1 |
| `f4_3` | alpha + 1 | alpha |

The multiplication table realizes the relation `alpha*alpha = alpha + 1`;
addition is coefficientwise addition modulo two. All ring laws, nontriviality,
and existence of inverses for nonzero elements are checked by finite
elimination and computation. This is an explicit field model; the development
does not assume a polynomial quotient or a pre-existing finite-field theorem.

The inclusion sends the two elements of `F2` to 0 and 1 in `F4`. Its preservation
laws and injectivity are proved. The Frobenius function fixes this inclusion,
preserves the field operations, and is its own inverse.

The checked results include:

- `f4_alpha_root` and `f4_other_root`: both alpha and alpha + 1 solve
  `x*x + x + 1 = 0`; `f4_3_not_2` proves they are distinct.
- `f4_loop_exchanges_roots`: transport around the Frobenius loop sends alpha
  to alpha + 1.
- `f4_loop_nontrivial`: that loop cannot be reflexivity.
- `f4_loop_twice`: concatenating the loop with itself is reflexivity.
- `f4_galois_has_two_elements`: an explicit bijection between `Fin(2)` and
  all automorphisms of `F4/F2`.
- `f4_galois_is_cyclic_two`: the bijection preserves the group operations.
- `f4_galois_group_equality`: the complete cyclic group of order two and the
  complete Galois group are equal as elements of `Group`.

The classification is substantive: preservation fixes 0 and 1, and injectivity
prevents alpha from mapping to either. Its image must therefore be alpha or
alpha + 1. Preservation of addition determines the remaining element. This
classifies every automorphism, rather than merely exhibiting two of them.

## Fixed fields and subobjects

[Read the general connection](../web/proof.html?proof=galois_fixing_subgroups&name=intermediate_galois_connection).
[Inspect the F4 fixed field](../web/proof.html?proof=f4_fixed_field&name=f4_fixed_intermediate_is_base).
[Inspect subobject recovery](../web/proof.html?proof=f4_galois_connection&name=f4_fixed_fixing_intermediate).

`Subgroup(G)` and `Subfield(F)` are bundles of small proposition-valued
membership and closure laws. Inverse closure is stated using an inverse
witness from the ambient group or field. It adds neither a total inverse
operation nor a decision about zero. Their law evidence is propositional;
subfield extensionality uses univalence on the membership propositions.
`IntermediateField(K,E)` adds containment of the specified base-field image.

For a family H of automorphisms and a predicate P on the carrier:

`H ⊆ Fixing(P)` if and only if `P ⊆ Fixed(H)`.

Both assignments reverse inclusion. The induced closures are extensive and
idempotent (the source exposes the two containments). The fixed elements form
an intermediate field even if H has not been assumed a subgroup. Automorphisms
fixing P form a subgroup even if P has not been assumed closed. Inverse closure
uses path reversal via the checked automorphism/loop correspondence.
`GaloisLoopInvariant` expresses precisely the same fixed-element condition
using transport around those loops.

Small-indexed intersections of subfields have their universal property. The
universe restriction is deliberate: subfield bundles live in U1, whereas
membership values and the supplied intersection index type live in U0. An
intersection of all subfields is not silently resized.

For F4/F2, `f4_fixed_in_base` returns an actual F2 preimage of any fixed
element; the converse holds because extension automorphisms fix the embedding.
This pointwise result uses no axioms. Univalence then gives equality of the
membership predicates and of the bundled intermediate fields.

`f4_intermediate_classification` proves that an intermediate field is equal
to the base image or the whole F4, assuming a decision for membership of alpha.
`f4_fixing_fixed_subgroup` and `f4_fixed_fixing_intermediate` recover the
original bundles, respectively assuming decisions for Frobenius membership
and alpha membership. No LEM or choice is imported. A finite ambient carrier
does not by itself decide membership of arbitrary proposition-valued subsets.
The module `f4_galois_correspondence` now packages the actual assignments as

```
Equiv(U1, DecidableSubgroup(F4GaloisGroup), DecidableIntermediateField(F2, F4OverF2))
```

[Inspect the correspondence](../web/proof.html?proof=f4_galois_correspondence&name=f4_galois_correspondence).
Both directions reverse inclusion. Each input includes a decision of membership
for every element; finite search constructs decisions for its image. These
algorithms use no LEM or choice. Classifying automorphisms uses function
extensionality; the inverse equalities of subobject bundles also use univalence.
The decision proofs themselves are propositions, so they do not distinguish
otherwise equal subobjects.

The reusable `equiv_from_inverse` lemma adjusts two inverse homotopies into the
half-adjoint coherence required by the existing `IsEquiv`, while preserving the
forward map and inverse. It works in every supported universe, for arbitrary
types, by path induction alone. No setness assumption or new axiom is added.
The full finite theorem with degrees and normal extensions remains outstanding.

The general normal-subgroup foundation is now checked. `group_kernel_normal`
proves that the kernel of every group homomorphism is normal, without axioms.
Normality is preserved by inverse images and small-indexed intersections.
`subgroup_images` gives direct images and their adjunction with inverse images.
Every group homomorphism factors as a merely surjective map to its realized
image followed by inclusion, without choosing representatives.
Group equality transports normality by path induction; an isomorphism supplies
such an equality through univalence. The conjugation automorphism is itself
represented as a loop in `Group`, with a checked decoding round trip.

For F4/F2, `f4_galois_abelian` transports commutativity along the equality with
the cyclic group of order two, and `f4_galois_subgroups_normal` applies this
to every subgroup. These use function extensionality and univalence, without
deciding subgroup membership. The general normal-extension correspondence and
quotient-group theorem remain outstanding. See the
[group development](group_identity.md) for the reusable constructions.

| Result | Axioms used |
|---|---|
| Predicate-level connection, order reversal, closure containments | None |
| Fixed-field inverse closure; F4 fixed-element/base-image implications | None |
| Fixed subfield, subobject-law proof irrelevance, small intersections | Function extensionality |
| Fixing subgroup via path reversal; invariance under loops | Function extensionality, univalence |
| Extensional equality of subfields; F4 classification, recovery and decidable correspondence | Function extensionality, univalence |

## Foundations and scope

The embedded-compositum and distinguished-class layer is checked in
[`embedded_composita`](../web/proofs/embedded_composita.proof),
[`distinguished_extensions`](../web/proofs/distinguished_extensions.proof), and
[`f4_embedded_composita`](../web/proofs/f4_embedded_composita.proof).
Given specified embeddings K → Ω and L → Ω, `EmbeddedCompositum` realizes
the subfield generated by their images as a field. Both factors embed into it,
and composition with its ambient inclusion recovers the specified embeddings.
For a common base B, agreement of the two embeddings B → Ω gives agreement
of the two induced embeddings into the compositum. Leastness also supplies a
commuting factorization into every ambient subfield containing both images.
Swapping the factors gives equality of the resulting bundled fields.

`ExtensionClass` is a predicate on the univalent type of extensions, with
membership in U1. `Distinguished(C)` requires propositional membership and
Lang's tower, compositum-base-change and compositum-closure conditions. The
third condition is proved from the first two, including the commuting base
maps. `extension_class_iso_iff` proves isomorphism invariance by transporting
membership along an equality of extensions; no separate invariance axiom is
required. These definitions do **not** yet prove that finite, algebraic or
separable extensions form distinguished classes. Those instances depend on
the later algebra in the [roadmap](galois-roadmap.md).

The concrete example proves that the compositum of two copies of F2 in F4 is
equal to F2 as a structured field. Regression checks reject identifying it
with all of F4, omitting a common-base triangle, substituting membership of
the wrong extension, or supplying non-propositional witness data as class
membership.

| New result | Checked axiom dependencies |
|---|---|
| Embedded-compositum leastness | Truncation type and elimination |
| Factor embeddings and factorization | Four existing truncation axioms |
| Commuting triangles, base agreement, derivation of Lang's third clause | Four truncation axioms and function extensionality |
| Equality after swapping factors; the F2 compositum field equality | Four truncation axioms, function extensionality and univalence |
| Invariance of class membership under extension isomorphism | Function extensionality and univalence |

Class predicates themselves are in U2: the fixed scope is U0 field carriers,
U1 field and extension bundles, and U1-valued membership. No resizing, choice,
LEM or new kernel rule is introduced by this layer.

Carriers are in `U0`; bundled fields and field extensions are in `U1`.
`AlgebraicFieldLaws` requires a nontrivial commutative ring and an actual inverse
witness for each element proved unequal to zero. It requires no decidable zero
test and no total inverse function. Inverse witnesses are proved unique, making
the field-law evidence propositional when the carrier is a set.

The general structure identity theorem uses the existing univalence axiom,
its transport computation rule, and function extensionality. No result adds
an axiom, uses `LEM`, or uses `Choice`. The concrete finite-field laws and the
Frobenius automorphism itself have no axiom dependencies. Equality of maps and
the classification use function extensionality; their conversion into paths
uses univalence. The explorer reports the exact dependencies of each theorem.

The automorphism/loop interpretation, general subobject connection and the
F4 subobject results above are checked. The general fundamental theorem,
splitting fields, separability, normality, degree calculations and infinite
correspondence remain unproved. See the roadmap for their unchanged scope.

## Modules and verification

| Module | Purpose |
|---|---|
| `structured_sets` | Reusable structure identity argument, total-space contraction, and both inverse laws |
| `algebraic_fields` | Bundled fields, field isomorphisms, and field structure identity |
| `field_extensions` | Base-field embeddings and the automorphism/loop identity |
| `galois_paths` | Action by transport, compatibility with composition, and the automorphism group |
| `finite_fields` | Explicit two- and four-element field models |
| `f4_galois` | Frobenius, its two roots, and the nontrivial loop of order two |
| `f4_galois_group` | Classification of all automorphisms and the cyclic group isomorphism |
| `subgroups`, `subfields` | Proposition-valued subobjects and extensional equality |
| `subfield_intersections` | Small-indexed intersections and their universal property |
| `intermediate_fields` | Ambient subfields containing the base image |
| `galois_fixed_points` | Order-reversing connection, closures and loop invariance |
| `galois_fixed_fields`, `galois_fixing_subgroups` | Closure proofs and bundled assignments |
| `f4_fixed_field` | The fixed elements of the full group are the embedded F2 |
| `f4_intermediate_fields` | Classification with alpha-membership decision |
| `f4_galois_connection` | Recovery of subgroups and intermediate fields with explicit decisions |
| `f4_galois_correspondence` | Order-reversing equivalence of decidable subobjects |
| `finite_decisions`, `decidable_subobjects` | Finite membership algorithms and uniqueness of decision data |

The hypotheses of the reusable structure identity argument are ordinary theorem
parameters, proved for the field and extension signatures: preservation is a
proposition, identity preserves the data, and preservation by the identity
function forces the data to agree. None is a new postulate.

Run focused checks with:

```sh
npm test -- web/proofs/f4_galois_group.proof
npm test -- tests/galois.test.mjs tests/galois-fixed.test.mjs
npm test -- f4_galois_connection subfield_intersections
```

Regression tests reject a corrupted multiplication table, a collapsed base-field
embedding, replacing the root-exchanging symmetry by the identity, claiming
alpha is fixed, claiming alpha lies in the base image, and discarding the
inverse-uniqueness argument. Exact axiom dependencies are asserted in tests. During
this development, the finite tables exposed an existing Unit beta-reduction
bug under enclosing binders. The correction returns the Unit point branch
unchanged, matching the existing `UnitComp` rule; it adds no inference rule.
Native and WASM regressions cover that case. See [kernel compatibility](compatibility.md).

For the mathematical viewpoint, see the *Symmetry* book's
[Galois theory chapter](https://github.com/UniMath/SymmetryBook/blob/master/galois.tex).
The proof here follows the same interpretation of field automorphisms as
self-identifications, using a reusable total-space contraction argument in
MathScript.

## Generated subfields and composita

[Explore generated subfields](../web/proof.html?proof=generated_subfields&name=generated_subfield_least).
[Read compositum associativity](../web/proof.html?proof=subfield_composita&name=compositum_associative).
[Inspect the F4 generator](../web/proof.html?proof=f4_generated_subfields&name=f4_alpha_generates_field).

`FieldClosureStage(F,P,n,x)` is a finite derivation that x lies in the subfield
generated by P. Stage zero contains P. A successor stage keeps previous
members, adds zero and one, and closes under negation, addition, multiplication
and witnessed inverses. Two ranks can be padded to a common rank before
combining their derivations. These constructions and their leastness proofs
use no axioms.

`GeneratedField(F,P,x)` is the propositional truncation of the existence of
such a rank and derivation. It remains in U0, without intersecting over the
U1-sized type of all subfields and without propositional resizing.
`generated_subfield` has checked closure laws. `generated_subfield_least`
eliminates a truncated derivation only into the membership proposition of a
supplied containing subfield. These proofs use the existing truncation axioms;
no LEM or choice is used, and no new axiom is added.

`compositum(F,S,T)` is generated by the union of two subfields in the same
specified ambient field. It is their least upper bound. Monotonicity,
commutativity, associativity and idempotence are proved; equality of the
resulting bundles uses the existing univalent subfield extensionality.
`prime_subfield(F)` is generated by the empty predicate and lies in every
subfield of F.

Transport along a field equality carries a compositum to the compositum of
the transported subfields. This is proved by path induction. Converting a
field isomorphism to a path gives `compositum_along_iso`. The separate `compositum_embeddings` module proves compatibility under
arbitrary embeddings using images and inverse images. It does not treat an
embedding as an equality of its source and entire codomain.

The F4 regression examples prove that alpha generates the whole field and
that its prime subfield is the embedded F2. A separate theorem excludes alpha
from the prime subfield, and a concrete computation checks addition of
derivations with different ranks. Mutation tests reject incorrect rank padding
and replacement of inverse closure by an unrelated membership proof.

The new modules are `subfield_generation_steps`, `generated_subfields`,
`subfield_composita`, `subfield_transport` and `f4_generated_subfields`.
Run their focused checks with `npm test -- tests/generated-subfields.test.mjs`.

## Variance and the order interface

`order_maps` supplies `Monotone`, `Antitone`, order duality and
`AntitoneConnection` for U1 carriers with small-valued relations. A preorder
can be read as a category with at most one morphism between objects;
`Antitone(A,B,...)` is `Monotone(A, Bᵒᵖ,...)`. No general category implementation
is needed to express the variance of these subobject operations.

`galois_orders` proves that subgroup and intermediate-field inclusion are
partial orders and instantiates the generic connection. Enlarging a subgroup
shrinks its fixed field; enlarging an intermediate field shrinks its fixing
group. The composite `intermediate_galois_closure` is monotone and idempotent
as an equality of bundled intermediate fields. The generic order-theoretic
derivations have no axioms. Their Galois
instantiations inherit function extensionality and univalence from the bundled
fixing-subgroup construction, whose inverse closure uses path reversal.
Antisymmetry and the resulting bundle equality also use those two axioms.
The predicate-level connection and variance proofs remain axiom-free.

This is order reversal under **inclusion**, distinct from transport along an
**equality** of presentations. The existing HoTT path action already supplies
that transport. Field embeddings now have checked identities, composition,
associativity and commutative towers, as described below. A general category
library is not a prerequisite for these field-morphism operations.


## Fields, embeddings, and realized subfields

[Inspect a realized subfield](../web/proof.html?proof=subfield_carriers&name=subfield_as_field).
[Read the intermediate-field tower](../web/proof.html?proof=intermediate_towers&name=intermediate_tower).
[Read change of ambient compositum](../web/proof.html?proof=compositum_embeddings&name=compositum_image).
[Inspect equality with the image field](../web/proof.html?proof=field_embedding_image&name=field_embedding_image_equality).

`SubfieldCarrier(F,S)` is the small subtype of ambient elements carrying
membership evidence. Its operations come from closure, and its field laws
follow by equality of ambient values. An ambient inverse of a nonzero member
lies in S; no zero test or new choice principle is used.
`subfield_as_field` packages the result as an `AlgebraicField`, and
`subfield_inclusion` is its injective field map into F. All of these generic
constructions use no axioms. The reusable subtype-is-a-set proof now lives
with the general subtype equality lemmas, rather than in the choice theorem.

`FieldEmbedding(K,L)` reuses the existing extension-embedding data. Identities,
composition and its associativity are checked; equality of complete embedding
records uses function extensionality. `FieldTower` is a specified commutative
triangle of embeddings. `intermediate_tower` realizes K → M → E with the
original K → E inclusion as its composite. This is the field-morphism
infrastructure needed for tower laws, without introducing a general category
library before it is useful.

`subfield_preimage` pulls membership back along an embedding. Its identity
and composition laws are equalities of bundles, with the order of embeddings
reversed. `subfield_image` stores an actual preimage and its membership
witness. Injectivity makes these witnesses unique; the type is already a
proposition, so image construction needs neither truncation nor choice.
Images are closed under inverses: an inverse in the target must be the image
of the unique source inverse. Both image and inverse-image closure proofs are
axiom-free.

For a fixed embedding, image and inverse image both preserve inclusion, and
`subfield_image_preimage_adjunction` proves

`image(S) ⊆ T` if and only if `S ⊆ preimage(T)`.

`OrderAdjunction` reuses the previous antitone connection interface by dualizing
the second order. This is distinct from the Galois fixed-field assignments,
which reverse inclusion. The adjunction proves that embeddings preserve
composita; equality of the bundles uses univalent extensionality.

`field_embedding_factor` is the unique factorization through any subfield
containing the embedding's values. Factoring through the whole image gives
`field_embedding_image_iso`, constructively and without axioms. Applying the
field structure identity theorem gives `field_embedding_image_equality`:
the source and its realized image are equal as fields, using univalence and
function extensionality. No equality with the entire codomain is asserted.

`f4_embedding_images` checks these interfaces on the non-surjective F2 → F4
inclusion. Negative tests reject a noncommuting tower, an alleged equality of
F2 with all of F4, and replacement of the image inverse by a constant map.
Run `npm test -- tests/field-embeddings.test.mjs` for these focused checks.
