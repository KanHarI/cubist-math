# Group isomorphism is equality

[Open the checked structure identity theorem](../web/proof.html?proof=group_univalence).
[Open its application to the circle](../web/proof.html?proof=circle_group_identity).

The formalization proves equality of the types themselves:

```text
group_isomorphism_is_equality(G, H) :
  GroupIso(G, H) =[U1] (G =[GroupType] H)
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

## What is equal?

The existing `Group(A, unit, multiply)` is a type of group-law evidence.
The new bundle is

```
GroupType = exists A : U0,
              exists unit : A,
                exists multiply : A -> A -> A,
                  Group(A, unit, multiply)
```

Thus `G = H` includes the carrier, unit, multiplication and all law evidence.
`GroupIso(G,H)` uses the existing multiplication-preserving bijections. Unit
preservation is derived; it is not silently added as a hypothesis. Inverses and
group-law evidence are proved unique where needed using the group laws and the
set condition on carriers.

`GroupType` lives in `U1` because its carrier ranges over `U0`. Consequently
its identity type is represented at that universe level too. The single
`Equiv(U, A, B)` definition takes an explicit universe parameter; the theorem
uses `U1`. Its underlying `IsEquiv(U, A, B, f)` is the same half-adjoint
equivalence data at every universe, and the existing univalence axiom accepts
it directly. No separate higher-universe equivalence definition remains.
This development bundles small groups; generalizing their carrier universe
is separate from generalizing equivalence itself.

Group equality is an identity type, not definitional equality or a truncated
claim of isomorphism. Different isomorphisms give different paths:
`group_isomorphism_paths_injective` proves that the inverse construction cannot
collapse them. The function used to generate these paths is
`group_identity_encode`; its inverse is `group_equality_iso`.

## Checked modules

- [group_identity.proof](../web/proofs/group_identity.proof): bundled groups,
  uniqueness of inverse/law evidence, preservation of units, and a direct proof
  that isomorphic group records are equal.
- [group_isomorphisms.proof](../web/proofs/group_isomorphisms.proof): an
  isomorphism is determined by its underlying function.
- [group_total_identity.proof](../web/proofs/group_total_identity.proof): the
  total space `exists H : GroupType, GroupIso(G,H)` is contractible, with center
  `(G, identity)`.
- [identity_systems.proof](../web/proofs/identity_systems.proof): a reusable
  identity-system construction, inverse laws, and an equivalence when the
  relation fibers are sets. These generic results require no axioms.
- [group_univalence.proof](../web/proofs/group_univalence.proof): isomorphism
  fibers are sets; the full group structure identity equivalence and both
  canonical inverse laws, followed by equality of the isomorphism and identity types.
- [circle_group_identity.proof](../web/proofs/circle_group_identity.proof): the
  already checked winding isomorphism yields `CircleLoopGroup = IntegerGroup`.
  Decoding this equality recovers that same isomorphism.

The group equivalence and circle application use only the existing univalence,
univalence computation and function extensionality assumptions (`lib_univalence`,
`lib_ua_elim`, `lib_funext`). They use no excluded middle, choice, propositional
truncation, or theorem-specific axiom. The kernel implementation is unchanged.

## Verification

Run only this development and its dependencies:

```
npm test -- web/proofs/group_univalence.proof web/proofs/circle_group_identity.proof
npm test -- tests/group-identity.test.mjs
```

The regression checks both inverse laws and assumption dependencies; constructs
an equality of full singleton-group records over different carriers (`Unit`
and `Unit × Unit`); checks the circle application; and rejects mutations that
remove multiplication preservation or replace the isomorphism round trip with
an unjustified reflexivity proof.
