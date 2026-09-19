# Galois symmetries as loops

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
  complete Galois group are equal as elements of `GroupType`.

The classification is substantive: preservation fixes 0 and 1, and injectivity
prevents alpha from mapping to either. Its image must therefore be alpha or
alpha + 1. Preservation of addition determines the remaining element. This
classifies every automorphism, rather than merely exhibiting two of them.

## Foundations and scope

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

This is the automorphism/loop interpretation and a complete finite example.
It does not yet include the general fundamental theorem of Galois theory,
intermediate-field correspondence, splitting fields, separability, normality,
or the construction of rational/algebraic number fields.

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

The hypotheses of the reusable structure identity argument are ordinary theorem
parameters, proved for the field and extension signatures: preservation is a
proposition, identity preserves the data, and preservation by the identity
function forces the data to agree. None is a new postulate.

Run focused checks with:

```sh
npm test -- web/proofs/f4_galois_group.proof
npm test -- tests/galois.test.mjs
```

Regression tests reject a corrupted multiplication table, a collapsed base-field
embedding, and replacing the root-exchanging symmetry by the identity. During
this development, the finite tables exposed an existing Unit beta-reduction
bug under enclosing binders. The correction returns the Unit point branch
unchanged, matching the existing `UnitComp` rule; it adds no inference rule.
Native and WASM regressions cover that case. See [kernel compatibility](compatibility.md).

For the mathematical viewpoint, see the *Symmetry* book's
[Galois theory chapter](https://github.com/UniMath/SymmetryBook/blob/master/galois.tex).
The proof here follows the same interpretation of field automorphisms as
self-identifications, using a reusable total-space contraction argument in
MathScript.
