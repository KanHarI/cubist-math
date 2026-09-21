# Cubical path algebra

`experiments/cubical/path-algebra.mjs` provides checked-term builders for the
path operations and groupoid laws needed by the circle encode/decode proof.
The current `web/proofs/paths.proof` defines its operations by identity
elimination and uses strict reflexivity computation in several proof bodies.
These helpers instead target the canonical direct cubical operations below.
Migrating the source requires explicit changes to those operation definitions;
the helpers must not silently be substituted for differently defined terms.

## Operations and orientation

For `p : Path A x y` and `q : Path A y z`, define

```
refl(x)(i)   = x
inverse(p)(i) = p(~i)
ap(f,p)(i)   = f(p(i))
(p · q)(i)   = comp j A [i=0 ↦ x, i=1 ↦ q(j)] p(i).
```

The exported builders are `pathRefl(A,x)`, `pathInverse(A,p)`,
`pathApply(B,f,p)`, and `pathConcat(A,x,p,q)`. Composition is ordered from
`p` to `q`. All generated names are fresh, and checked native/browser references
are preserved. Construction itself is not a checking certificate.

## Derived laws

The following builders return proof terms directly:

| Builder | Proved equality |
| --- | --- |
| `transportConstant(A,x)` | `comp j A [] x = x` |
| `pathRightUnit(A,x,y,p)` | `p · refl(y) = p` |
| `pathLeftUnit(A,x,y,p)` | `refl(x) · p = p` |
| `pathInverseRight(A,x,y,p)` | `p · inverse(p) = refl(x)` |
| `pathInverseLeft(A,x,y,p)` | `inverse(p) · p = refl(y)` |
| `pathAssociative(A,x,y,z,w,p,q,r)` | `(p · q) · r = p · (q · r)` |
| `pathApplyConcat(A,B,f,x,y,z,p,q)` | `ap(f,p · q) = ap(f,p) · ap(f,q)` |

These are paths, not new judgmental computation rules. In particular constant
transport in a neutral type is not assumed to reduce definitionally to its
argument.

For constant transport, add a wall `k=1 ↦ x` to the original empty composition;
varying `k` gives its path to `x`. For the right unit, add the wall `k=1 ↦ p(i)`
to the concatenation square. The left unit uses `p(i ∧ j)`. The right inverse
uses `p(i ∧ ~j)`; the left inverse uses `p(~i ∨ j)`. Their boundary restrictions
are exactly the required concatenation and constant path.

For associativity, let `L(i,j)` fill the composition of `p` with `q`, and let
`Q(j,k)` fill the composition of `q` with `r`. Define

```
H(i,k) = comp j A [i=0 ↦ x, i=1 ↦ Q(j,k), k=0 ↦ L(i,j)] p(i).
```

Its base is `(p · q)(i)`, endpoint walls are `x` and `r(k)`, and its top is
`(p · (q · r))(i)`. Add `s=1 ↦ H(i,k)` to the square computing
`((p · q) · r)(i)`. Varying `s` proves associativity. Each intersection and
endpoint is checked by the ordinary native composition rule.

For preservation of concatenation, apply `f` to the filling square for
`p · q`. This is a filling with exactly the base and sides of the square for
`ap(f,p) · ap(f,q)`. Add it as the `k=0` wall to that composition; varying
`k` gives the claimed path between its two possible top edges. Mixed universe
levels are supported and independently checked.

## Validation and remaining work

`tests/path-algebra.test.mjs` independently checks the generic laws with the
JS reference checker and native C checker at U0 and U2. The native tests also
apply the laws to the loop formed by the two different meridians of
`Suspension(Unit + Unit)`, using closed checked definitions. These checks stay
below 10,000 arena nodes. A malformed concatenation with mismatched endpoints
is rejected. Name-collision and browser-reference cases are included.

There are no new axioms or kernel rules. The dependent transport, decoder, `apd_constant`, and cancellation laws for
these operations are provided in
[dependent-transport.md](dependent-transport.md). Existing source definitions
still need explicit migration and native checking.
