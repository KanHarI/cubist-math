# Preserving the supplied inverse and section during adjointification

`lib/cubical/adjointification.mjs` derives the small path-algebra
helpers used by `archive/first-library/equivalence_from_inverse.cubist`. The source proof
keeps `f`, `g`, and `eta` and changes only the counit to

```
epsilon'(y) = inverse(epsilon(f(g(y)))) · (ap(f,eta(g(y))) · epsilon(y)).
```

Converting quasi-inverse data to native contractible fibers and then extracting
half-adjoint data preserves `g`, but rebuilds `eta`. That conversion therefore
cannot silently replace the above source contract. The helpers here instead
support the existing counit and triangle argument without strict J beta.

## Checked helpers

- `cancelRight(A,x,y,z,p,q,r,same)` derives `p=q` from `p·r=q·r`.
- `prependInverseCancel(A,x,y,z,p,q)` derives `inverse(p)·(p·q)=q`.
- `homotopyNatural(A,f,h,x,y,p)` derives
  `ap(f,p)·h(y) = h(x)·p`, where `h(t):f(t)=t`.
- `homotopySelf(A,f,h,x)` derives `ap(f,h(x)) = h(f(x))`.
- `applyInterchange(A,B,f,g,x,y,p)` derives
  `ap(f,ap(g∘f,p)) = ap(f∘g,ap(f,p))`.

All return inert proof terms that require ordinary native checking. The
operations are the canonical direct ones in `path-algebra.mjs`.

## Naturality square

Write `H(i,j)=h(p(i))(j)`. Its bottom edge is `f(p(i))`, its top is `p(i)`,
and its left and right are `h(x)` and `h(y)`. The concatenation of bottom
and right can be compared with the diagonal by adding the wall
`k=1 ↦ H(i,i∧j)` to its composition square. Similarly, the concatenation
of left and top is compared with the diagonal using `H(i∧j,i)`. Concatenate
the first comparison with the reverse of the second to obtain naturality.

Self-naturality is naturality on `h(x)` followed by right cancellation.
Right cancellation uses the already checked appended-inverse cancellation
laws. Prepending an inverse cancels by associativity, the inverse law, and
the left unit law. Direct cubical application makes interchange
judgmentally equal, so its proof is reflexivity.

Four tests independently check these laws with the JS reference and native C
checkers, including U0 and U2. This module supplies the foundational lemmas;
the source `adjoint_triangle` must still be checked after its helper bodies
are explicitly migrated. No existing theorem is replaced without checking
its declared type.
