# Public half-adjoint equivalences and cubical fibers

`experiments/cubical/public-equivalence.mjs` connects the existing public
MathScript equivalence representation with the native CCHM representation.
The public signatures are taken from `buildAxiomSpecialization` in
`web/mathscript/compiler.mjs`; no compiler or website code is changed here.

## Checked interface

`halfAdjointType(A,B,f)` is exactly

```
Σ g : B → A,
Σ eta : (x : A) → g(f(x)) = x,
Σ epsilon : (y : B) → f(g(y)) = y,
(x : A) → ap(f,eta(x)) = epsilon(f(x)).
```

`halfAdjointEquiv(A,B)` adds the leading forward map. The `ap` operation is the
canonical direct cubical application from `path-algebra.mjs`.

- `halfAdjointToNative(A,B,e)` produces contractible fibers for the same map.
  It uses the proved quasi-inverse construction; the triangle is not needed
  in that direction.
- `nativeToHalfAdjoint(A,B,e)` constructs inverse maps, homotopies and the
  half-adjoint triangle from the supplied fiber contractions.
- `nativeEquivalenceRoundTrip(A,B,e)` proves that converting a native
  equivalence to public form and back gives the original native equivalence.
  Its forward map is definitionally unchanged, and contractibility witnesses
  are propositions.
- `publicUnivalencePath(A,B,e,level=0)` builds the computational Glue universe
  path from a public half-adjoint equivalence.
- `publicUnivalenceBeta(A,B,e,x)` proves that transport along that path sends
  `x` to the supplied public forward map applied to `x`.

The conversion builders apply generic lemmas under lambda-bound data. This
keeps large filling proofs from being duplicated throughout subsequent
contractions. References stay inert and are checked by the native registry.

## The half-adjoint triangle

For a fixed `y`, a native fiber consists of `x : A` and a path `y = f(x)`.
Its center determines the inverse `g(y)` and the reversed counit
`epsilon(y) : f(g(y)) = y`.

Contract the fiber over `f(x)` to `(x,refl(f(x)))`. The first component is
`eta(x)`. The second component is a square `E(j,r)` whose left edge is the
center's fiber path, top edge is `ap(f,eta(x))`, and bottom and right edges
are constant at `f(x)`. If `c` is that left edge, the cube

```
comp r B [j=0 ↦ c(r), j=1 ↦ f(x),
          k=0 ↦ E(j,r), k=1 ↦ c(r ∧ ~j)] f(x)
```

proves the triangle: at `k=0` it is `ap(f,eta(x))`, and at `k=1` it is
`epsilon(f(x))`. All boundaries are checked by existing composition rules.

## Validation and remaining obligations

Generic conversions check with both JS and native C at U0 and U2. The public
`ua` and beta statement also check generically. Native checking verifies the
native round-trip law. A closed product-swap example computes actual
nonidentity transport, and a false beta endpoint is rejected.

This checkpoint deliberately does not claim the full public `Univalence`
statement, an `idtoequiv` definition, or `UnivalenceEta`. It also does not yet
prove the round trip beginning with arbitrary public half-adjoint data.
Those coherence obligations remain separate from the checked maps and beta
law provided here. No missing result is replaced by an axiom.
