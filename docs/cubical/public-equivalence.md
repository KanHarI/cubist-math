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

The full **public** `Univalence` statement still requires the round trip
beginning with arbitrary public half-adjoint data, or equivalently the relevant
half-adjoint witness uniqueness theorem. This obligation remains separate
from the native univalence equivalence and the public eta law below. No
missing result is replaced by an axiom.


## Equality-to-equivalence and eta

`nativeIdentityToEquivalence(A,B,p,identity)` is the explicit weak-elimination
construction

```
comp j Equiv_native(p(~j), B) [] identityEquivalence(B).
```

The optional `identity` argument allows sharing the actual checked identity
equivalence definition. It is not an additional hypothesis. This definition
has the standard meaning of `idtoequiv`, but does not assert strict computation
at reflexivity. Its forward map can contain constant-transport correction
compared with the literal term `transport(p)`.

`nativeUnivalenceEta(A,B,p,level,identity)` proves `ua(idtoequiv(p))=p`.
Fill the preceding equivalence transport to get `E(i):Equiv_native(p(i),B)`,
with endpoints `idtoequiv(p)` and identity. The Glue square

```
Glue B [i=0 ↦ (A,idtoequiv(p)), i=1 ↦ (B,identity), k=1 ↦ (p(i),E(i))]
```

has at `k=0` the standard `ua` line and at `k=1` the original path.

`publicIdentityToEquivalence(A,B,p,identity)` converts the result to public
half-adjoint form. `publicUnivalenceEta(A,B,p,level,identity,roundTripLemma)`
proves its public eta law by applying `ua` to the native representation
round-trip proof, then composing with native eta.

The final parameter is a shared, checked function

```
(e : Equiv_native(A,B)) →
  halfAdjointToNative(nativeToHalfAdjoint(e)) = e.
```

Register the generic theorem with an explicit type ascription before applying
it to `A` and `B`; the tests give a complete example. The construction requires
this shared lemma instead of inlining its filling proof repeatedly. Native
checking verifies the supplied function and every application. This is proof
sharing, not a new axiom or unchecked dependency.

## Full native univalence

`nativeUnivalenceCounit(A,B,e,level,identity)` proves
`idtoequiv(ua(e))=e`. Over the Glue line, `unglueEquivalence` supplies a dependent
line of equivalences to `B`. Its endpoint forward maps are already correct;
uniqueness of native equivalence witnesses repairs the endpoint witnesses.
Reverse this dependent line and use the path-over bridge to obtain the counit.

`nativeUnivalenceEquivalence(A,B,{level,identity,eta,counit})` packages the two
checked inverse laws into

```
Equiv_native(Path U_level A B, Equiv_native(A,B)).
```

Its forward map is the concrete `nativeIdentityToEquivalence` above. Pass
named checked eta and counit functions specialized to `A,B`. The generic
quasi-inverse construction is checked under lambda-bound maps before those
maps and laws are applied, keeping the proof compact.

Native eta and counit check at U0 and U2. The complete native equivalence and
public eta also check against closed checked lemma registries. No universe
composition, Glue behavior, or path computation rule has been added or
relaxed for these results.
