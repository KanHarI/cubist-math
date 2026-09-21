# Dependent transport and cancellation

`experiments/cubical/dependent-transport.mjs` derives the remaining transport
and cancellation laws from `web/proofs/paths.proof`, for the direct cubical
operations documented in [path-algebra.md](path-algebra.md). All helpers emit
inert syntax, checked by the native C kernel. There are no added axioms,
judgmental regularity assumptions, or changes to reflexivity.

## API and statements

Write `tr(C,p,a)` for transport along `p`, and `p · q` for canonical cubical
concatenation. All proof helpers return proof terms directly.

| Helper | Result |
| --- | --- |
| `pathTransport(C,p,a)` | `comp i C(p(i)) [] a` |
| `transportInverseAfter(A,C,x,y,p,a)` | `tr(C,inverse(p),tr(C,p,a)) = a` |
| `transportAfterInverse(A,C,x,y,p,b)` | `tr(C,p,tr(C,inverse(p),b)) = b` |
| `transportConcat(A,C,x,y,z,p,q,a)` | `tr(C,p · q,a) = tr(C,q,tr(C,p,a))` |
| `transportApply(C,p,a)` | `tr(C,p,a) = tr(identity,ap(C,p),a)` |
| `dependentApply(C,f,x,y,p)` | transport-form dependent action of `f` on `p` |
| `dependentApplyConstant(A,B,f,x,y,p)` | `apd(f,p) = transport_constant(f(x)) · ap(f,p)` |
| `transportDecoder(A,origin,C,x,y,p,f,b)` | the decoder transport formula below |
| `cancelLeft(A,x,y,z,p,q,r,same)` | `q = r`, given `same : p · q = p · r` |
| `appendCancelInverse(A,x,y,z,p,q)` | `(p · q) · inverse(q) = p` |
| `appendInverseCancel(A,x,y,z,p,q)` | `(p · inverse(q)) · q = p`, for `q : z = y` |

The `apd` statement uses the dependent-path/transport bridge in
[path-over.md](path-over.md): apply `f` pointwise to the path, then convert the
resulting dependent path to equality after transport. This matches the native
frontend's explicit implementation, rather than a strict-J implementation.

## Construction of the transport laws

Let `F(i)` fill transport of `a` along `C(p(i))`. Backward transport starts at
`F(1)`. Add a wall `k=1 ↦ F(~i)` to its composition. At `k=0` this is the
original backward transport; at `k=1` it is `F(0)=a`. Reversing `p` gives the
other round trip, since reversal twice is definitionally the original path.

For transport along a concatenation, fill its defining square in the base
space. Above that square, compose in `C`, with base the filling along `p`,
left wall the original `a`, and right wall the filling along `q` starting at
`tr(C,p,a)`. The top is a dependent path over `p · q`. Converting it with the
checked path-over bridge proves the transport composition law.

For `transportApply`, direct application of a function to a path makes both
transport families definitionally equal. Reflexivity proves the stated law.

## Decoder transport

For `f : C(x) → Path A origin x` and `b : C(y)`, the formula is

```
tr(point ↦ C(point) → Path A origin point, p, f)(b)
  = f(tr(C,inverse(p),b)) · p.
```

The kernel's existing Pi composition rule first transports `b` backwards.
Its Path composition rule then appends `p`. With the canonical concatenation,
these expressions are definitionally equal, so reflexivity is sufficient.
The regression test checks this conversion for a generic dependent family;
there is no extra decoder-specific computation rule.

## Constant-family dependent action

Put `a=f(x)`, `r=ap(f,p)` and let `F(i)` fill constant transport of `a` in `B`.
Let `L(j,k)` fill that same transport with the `j=1` wall held at `a`. Its top
is `transport_constant(a)(j)`. The cube

```
comp i B [j=0 ↦ F(i ∨ k), j=1 ↦ r(i)] L(j,k)
```

has at `k=0` the bridge-based `apd`, and at `k=1` the concatenation of
`transport_constant(a)` and `r`. The `j` endpoints remain fixed.

## Cancellation and verification

Left cancellation follows by prefixing the supplied equality with the reverse
path, then composing associativity, the inverse law, and the left unit law.
The two appended inverse laws follow from associativity, the inverse law under
function application, and the right unit law.

The seven new tests check generic transport laws at U0 and U2 with both the JS
reference checker and native C checker. They also cover decoder transport,
constant-family dependent action, and all cancellation helpers. A nonidentity
product-swap Glue family checks against actual closed definitions; a false
round-trip endpoint is rejected.

This completes the listed path-law helpers, not the entire source migration.
Existing source definitions must explicitly adopt the direct operations, and
higher identity-system, circle, and other library proofs still require their
own native checking.
