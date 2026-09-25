# Cantor–Schröder–Bernstein

Run `make serve` and open
[Cantor–Schröder–Bernstein · mutual injections](http://127.0.0.1:8088/proof.html?proof=schroeder_bernstein).
The [Cubist source](../../archive/first-library/schroeder_bernstein.cubist) proves:

```text
forall A : U0. forall B : U0. IsSet(A) -> IsSet(B) ->
  forall f : A -> B. forall g : B -> A.
    Injective(A, B, f) -> Injective(B, A, g) -> Equiv(U0, A, B)
```

`Injective` means left-cancellable: `f(x) = f(y)` implies `x = y`.
The conclusion is the full half-adjoint `Equiv`, containing a function, an
inverse, both inverse laws, and coherence. It is not a mere existence claim.
In the CLI:

```text
prove archive/first-library/schroeder_bernstein.cubist
check CantorSchroederBernstein cantor_schroeder_bernstein
```

## Proof

Call `x` a g-point when every ancestor of `x` under iteration of `g` after `f`
has a g-preimage. Injectivity between sets makes each fiber a proposition,
and function extensionality makes being a g-point a proposition. Excluded
middle therefore decides it.

Define the new map to use the unique g-preimage on g-points and to use f
elsewhere. The branches have disjoint images, and each is injective.
For every y, either g(y) is a g-point, giving a preimage immediately, or
double-negation elimination in the proposition-valued f-fiber supplies a
preimage in the other branch. These explicit preimages give an inverse.
Injectivity proves the other inverse law; setness supplies coherence.

This adapts the g-point argument in
[Escardó's proof](https://arxiv.org/abs/2002.07079).

The checked dependencies are excluded middle (`LEM`), function extensionality,
and the existing truncation constructor and eliminator. The library expresses
LEM as double negation implying mere inhabitation, so
[classical.cubist](../../archive/first-library/classical.cubist) derives proposition-level
double-negation elimination and excluded middle from it. The recorded
name `s0121_Axiom` is an earlier name for the same kernel judgement as
`lib_Trunc`, used in LEM's original construction; the dependency display
deduplicates these aliases by kernel identity. No axiom of choice,
univalence, or theorem-specific axiom is used.

## General types

For arbitrary homotopy types, mutual **embeddings** imply equivalence assuming
excluded middle and function extensionality. An embedding means that each
fiber is a proposition, equivalently that its action on every path space is
an equivalence. The kernel-checked theorem added here is the set version;
the general result is established in
[Escardó's paper](https://arxiv.org/abs/2002.07079).

Mere left-cancellability is insufficient for general types. For example,
`Nat × S1` and `Unit + (Nat × S1)` admit left-cancellable maps both ways:
include the circles in the sum, and in the reverse direction send the extra
point to the base point of the zeroth circle while shifting every circle
index by one. They are not equivalent: only the latter has a contractible
connected component. This counterexample is discussed in
[the author's exposition](https://homotopytypetheory.org/2020/01/26/the-cantor-schroder-bernstein-theorem-for-%E2%88%9E-groupoids/).
