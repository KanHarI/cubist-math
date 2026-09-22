# Every surjection has a right inverse

Run `make serve`, then open
[Surjections · right inverses and choice](http://127.0.0.1:8088/proof.html?proof=surjections).
The same proof is available in the CLI:

```text
prove web/proofs/surjections.cubist
check EverySurjectionHasRightInverse every_surjection_has_right_inverse
```

The [Cubist source](../web/proofs/surjections.cubist) proves the usual
set-theoretic statement using the existing library axiom of choice (`AOC`):

```text
forall A : U0, forall B : U0, IsSet(A) -> IsSet(B) ->
  forall f : A -> B, Surjective(A, B, f) -> Mere(RightInverse(A, B, f))
```

Here `Fiber(A, B, f, y)` is `exists x : A, f(x) = y`;
`Surjective(A, B, f)` says each fiber is merely inhabited. A
`RightInverse(A, B, f)` consists of `g : B -> A` with the pointwise law
`f(g(y)) = y`. `Mere` denotes propositional truncation: the conclusion asserts
existence of such a map, without selecting a distinguished inverse. `IsSet`
requires equality proofs between the same endpoints to agree.

The proof first shows that a proposition-valued subtype of a set is a set.
Consequently the fibers of a map between sets are sets. Choice applied to the
family of fibers gives mere existence of a preimage for every target element
simultaneously. Projecting these preimages gives the inverse function and its
right-inverse law. The final step maps this construction under truncation.

`right_inverse_from_preimages` gives an actual inverse when preimages are
already supplied as dependent pairs; that lemma and the fiber-setness lemmas
are axiom-free. The final theorem depends exactly on `AOC`, `lib_Trunc`,
`lib_trunc_intro`, `lib_trunc_is_trunc`, and `lib_trunc_elim`. It does not use
excluded middle, function extensionality, or univalence.

The compiler's `Choice(U0)(A, B, setA, setFibers, inhabited)` interface checks
all premises and applies the existing `AOC` declaration through the kernel.
It introduces no new axiom or kernel rule. In the web inspector, both the
`Choice` call and the theorem's `AOC` dependency link to that declaration.
