# One univalence axiom

The library postulates that the canonical map from equality to equivalence is
itself an equivalence:

```text
Univalence(U0, A, B)
  : IsEquiv(U1, (A =[U0] B), Equiv(U0, A, B), idtoequiv(U0, A, B))
```

This is the standard univalence formulation. `idtoequiv` is constructed by
path induction: reflexivity gives the identity equivalence. It uses no axiom.
`IsEquiv` is the same half-adjoint equivalence structure used throughout the
library, including at higher universes.

The single assumption supplies an inverse and its laws:

- `ua(U, A, B, e) : A =[U] B` is the inverse function extracted from that evidence.
- `UnivalenceBeta(U, A, B, e, x)` proves that transporting `x` along `ua(e)`
  equals the forward function of `e` applied to `x`.
- `UnivalenceEta(U, A, B, p)` proves `ua(U, A, B, idtoequiv(U, A, B, p)) = p`.

The beta proof applies the right inverse law to evaluation of an equivalence
at `x`. A separate path-induction lemma identifies that evaluation of
`idtoequiv(p)` with transport along `p`. The eta proof is the left inverse
law directly. Neither law is a separate postulate, and beta is propositional
equality, not a new kernel reduction rule.

All four interfaces accept `U0`, `U1`, etc., or a parameter `U : Universe`.
The fully expanded axiom signature avoids requiring a successor operation on
universe variables. At a named universe it is definitionally equal to the
`IsEquiv` expression above, as checked in `tests/universes.test.mjs`.

## Names and migration

Previously `Univalence(U, A, B, e)` meant the inverse operation. That operation
is now called `ua(U, A, B, e)`. `Univalence(U, A, B)` names the actual axiom.
`UnivalenceBeta` retains its application syntax but is now a derived theorem;
its former restriction to named finite universes is removed.

At the construction level:

| Binding | Role | Univalence assumptions |
|---|---|---|
| `lib_AreEquiv` | Canonical `idtoequiv`, by path induction | None |
| `lib_univalence` | `IsEquiv(idtoequiv)` | The single axiom |
| `lib_ua` | Extracted inverse | `lib_univalence` |
| `lib_ua_elim` | Transport beta theorem | `lib_univalence` |
| `lib_ua_unique` | Eta theorem | `lib_univalence` |

The old three-postulate presentation is replaced in both the native library
and the browser's replayable construction exports. Function extensionality
remains a separate existing assumption; deriving it from univalence is outside
this change.

## Proof generation and checking

`tools/proofs/univalence.mjs` builds the type and derived terms using only
public kernel instructions. It checks that exactly one axiom was introduced
and that all three results depend only on it. Its generated native proof is
`src/univalence_generated.inc`; no kernel inference rule is modified.
`tools/port_proofs.py` preserves this replacement when refreshing the upstream
ported proof programs.

Regenerate after changing the proof generator:

```sh
node tools/proofs/univalence.mjs
make proof-export
npm run format:mathscript
```

Focused checks:

```sh
npm test -- tests/universes.test.mjs tests/group-identity.test.mjs tests/galois.test.mjs
make test
```
