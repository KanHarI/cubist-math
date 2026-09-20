# The fundamental group of the circle

Open [the circle proof](http://127.0.0.1:8088/proof.html?proof=circle) with
`make serve` running. Click names to inspect definitions, then **View source** to
navigate to their mathematical source. The CLI checks the same program:

```text
prove web/proofs/circle.proof
check FundamentalGroupS1IsZ fundamental_group_of_circle
```

The final checked theorem is `fundamental_group_of_circle : FundamentalGroupS1IsZ`.
Its statement packages the group of based loops, the group of integers under
ordinary addition, and a multiplication-preserving bijection between them.

## Source map

| Source | Content |
| --- | --- |
| [suspension.proof](../web/proofs/suspension.proof) | `S0 = Unit or Unit`, `S1 = Suspension(S0)`, the generating loop, and a derived recursor with its path computation law |
| [paths.proof](../web/proofs/paths.proof) | Path algebra, transport, based path induction, and half-adjoint equivalences |
| [sets.proof](../web/proofs/sets.proof) | Decidable equality and Hedberg's theorem |
| [groups.proof](../web/proofs/groups.proof) | Group and group-isomorphism statements |
| [integers.proof](../web/proofs/integers.proof) | Signed integers, successor equivalence, arithmetic addition, and setness |
| [circle.proof](../web/proofs/circle.proof) | Integer cover, encode/decode, winding, inverse laws, group laws, and the final theorem |

Suspending the two-point type gives the circle. Suspending `Unit` alone gives a
contractible type. Integers use `Nat or Nat`: `left n` represents n, and `right n`
represents -(n+1).

## Argument and assumptions

Univalence turns integer successor into a path between types. Suspension induction
uses that path to construct the integer cover of the circle. Transport around the
generating loop adds one. Encode and decode give inverse maps between based loops
and integers; winding carries concatenation to arithmetic addition.

Decidable equality and Hedberg's theorem establish that the loop space is already
a set. This set of loops represents the fundamental group; a general set-truncation
constructor is not required or introduced here. The final statement includes
associativity, units, inverses, setness, and a group isomorphism.

The development uses two library axioms: univalence and function extensionality.
Its transport computation rule is [derived from univalence](univalence.md). Source inspection links these uses
to their original declarations. No circle-specific axiom or theorem is added to C.
The [kernel extension](../src/kernel/suspension.c) supplies general suspension
formation, points, meridians, dependent elimination, and propositional meridian
computation. Transport and dependent application reuse the existing equality
eliminator. Point computation is definitional; path computation is propositional.

The encode/decode strategy follows the standard mathematical approach described by
[Licata and Shulman](https://arxiv.org/abs/1301.3443). All supporting proof terms here
are elaborated from the linked mathematical sources and checked by the C/WASM kernel.

## Validation

`npm test` checks the complete theorem through WASM and the CLI, and rejects a
wrong winding number and a fabricated inverse law. `npm run test:browser` checks
source navigation and axiom links. Native tests exercise the new general rules,
including invalid coherence data, together with the existing inference suite.
