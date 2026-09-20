# Binary numbers, arbitrary radix, and proof transfer

The mathematical sources now prove `10! = 3628800` using W-type binary numbers,
using one generic radix development instantiated at bases 2 and 10, and by
transporting the results among these representations and unary `Nat`.

**Backend distinction:** these proofs currently check on the production Id/J
kernel. The transfer proofs explicitly depend on its existing univalence axiom.
They are not yet checks by the native cubical kernel. That migration requires
computational univalence, source translation, and all existing library features;
there must be no old-kernel fallback labelled as a successful cubical check.

## Representation and syntax

`W(A, B)` forms well-founded trees. `sup(T, label, children)` introduces a tree,
and `wrec(T, motive, step, tree)` performs dependent induction. The step takes
`label`, the child function, and a dependent recursive result for every child.
These elaborate to the production kernel's existing W rules; no W axiom was added.

`BinaryPositive` has a leaf for 1 and unary constructors for digits 0 and 1.
`BinaryNat` adds a separate zero. Thus positive numbers have no leading-zero
representations. `0b110` expands to
`binary_positive(binary_bit0(binary_bit1(binary_one)))`, with one constructor per
bit. Hover exposes this expansion. Decimal literals retain their unary `Nat`
meaning. The parser stores binary digits exactly as text, rejects malformed
literals, and permits at most 256 significant bits subject to kernel depth limits.

`RadixNat(extra)` uses radix `extra + 2`. Leaves carry one of the nonzero leading
digits; unary nodes carry any radix digit. Its finite digits, increment with
carry, addition, multiplication, and factorial are defined uniformly. The base-2
and base-10 factorial proofs use exactly this same implementation.

## Sources and dependencies

- `binary_naturals`, `binary_arithmetic`: representation, literals, fast arithmetic,
  manual `binary_factorial_ten`. No axioms.
- `radix_naturals`, `radix_arithmetic`, `radix_factorial`: the generic representation,
  arithmetic, and manual base-2/base-10 factorial instances. No axioms.
- `binary_induction`, `radix_induction`: dependent induction in digit notation.
  Function extensionality identifies W child functions from `Void` and `Unit`.
- `binary_equivalence`: both round trips and full half-adjoint equivalences with Nat.
- `binary_arithmetic_correct`: successor/addition/multiplication/factorial compatibility,
  and `factorial_ten_from_binary` in the **existing** Nat factorial.
- `radix_digit_laws`, `radix_decode`, `radix_arithmetic_correct`: generic digit laws,
  successor and arithmetic compatibility, and the Nat round trip.
- `radix_uniqueness`: uniqueness of bounded quotient/remainder and finite digit values.
- `radix_equivalence`: evaluation injectivity, the second round trip, and both full
  equivalences between arbitrary radix and Nat.
- `radix_binary_equivalence`: direct digit algorithms in both directions, their
  correctness and inverse laws, and full binary/radix equivalences. These conversion
  algorithms do **not** use a unary intermediate.
- `binary_univalence_transfer`, `radix_univalence_transfer`: actual transport along
  `ua(e)`, followed by its computation law and arithmetic compatibility. Directions:
  binary -> Nat, binary -> arbitrary radix, arbitrary radix -> binary, arbitrary
  radix -> Nat; also Nat -> binary. Concrete base-2/base-10 endpoints are included.

The equivalences/compatibility proofs use function extensionality, with no choice
or LEM. The univalence transfer layer additionally uses the one existing univalence
axiom. Both concrete numeral-conversion certificates are independent of univalence
and the factorial theorems (their recorded derivations include function
extensionality); the transferred factorial results do not use a manual
factorial proof merely to identify the target numeral.

## Compact Nat acceptance test

`factorial(10) = nat_3628800` is checked without constructing a unary chain of
3,628,800 successors. `nat_3628800` names the binary-to-Nat evaluation expression.
The original `factorial` definition is now boxed (`opaque def`), with the same
checked body; no replacement factorial or new equation is postulated. Decoder
functions also stay boxed. Computation is requested through proved equations.

Measured before inspection on the complete four-direction transfer module:

- 228,271 checked production-kernel instructions;
- 309,599 total syntax nodes; about 51.6 MB reported kernel allocation;
- largest closed unary numeral anywhere in the arena: **10**.

`tests/representation-transfer.test.mjs` checks these structural bounds, actual
proof verification, and exact axiom dependencies. It explicitly does not claim
to be the future native cubical acceptance test. That test must check the same
statements with computational Glue/univalence, with no UA/FunExt axiom fallback,
and preserve the compact allocation bound.

## Normalization and verification

The old elaborator's arbitrary 100-pass normalization cutoff rejected valid
base-10 arithmetic. Normalization now stops at its checked fixed point; every
pass remains a kernel instruction subject to the overall instruction/allocation
bounds. Nat induction's final branch conversion now supports boxed definitions.

Large computations use short checked digit/iteration certificates to avoid
expanding every recursive call simultaneously in the old bottom-up reducer.
The new native cubical checker uses demand-driven conversion and keeps inspection
normalization separate from proof checking.

Targeted checks:

```
npm test -- tests/binary-radix.test.mjs tests/representation-transfer.test.mjs
npm test -- radix_univalence_transfer
```

The new C backend and remaining website migration are tracked separately under
`docs/cubical/`. Cubical univalence's construction is based on the Glue rules in
[Cohen–Coquand–Huber–Mörtberg](https://arxiv.org/abs/1611.02108), not a new opaque
transport oracle.
