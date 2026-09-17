# Infinitely many primes

Open **Infinitely many primes (Euclid)** in the workbench, or use the CLI:

```text
open primes
check InfinitelyManyPrimes infinitely_many_primes
```

The kernel checks the closed, constructive theorem

```text
∀ n : Nat, Σ p : Nat, Prime(p) × (n < p).
```

The saved proof has **4,327 instructions and no axioms**. It runs with axioms
disabled. In particular, it assumes neither excluded middle, choice, function
extensionality, prime-factor existence, nor arithmetic laws.

## Definitions

All arithmetic uses the kernel's primitive `Nat`, zero, successor, and induction.
Addition and multiplication recurse on their first argument. Factorial has
`0! = 1` and `(n+1)! = (n+1) * n!`. Order is defined by simultaneous recursion:
`0 ≤ n` is Unit, `succ(m) ≤ 0` is Void, and
`succ(m) ≤ succ(n)` is `m ≤ n`. Strict order means `succ(m) ≤ n`.

`Divides(d, n)` is `Σ k : Nat, k*d = n`. Primality is the standard absence of
proper nontrivial divisors, written with explicit offsets:

```text
Prime(p) := Σ i : Nat,
              (p = 2+i) × (∀ j : Nat, j < i → ¬Divides(2+j, p)).
```

Thus 0 and 1 are excluded, and every possible divisor from 2 through p−1 is
excluded. The generator independently constructs checked proofs that 2 is prime
and that 0, 1, and 4 are not prime; it also checks small arithmetic examples.

## Argument

1. Derive addition and multiplication laws, order lemmas, and decidable equality
   by natural-number induction and equality elimination.
2. Construct bounded search for a decidable predicate. Its result either gives
   the least witness up to the bound or refutes every candidate in that range.
3. Decide divisibility by `d ≥ 2`: any quotient witnessing `k*d = m` satisfies
   `k ≤ m`, so bounded search suffices.
4. For `m ≥ 2`, choose its least divisor `p ≥ 2`. Such a divisor exists because
   `m` divides itself. A proper nontrivial divisor of `p` would divide `m` by
   transitivity, contradicting minimality. Therefore `p` is prime.
5. Apply this to `m = n! + 1`, which is at least 2. If `p ≤ n`, then `p` divides
   `n!` as well. Induction on the two quotients proves that a number at least 2
   cannot divide consecutive numbers. Hence `n < p`.

This is the standard factorial version of
[Euclid's argument](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Infinite.html),
implemented here from the primitive rules rather than imported from another prover.

## Inspecting and regenerating

The exported lemmas include `bounded_least_search`,
`nontrivial_divisibility_decidable`, `prime_divisor_exists`,
`bounded_divisor_of_factorial`, and `nontrivial_divisor_not_consecutive`.
Use **Inferred by** to follow premises, or enable **Show intermediate steps**.
The final object displays its verified type, `InfinitelyManyPrimes`.

The proof-producing sources are:

- [`arithmetic.mjs`](../tools/proofs/arithmetic.mjs): arithmetic and order.
- [`number_theory.mjs`](../tools/proofs/number_theory.mjs): bounded search and divisibility.
- [`euclid.mjs`](../tools/proofs/euclid.mjs): prime divisors and the final argument.
- [`check_primes.mjs`](../tools/proofs/check_primes.mjs): independent boundary checks.
- [`primes.mjs`](../tools/proofs/primes.mjs): dependency pruning and artifact export.

Run `make proof-export` to regenerate. The generator replays the optimized proof
in a fresh axiom-disabled engine before saving it. JSON and `.math` source both
replay through the same kernel. The arithmetic library requires larger workbench
resource bounds: 8,192 instructions and context counters up to 4,096; expression,
depth, arena, judgement, and memory limits are unchanged. No inference rule was
added or weakened for this theorem.
