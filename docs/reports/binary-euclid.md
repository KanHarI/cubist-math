# Binary divisibility, primes and Euclid in the library

Part one of EVAL7 in the
[runtime evaluation roadmap](../roadmaps/runtime/runtime-evaluation-roadmap.md#eval7-reduce-the-algorithms-work),
step NT2 of the [archive retirement](../roadmaps/archive-retirement.md#number-theory-in-the-library),
2026-10-28: the library modules over binary `Nat`. The archive's unary
`primes` and `euclid` are unchanged and keep every consumer until part two
moves them; the comparisons below run both, as separate source-algorithm
series.

## The modules

Five modules, none of which uses an assumption; every declaration is
`computable`. None takes the name of a module in use: a library `primes` or
`euclid` would shadow the archive's for the Cubist tests, the REPLs and the
tools that import them, which is part two's change.

| Module | Holds |
| --- | --- |
| [`bnat_order_laws`](../../library/bnat_order_laws.cubist) | The order laws the others need: a comparison reversed, what is not below is at or above, irreflexivity, positive products, the successor in the order, cancellation of a strict sum, monotone products. Laws about the bits are proved on the bits; the others decide the binary comparison, return its own evidence, and refute the other branch through `bnat_order`'s unary correspondence. |
| [`bnat_division`](../../library/bnat_division.cubist) | Division with remainder by a positive divisor, and the borrow subtraction it uses. |
| [`divisibility`](../../library/divisibility.cubist) | `Divides(d, n) := exists q : Nat. q * d = n`, its remainder-based decision, and the lemmas Euclid needs. |
| [`prime_numbers`](../../library/prime_numbers.cubist) | `Prime`, the least divisor search and its certificate. |
| [`binary_euclid`](../../library/binary_euclid.cubist) | `euclid : InfinitelyManyPrimes`, the archive's statement over binary `Nat`. |

### Division with remainder

`bpositive_divmod(n, d)` recurses to the leading bit of `n` and takes one
long-division digit for each lower bit: the remainder so far, doubled with
the bit, is below twice the divisor, so it holds the divisor at most once.
A digit is one comparison and, when the divisor fits, one subtraction:
`bnat_sub` subtracts low bit first, carrying the pair `(p - q, p - q - 1)`
as the borrow. `bnat_sub(a, b)` is `a - b` for `b <= a`
(`bnat_add_sub`); division calls it only after its comparison. The
certificate, `bnat_divmod_correct(n, d) : q * d + r = n and r < d`, is a
separate theorem by the same recursion on bits, from addition and doubling
laws that hold by computation. Its folded normal form at 121 and 11 is
`(refl(121), tt)`.

### The divisibility decision

`divides_decide(d, n)` divides once. For a positive divisor, a zero
remainder gives the quotient as the witness; any other remainder refutes
every multiple, since `k * d = q * d + r` with `r < d` forces `r = 0`
(`bnat_remainder_zero`, whose unary argument compares `k` with `q`). Zero
divides only zero. The archive searches quotient candidates up to the
dividend, testing each product for equality.

### The least divisor search

`least_divisor(m, 1 < m)` returns the least divisor of `m` above one with
its certificate, `IsLeastDivisor(m, p)`: `1 < p`, `p` divides `m`, and no
divisor of `m` lies strictly between one and `p`. Candidates rise from 2:

- past the square root, `m < d * d`, the answer is `m` itself;
- a candidate that divides `m`, by the remainder decision, is the answer;
- otherwise the search goes on with the next candidate.

The search is NUM1's strong recursion on the candidate's distance `k` to
`m`, with `d + k = m`: each further call is at `k - 1`, a strict decrease
(`bpositive_pred_lt`). At distance zero the candidate is `m`, which divides
`m`, so the search ends there at the latest. The square-root bound is
proved (`no_divisor_past_square`): a divisor `e < m` of `m` and its
cofactor both divide `m` and are above one, so with no divisor below `d`
both are at least `d`, and their product `m` at least `d * d`. The least
divisor is the archive's (`prime_divisor_exists` finds the least divisor at
least 2), and it is prime (`least_divisor_prime`).

### Euclid

For every `n`, `p` is the least divisor of `succ(factorial(n))` above one,
with `nat`'s factorial. `n < p` is the binary comparison's evidence when it
holds; otherwise `p <= n`, so `p` divides `n!` (every number from one to
`n` does, `divides_factorial`) and `n! + 1`, which no number above one does
(`divisor_not_consecutive`: `n! + 1` leaves remainder one). This is the
archive's argument.

## Acceptance

- **Checked, without assumptions.** `tests/library.test.mjs` checks the five
  modules completely with no assumption; the source contracts
  ([`binary_euclid_contracts`](../../tests/fixtures/contracts/binary_euclid_contracts.cubist))
  state `expect_axioms([])` for the theorem, the search and the decision.
- **The witnesses.** `evaluate euclid(n).1 expecting p;` for `n` from 0 to 5
  with `p` = 2, 2, 3, 7, 5, 11; `euclid(3)`, and the certificates of
  `euclid(5)`, under `!!_`;
  division, the decision's branches and the search's exits (a composite, a
  prime past its square root, an even number, and a square with its
  divisor's certificate under `!!_`). The Cubist test module
  [`prime_witnesses`](../../cubist-tests/prime_witnesses.cubist) shows the
  same witnesses as printed values, a value form, `(5, (tt, <fun>), tt)` for
  4, and a folded normal form.
- **Folded normal forms are small.** `!!euclid(n)` keeps the search's
  certificate named, `least_divisor(121, tt).2.2.2(…)` at 5: 375 characters
  for 0 to 3, 377 for 4, 387 for 5 and 389 for 6. The archive's are 104 for
  0 and 1, 607 for 2 and 640 for 3, and stop with K344 at 4.

## Measurements

`node tools/runtime-repl-probe.mjs` checks each workload's setup in a
fresh REPL session and measures one entry, by the runtime and by the
kernel's queries alone, each sample in a process of its own
([the probe](runtime-repl-evaluation.md#measurements)). The archive's
workloads are `import euclid; use unat;`, the library's
`import binary_euclid; use nat;`. Three runs at `0e3404dc`, this change on
main `a30189f5`, Node 24.13.0, macOS arm64 (Apple M3 Pro, 36 GiB),
runtime SHA-256 prefix `12e703bcb1787daf`; every counter was the same in
all three. The machine was shared with other heavy jobs (load average
20–55 during the runs), so the times are medians of three loaded samples,
not speed claims. Ticks are the kernel's query steps for the entry, steps
the runtime's transitions; the units differ.

| Entry | Archive, kernel's queries | Archive, runtime | Library, kernel's queries | Library, runtime |
| --- | --- | --- | --- | --- |
| `euclid(3)` | value, 150,918 ticks | same value, 247,542 steps | `(7, (tt, <fun>), tt)`, 26,666 ticks | fallback at a composition after 64,482 steps; 26,667 ticks |
| `euclid(4).1` | K344 after 655,030 ticks | `5`, 469,175 steps | `5`, 56,921 ticks | fallback after 64,711 steps; 56,921 ticks |
| `euclid(4)` | K344 after 652,129 ticks | `(5, (3, <path>, <fun>), tt)`, 1,385,819 steps | `(5, (tt, <fun>), tt)`, 61,619 ticks | fallback after 64,723 steps; 61,620 ticks |
| `euclid(5).1` | K344 after 887,726 ticks | `11`, 28,187,952 steps, 15,566,553 cells | `11`, 157,971 ticks | fallback after 64,952 steps; 157,972 ticks |
| `euclid(6).1` | K336 after 465,336 ticks | E488 at 20M cells | `7`, 136,013 ticks | fallback after 65,193 steps; 136,013 ticks |
| `euclid(10).1` | — | — | `11`, 512,364 ticks | fallback after 64,672 steps; 512,364 ticks |
| `euclid(7).1` | — | — | K344 after 653,941 ticks | fallback, then K344 after 653,941 ticks |
| `euclid(3).1 expecting 7` | 149,722 ticks | the kernel's | 25,099 ticks | the kernel's |
| `euclid(5).1 expecting 11` | K344 after 887,729 ticks | the kernel's | 160,169 ticks | the kernel's |
| `!!euclid(5)` | — | — | 312,544 ticks, 387 characters | the kernel's |

Median entry times, runtime and kernel paths: the archive's `euclid(5).1`
took 2,617 and 151 ms, its `euclid(6).1` 1,649 and 121 ms; every library
entry took at most 176 ms on either path. Process peaks were 143–177 MiB
for the archive's entries, but 610 MiB for `euclid(5).1` and 508 MiB for
`euclid(6).1` by the runtime, and 292–307 MiB for the library's, whose
setup loads the binary foundations.

## Findings

**The runtime does not execute the library Euclid.** NUM1's Peano and
strong recursion transport along offset paths (`bpositive_advance`,
`bnat_below_case`), and the runtime reports a composition unsupported: each
library value form falls back to the kernel's queries after about 65,000
runtime steps and a snapshot of about 16,140 nodes, whatever `n`. The
kernel's queries then compute every library value form measured but
`euclid(7)`, where the archive's stop from `euclid(4).1` on.

**A depth limit, met by NUM1's strong recursion alone.** `7! + 1 = 71 * 71`
takes 70 candidates, and the kernel's queries stop with K344 at the syntax
depth guard; `8! + 1 = 61 * 661` takes 60 and stops the same way, while
`9! + 1` and `10! + 1`, with 18 and 10 candidates, compute. A recursion that
only calls itself at the predecessor meets the same guard at these depths:

```cubist
computable def descend_positive(
  floor : Nat, p : BPositive, below : NatBelow(U0, fun (m : Nat) => Nat, b_positive(p))
) :
  Nat := match bnat_lt_decide(floor, b_positive(p)) return Nat {
    left above => below(bpositive_pred(p), bpositive_pred_lt(p));
    right no => b_positive(p);
  };

computable def descend_step(floor : Nat, n : BNat) :
  BNatBelow(U0, fun (m : BNat) => BNat, n) -> BNat := match n {
    b_zero => fun (below : BNatBelow(U0, fun (m : BNat) => BNat, b_zero)) => b_zero;
    b_positive(p) => descend_positive(floor, p);
  };

computable def descend(floor, n : Nat) :
  Nat := nat_strong_recursion(U0, fun (m : Nat) => Nat, descend_step(floor), n);
```

`descend(4970, 5039)`, 69 levels, and `descend(1000, 1100)`, 100, stop
with K344; `descend(40260, 40319)`, 59 levels, and `descend(0, 200)`
compute; `descend(0, 1000)` stops with K336. In `bnat_below_case`, the call
at the predecessor returns under a transport,
`comp(fun (i : Interval) => P(same @ ~i), step(n, below))`, so each level
presumably nests one more. Lifting the limit is NUM1's or the evaluator's
work (EVAL4's explicit stack), not the search's.

**The search's own certificate is a function, normalized under its
binders.** `!!euclid(n)` keeps it named, but `!!least_divisor(m, …)`
normalizes the minimality certificate, one layer a candidate with the
recursion's transports: at 25 it stops with K344. The contracts observe it
by its weak head. A variant that returned the least divisor as a number,
with its certificate a separate theorem by strong induction, was tried and
withdrawn: reading even `1 < p` from that certificate unfolds NUM1's
coherence path. Checked as a file with its imports, the six witnesses and
two value forms took 34.2M ticks against 0.42M, and `!!euclid(5)` 34.8M
against 0.50M, its output past 1,000 characters.

## Part two

The decided migration
([roadmap](../roadmaps/runtime/runtime-evaluation-roadmap.md#eval7-reduce-the-algorithms-work)):
every consumer of the archive's `euclid` moves to the library Euclid (the
landing page, quick reference and reference examples; the site, inspector,
program and instruction-driver tests; the evaluation baseline, under a new
version; #289's probe and tests, and this probe's archive workloads; the
demand-marks report), then `euclid.cubist` is deleted and `primes` loses
`Divides`, its decision and lemmas, `Prime`, `prime_divisor_exists`,
`factorial_positive` and `bounded_divisor_of_factorial`. Part two also
decides the library module's final name: once the archive's `euclid` is
gone, `binary_euclid` can take it.
