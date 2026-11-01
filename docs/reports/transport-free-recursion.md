# Binary recursion without transports

2026-11-01, branch `bnat-transport-free-recursion` on main `d875dd08`.
The library's arithmetic was binary-native, but its strong recursion and
its dependent Peano recursion put transports on the computational path:
the runtime fell back to the kernel's queries on `factorial`, Euclid's
least divisor search and every other user of the recursion, and the
kernel's queries recomputed the rest of the computation at each
composition and stopped at their syntax depth guard (K344) after about
sixty levels. This change makes both recursions compute without a
transport, for arbitrary dependent families, with the public statements
unchanged, and keeps the old recursion's sharing of overlapping calls
([below](#sharing)).

## Before

Measured on `d875dd08`, each entry in a new program after its imports
(`import euclid; use nat;` unless noted): the value form by the runtime
and by the kernel's queries alone (`runtimeEvaluation: false`), and the
demand marks and expected values, which the kernel computes. Ticks are the
kernel's query steps for the entry, steps the runtime's transitions. The
definition a fallback was in was read from the runtime's demand trace.

- **Every value form that recursed fell back at a composition**, the
  first one met in `bnat_peano`'s `bpositive_advance`: the strong
  recursion built its callbacks by `bnat_peano` over `BNatBelow`, whose
  binary advance transports along its offset paths, and each callback
  then retyped the result at the predecessor with
  `comp(fun i => P(same @ ~i), step(n, below))` (`bnat_below_case`).
  That held for `factorial(n)` from 1, `least_divisor(m, tt)` past its
  first candidate, `euclid(n)` and `euclid(n).1` from 1,
  `least_element` (on `nat_peano`), a Peano count, and a dependent strong
  recursion (`IdentityWitness` from `cubist-tests/binary_recursion.cubist`):
  each after 3,600 to 21,700 runtime steps. Only `factorial(0)`,
  `least_divisor(4, tt)`, `euclid(0)` and the searches that end at their
  first candidate computed in the runtime.
- **The kernel's queries stopped with K344** at `euclid(7).1`,
  `euclid(8).1`, `euclid(11).1`, `euclid(13).1` and `euclid(15).1`, at
  `least_divisor` past 28 candidates (`least_divisor(961, tt)`), at
  `factorial(60)`, at `least_element` past 63 candidates and at
  `!!least_divisor(25, tt)`; `factorial(200)` and a Peano count of 200
  stopped with K336, the kernel's native recursion guard.
  On the library's binary Euclid `euclid(4).1` and `euclid(5).1` computed,
  in 57,053 and 160,432 ticks; the K344 rows of the
  [runtime report](runtime-repl-evaluation.md) for those entries are the
  deleted archive's unary Euclid.

## The redesign

### Strong recursion

[`bnat_recursion`](../../library/bnat_recursion.cubist) keeps main's
shape: the values below `succ(n)` extend those below `n` with the step's
value at `n` (`bnat_below_step`), and `bnat_peano`'s advance over binary
offsets builds the extensions up to the bound. Two transports were on
that path, and both are gone.

- **The value at `n`, read at `m`.** A read at `m < succ(n)`
  (`bnat_below_read`) compares `m` with `n` once, on the bits: below `n`
  it delegates to the values below `n`, and at `n` it returns the step's
  value, which was retyped from `P(n)` to `P(m)` by
  `comp(fun i => P(same @ ~i), …)` (`bnat_below_case`) and is now read
  through `bnat_equal_cast`
  ([`bnat_equality`](../../library/bnat_equality.cubist)): a cast along
  equal bits that recurses on the bits of both numbers until they are one
  numeral and then returns the value as it is. The step's value is the
  extension's argument (`bnat_below_extend`), computed once and returned by
  every later read at `n`.
- **The offsets.** The advance moved the values below each bound along its
  offset's path with a composition. It now takes a reindexing
  (`BNatReindex`), and the strong recursion reindexes its callbacks by
  their evidence (`bnat_below_reindex`): a point's evidence is moved to the
  old bound by `bnat_lt_bound`, decided on the bits when it is demanded,
  with the offset's path refuting only the other branch.

The decrease laws, `n < succ(n)` and `pred(p) < p`, are proved on the
bits, with the odd/even and doubling lemmas moved here from
`bnat_division`. Coherence, `bnat_below(…, n)(m, h) =
bnat_strong_recursion(…, m)`, is re-proved for arbitrary dependent
families, with no proof irrelevance assumed: a step keeps the values below
coherent given the equation at its bound, a reindexing keeps them coherent,
the advance keeps them coherent given the equation below its final bound
(its offsets' order decided on the bits, `bnat_lt_add_right`), and the
coherence at every `n` is proved by the strong recursion itself as
induction. `bnat_strong_recursion_equation` follows as before.

### Peano recursion

[`bnat_peano`](../../library/bnat_peano.cubist) is main's advance over
binary offsets with the reindexing `bnat_equal_reindex`: each offset's
two numerals have equal bits, so the value is read at the offset through
`bnat_equal_cast`, which transports nothing, for any dependent family.
The successor equation is proved once for any reindexing that agrees with
its paths (`BNatReindexTotal`, `bnat_peano_reindexed_succ`); the cast's
agreement is `bnat_equal_cast_total`.

### The searches

The [divisor search](../../library/prime_numbers.cubist) passed to each
next candidate a proof of its distance to the number built from the last
one, `trans(…, trans(…, distance))`, which grew by a composition at every
candidate. The kernel's queries, which substitute an argument unevaluated,
still met K344 there once the recursion's own transports were gone:
`least_divisor(3721, tt)`, with 60 candidates, and `euclid(7).1`, with 70,
stopped. The next distance is now decided on the bits
(`nat_decide`), the decision's own path passed on and the old proof only
refuting the other branch, at the cost of one comparison a candidate.
[`least_element`](../../library/least_elements.cubist) ran on Peano
recursion and transported the witness's evidence to every candidate; it now
recurses on the candidate's distance to the witness in the same way, the
evidence it finds being the decision's own and the witness's only
refuting at distance zero.

### The statements

Every public statement is unchanged: `BNatBelow`, `bnat_strong_recursion`
and its equation, `nat_strong_recursion` and its equation, `bnat_peano`,
`nat_peano` and their zero and successor equations, `bnat_peano_total`,
`bnat_factorial` with its zero and successor laws, `least_divisor`,
`euclid`, `least_element` and `least_element_from_mere`. `bpositive_advance`
takes a reindexing, and `bnat_peano_reindexed` is the advance from zero
with one. The search helpers `DivisorSearch` and `LeastSearch`, internal to
their modules, keep their roles; `LeastSearch` now takes the witness and
states the distance. `bnat_below_case`, `bnat_below_case_coherent`,
`bnat_below_succ`, `bnat_total_reindex`, `least_search_zero` and
`least_search_succ` are removed; nothing outside their modules used them.

## Sharing

The first version of this change iterated a course of values, a bound with
the values below it, by `bnat_iterate`, each step giving the values below
`succ(b)` as the step at every `m`. Nothing was retyped, but nothing was
stored either: a read at `m` rebuilt `step(m, …)` from the values below,
so a branching recursion recomputed its overlapping calls. Codex's first
review of #346 found it with a Fibonacci on the strong recursion, whose
step asks for the values at the predecessor and at its predecessor
([`strong_recursion_contracts`](../../tests/fixtures/contracts/strong_recursion_contracts.cubist)):

| `fib(n)` | Main: runtime | Main: kernel's queries | The course of values | Now: runtime | Now: kernel's queries |
| --- | --- | --- | --- | --- | --- |
| 22 | fallback after 5,964 steps | 171,135 ticks | E488 in the runtime; 14,810,142 ticks | 203,420 steps, 16 ms | 184,472 ticks |
| 25 | fallback after 6,084 steps | 197,821 ticks | E488; 64,203,550 ticks | 238,987 steps, 21 ms | 211,118 ticks |
| 40, expected `102334155` | the kernel's | 485,034 ticks | K347, the arena exhausted, after 211,237,733 ticks | the kernel's | 428,441 ticks |

Now each smaller value is computed once and shared, in the runtime, where
it is the extension's argument cell, and in the kernel's queries, where it
is one term that every read returns. The course of values cost the linear
recursions less, since it compared nothing: `euclid(5).1` took 105,313
ticks on the kernel's queries against 198,313 now, `factorial(40)`
6,138,059 against 7,589,076. A read now compares the point with its bound
and casts the value on the bits, a few operations a level whose cost grows
with the bound's bits.

## After

`node tools/runtime-repl-probe.mjs`, each sample in a process of its own,
on this branch at `e34cf46a` with a clean tree and on `d875dd08`'s library
modules in the same tree, Node 24.13.0, macOS arm64 (Apple M3 Pro),
runtime SHA-256 prefix `0ca9a938c16da1a5`, one run each. The machine was
shared with other heavy jobs, so the times are single loaded samples, not
speed claims.

| Workload | Main: runtime | Main: kernel's queries | Now: runtime | Now: kernel's queries |
| --- | --- | --- | --- | --- |
| `euclid(3)` | fallback after 4,687 steps, 9 ms | 26,944 ticks, 9 ms | 41,614 steps, 11 ms | 31,726 ticks, 7 ms |
| `euclid(4).1` | fallback after 4,943 steps, 12 ms | 57,053 ticks, 11 ms | 73,913 steps, 12 ms | 71,540 ticks, 9 ms |
| `euclid(4)` | fallback after 4,938 steps, 12 ms | 61,786 ticks, 9 ms | 76,823 steps, 14 ms | 73,434 ticks, 19 ms |
| `euclid(5).1` | fallback after 5,184 steps, 19 ms | 160,432 ticks, 15 ms | 216,057 steps, 20 ms | 198,313 ticks, 19 ms |
| `euclid(6).1` | fallback after 5,425 steps, 16 ms | 133,848 ticks, 13 ms | 173,329 steps, 18 ms | 167,332 ticks, 15 ms |
| `euclid(10).1` | fallback after 4,939 steps, 33 ms | 423,409 ticks, 27 ms | 531,058 steps, 32 ms | 519,923 ticks, 36 ms |
| `euclid(7).1` | K344 | K344 after 634,130 ticks | 2,617,533 steps, 74 ms | 1,935,443 ticks, 120 ms |
| `euclid(3).1 expecting 7` | the kernel's | 25,278 ticks, 10 ms | the kernel's | 31,594 ticks, 9 ms |
| `euclid(5).1 expecting 11` | the kernel's | 162,533 ticks, 16 ms | the kernel's | 200,559 ticks, 19 ms |
| `!!euclid(5)` | the kernel's | 319,743 ticks, 26 ms | the kernel's | 298,779 ticks, 26 ms |
| `factorial(40)` | fallback after 4,459 steps, 1,200 ms | 38,346,979 ticks, 1,193 ms | 951,525 steps, 41 ms | 7,589,076 ticks, 277 ms |
| `least_divisor(44521, tt).1`, 210 candidates | K344 | K344 after 690,421 ticks | 10,695,566 steps, 188 ms | 6,867,452 ticks, 437 ms |
| `least_divisor(63001, tt).1`, 250 candidates | K344 | K344 after 679,609 ticks | 12,825,717 steps, 223 ms | K344 after 7,588,973 ticks |
| `least_element(…, 1000000, tt).1`, least 240 | K344 | K344 after 214,535 ticks | 5,458,094 steps, 109 ms | 5,267,427 ticks, 274 ms |
| a Peano count of 300 | K336 | K336 after 27,343 ticks | 1,653,757 steps, 42 ms | 1,928,519 ticks, 172 ms |
| `fib(25)` | fallback after 6,084 steps, 21 ms | 197,821 ticks, 20 ms | 238,987 steps, 21 ms | 211,118 ticks, 17 ms |

No value form of `factorial`, `least_divisor`, `euclid`, `least_element`,
`nat_peano`, the Fibonacci or a dependent strong recursion falls back:
every one measured computes in the runtime, and the evaluation baseline,
the runtime and demand-mark tests and the probe's workloads agree. Of the
source contracts' value forms, the only fallbacks left are the univalence
path's compositions in `radix_contracts`, which are transports by design,
and `divides_decide(0, 0)`, at a path abstraction's η, which the recursion
does not reach. Where main's kernel queries compute, they now take a fifth
to a third more ticks on the small Euclid and factorial entries (the
baseline's `factorial(4)` normal form, 18,068 against 13,793), and fewer
on `!!euclid(5)`; `factorial(40)` takes a fifth of main's.

**The kernel's queries alone**, which value forms would return to without
the runtime, now compute:

| | Main | Now |
| --- | --- | --- |
| `euclid(n).1`, n from 0 to 10 | 0 to 6, 9 and 10; K344 at 7 and 8 | all; also 12, 13 (82 candidates) and 15; K344 at 11, whose 39,916,801 is prime |
| `least_divisor` | 28 candidates (`least_divisor(841, tt)`); K344 at 30 (`least_divisor(961, tt)`) | 210 candidates (`least_divisor(44521, tt)`); K344 at 250 |
| `least_element` | 63; K344 at 64 | 240; K344 at 300 |
| Peano recursion, a count | 100; K336 at 200 | 300; K336 at 1,000 |
| `factorial(n)` | 40; K344 at 60 | 60, in 138,487,845 ticks |
| `!!least_divisor(25, tt)` | K344 | 202,120 ticks |

Syntax depth, measured over the nodes each kernel normalization allocated,
grows by about two levels a candidate in the divisor search (165 at 60
candidates, 347 at 150, 464 at 210) and in the least element search (149 at
60, 426 at 200), and by one level a step in the Peano count (102 at 100, 302
at 300); the diagnosis measured about sixteen a candidate in the divisor
search before. K336 now appears only in the Peano count past 300, whose
step accumulates `succ(count)`, each successor's weak head asking the one
below it in a nested native call.

## What the kernel's K344 was

On the kernel's path the substituted terms grow with the recursion's
depth wherever something is carried from one level to the next without
being evaluated. Before this change three things grew in Euclid's search:
the recursion's retyping compositions, pushed through the search's Π type
to each argument, `bpositive_advance`'s compositions in the callbacks, and
the search's distance proof. With the recursion transport-free the
distance proof alone stopped `euclid(7).1`, as a chain of path
abstractions, compositions and tubes over the previous distance at every
candidate; deciding it removed that. What still grows is data the search
must keep: its minimality certificate, one `no_divisor_below_succ` over
the last at every candidate, about two syntax levels a candidate. A
diagnosis made in parallel, read-only, found the same causes.

## Outcomes

Every printed value is the same, by the runtime and by the kernel, and
every value form, expected value and `!!` text of the source contracts and
the Cubist tests is unchanged. Four workloads of the evaluation baseline,
`!!!euclid(3)`, its `print` twin, `!!!euclid(4)` and
`euclid(4) expecting !!!(5, _)`, print the same 1,000 characters, but their
full normal forms, cut there, differ past them: the minimality
certificate's normal form no longer holds the compositions the recursion's
retyping wrapped around the search's arguments
(`compose k in BNat from compose k in BNat from …`), so its digest moved.
The baseline is recorded as version 11 for this, for the runtime's new
value forms, for the new depth failure and for the Fibonacci.

## Workarounds and open points

- Deciding each next distance in the two searches is a choice made for
  the kernel's queries, which substitute proofs unevaluated: it keeps a
  proof from growing at the price of one comparison a candidate, 10 to 13%
  of the search's work when measured on the course of values
  (`euclid(5)`'s value form by the kernel's queries, 93,379 ticks with the
  threaded proof and 103,848 decided; `euclid(7).1` in the runtime,
  1,832,264 and 2,078,543 steps). A kernel that shared or evaluated such
  arguments would not need it.
- Sharing costs the linear recursions a comparison and a cast on the bits
  at every level (above, [Sharing](#sharing)): on the kernel's queries,
  `euclid(5).1` takes 198,313 ticks where main took 160,432, and a
  descent through 100 levels 552,117 where main took 266,884.
- `factorial(n)` on the kernel's path costs about what the product
  `n * ((n - 1) * (…))` of literals costs, 6.5M ticks at 40 and 130M at
  60, against 0.6M and 1.7M for the same product nested the other way:
  the kernel's lazy multiplication of a large lazily computed right
  operand. `bnat_factorial`'s step multiplies `n` by the recursive value,
  as its successor law states.
- A Peano count of 100 costs 456,100 ticks on the kernel's path where main
  took 49,503: each offset casts its value on the bits, where main's
  compositions forced nothing until they met K336 at 200.
- In the runtime, `least_divisor(1000003, tt)` and `euclid(11)`, which
  take a thousand candidates and more, stop at its allocation budget
  (E488); the kernel's queries stop with K344.
- `divides_decide(0, 0)` still falls back, at an η-expanded path
  abstraction, which this change does not touch.

## Checks

- `npm test` at `7e261629`: 2,144 of 2,145 tests passed; the one failure
  counted `bnat`'s declarations, which the two casts raise from 27 to 29,
  and passes with the count corrected (`4f2e931e`); at `5415473e` all
  2,145 passed. The source contracts,
  the Cubist tests, the library and corpus checks, the evaluation baseline
  and the driver trace (unchanged) are among them.
- `node tools/audit-cubical.mjs --all`: 353 modules, 3,527 declarations,
  no failure.
- `npm run format:cubist` and `npm run lint:cubist`: no change, no
  warning. The Files index (`web/cubist-files.json`) is regenerated for the
  README rows.
- New checks: the runtime test asserts that the value forms of Euclid,
  factorial, the least divisor and least element searches compute in the
  runtime with no fallback, and `euclid(7).1` both ways; the runtime query
  test reads Euclid's prime from the runtime bit by bit; the contracts
  `euclid.witness_7`, `euclid.witness_8` and `least_elements.far_least`,
  and the Cubist test's Peano count of 300, compute only where the
  recursion builds no growing term.
