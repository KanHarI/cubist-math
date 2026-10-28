# Binary divisibility, primes and Euclid in the library

EVAL7 in the
[runtime evaluation roadmap](../roadmaps/runtime/runtime-evaluation-roadmap.md#eval7-reduce-the-algorithms-work),
step NT2 of the [archive retirement](../roadmaps/archive-retirement.md#number-theory-in-the-library),
2026-10-28. Part one built the library modules over binary `Nat`, beside
the archive's unary `primes` and `euclid`, which kept every consumer; its
comparisons ran both, as separate source-algorithm series. Part two
([below](#part-two)) moved every consumer to the library's Euclid, named it
`euclid`, and deleted the archive's Euclid and `primes`' divisibility and
primality. Part one's sections keep their measurements as taken; where they
name `binary_euclid`, that is the module part two renamed.

## The modules

Five modules, none of which uses an assumption; every declaration is
`computable`. In part one none took the name of a module in use: a library
`primes` or `euclid` would have shadowed the archive's for the Cubist tests,
the REPLs and the tools that import them. Part two named the Euclid module
`euclid`, once the archive's was deleted.

| Module | Holds |
| --- | --- |
| [`bnat_order_laws`](../../library/bnat_order_laws.cubist) | The order laws the others need: a comparison reversed, what is not below is at or above, irreflexivity, positive products, the successor in the order, cancellation of a strict sum, monotone products. Laws about the bits are proved on the bits; the others decide the binary comparison, return its own evidence, and refute the other branch through `bnat_order`'s unary correspondence. |
| [`bnat_division`](../../library/bnat_division.cubist) | Division with remainder by a positive divisor, and the borrow subtraction it uses. |
| [`divisibility`](../../library/divisibility.cubist) | `Divides(d, n) := exists q : Nat. q * d = n`, its remainder-based decision, and the lemmas Euclid needs. |
| [`prime_numbers`](../../library/prime_numbers.cubist) | `Prime`, the least divisor search and its certificate. |
| [`euclid`](../../library/euclid.cubist) | `euclid : InfinitelyManyPrimes`, the archive's statement over binary `Nat`; `binary_euclid` in part one. |

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
  ([`euclid_contracts`](../../tests/fixtures/contracts/euclid_contracts.cubist),
  `binary_euclid_contracts` in part one)
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

Done on 2026-10-28, on main `27c0cc38`: the decided migration
([roadmap](../roadmaps/runtime/runtime-evaluation-roadmap.md#eval7-reduce-the-algorithms-work)).

### The name

The library's Euclid module, `binary_euclid` in part one, is now
[`euclid`](../../library/euclid.cubist). With the archive's deleted it
shadows nothing, and the name every entry point has always used for Euclid
now finds the library's, since a bare module name is looked up in
`library/` first: `proof.html?proof=euclid`, the workspace's default page
and the landing page's first card; `node cli/repl.mjs check euclid`;
`npm test -- euclid`; and `import euclid;` in a REPL. Its source contracts
are [`euclid_contracts`](../../tests/fixtures/contracts/euclid_contracts.cubist),
with the test IDs `euclid.*`. `prime_numbers` keeps its name: the archive's
`primes` remains until NT3 and NT4.

### Every consumer moved

- **Site.** The landing page's Euclid card describes the library's argument
  and opens it; the workspace opens the library's Euclid when its URL names
  no module or an unknown one (it fell back to an archive path); the quick
  reference's default source is `library/euclid.cubist`; the language page lists `euclid` among the
  library's examples; the module lists (`web/cubist/modules.mjs`), the
  archive's proof catalog (`web/proof-library.mjs`, where `primes` is
  retitled for what it keeps) and the Files index (`web/cubist-files.json`).
  The reference's checking chapter names `check euclid` as a module found
  in `library/` first, which it now is; no reference example imported the
  archive's Euclid or a deleted definition. The benchmark page's saved
  reports linked each row to today's workspace, where `primes.Prime` and
  the archive's `euclid` no longer exist and `euclid` names the binary
  theorem. A saved report now pins each module it measured exactly as
  committed, with its path and the measured text's SHA-256, and a row links
  to that source at the recorded revision, on the repository; a row
  measured from working changes has no link, since no committed source is
  the one measured. A dated record stays truthful this way through every
  later deletion. The archive's report, measured at `d92b54e8` on a clean
  tree, pins every module; the library's and the Cubist tests', measured
  there with working changes whose texts were not kept, were recorded again
  on a clean tree.
- **Tests.** The site, landing, inspector, cubical and proof-navigation
  browser tests open the library's Euclid: its goal at line 16, its local
  `least : IsLeastDivisor(succ(factorial(n)), p)` in the inspector, the
  workbench and the kernel graph, and `least_divisor`'s source in
  `prime_numbers`; the topic picker, which lists the archive, is exercised
  on `signed_integers` and `paths_`, and an archive page's library import on
  `basics`. The inspection, program and instruction-driver tests check
  `library/euclid.cubist`; module resolution, the test runner's selection
  and the REPL's `/modules` take `basics` as their archive entry point; the
  reference harness's excerpt example quotes `divisibility`; and the
  reference's link check resolves a link by the site's mounts
  (`tools/site-layout.json`), so that the quick reference's link into
  `library/` resolves as `archive/` did.
- **#289's tests.** `tests/runtime-evaluation.test.mjs` prints the library's
  value forms both ways: each falls back at a composition, and the kernel's
  queries show `(7, (tt, <fun>), tt)`, `5`, `(5, (tt, <fun>), tt)`, `11`,
  `7` and `120`, and stop at `euclid(7).1` with K344 either way. The
  runtime's own limits, which the archive's `euclid(5)` and `euclid(6)`
  reached, are exercised by `duplicated-calls-24`: E488 at the allocation
  cap, not retried, and E629 under a 150 ms declaration limit.
  `tests/cubical-runtime.test.mjs` checks that the library's prime stops the
  query at a composition with no native syntax allocated, and keeps the
  archive workload's other checks on unary recursion defined in the test:
  `factorial(6)` observed digit by digit without native syntax, and a
  parity 10,000 levels deep stopped by its step budget past 3,500 frames.
  The demand marks' tests take `euclid(7).1` as the component whose weak
  head fails, and the library's `euclid(3)` for the patterns' costs.
- **Probes.** `tools/runtime-repl-probe.mjs`'s `euclid-*` workloads are the
  library's (part one's `binary-euclid-*`). `tools/shared-evaluation-probe.mjs`
  observed the archive's unary primes through the runtime and is retired
  with it; the [shared runtime report](shared-runtime-evaluation.md) keeps
  its figures. The [demand marks' report](../roadmaps/historical/evaluation-demand-marks/report.md)
  and its scripts keep the archive's Euclid cases as measured, reproducible
  in a checkout before the deletion.
- **Documents.** The Cubist guide, the library and Cubist-test READMEs, the
  results catalog (Euclid's theorem recorded as rebuilt), the tactical
  checkpoint, the RH roadmap's prime arithmetic, and the runtime REPL
  report.

### Deleted from the archive

`euclid.cubist` (`InfinitelyManyPrimes` and `euclid`), and from `primes`
its ten definitions of divisibility and primality: `nat_quotient_bound` and
`nontrivial_divisibility_decidable` (the decision), `Divides`,
`divides_transitive`, `multiples_not_adjacent`,
`nontrivial_divisor_not_consecutive`, `factorial_positive`,
`bounded_divisor_of_factorial`, `Prime` and `prime_divisor_exists`.
`primes` keeps 258 of its 494 lines: `bounded_least_search` and
`least_bounded_witness`, which `natural_minimum` uses (NT3), and the unary
`factorial`, which four numeral modules use (NT4).

Nothing used them. Of every Cubist source, 239 reach `primes` through their
imports, directly or not: 192 archive modules, 40 Cubist tests and 7
documentation examples. None names a deleted definition, and no source but
the library's own imports `euclid`; JavaScript tests and tools named them
only through the moved consumers. The corpus test counts 3,843
declarations, 12 fewer, and `node tools/audit-cubical.mjs --all` checks
371 modules and 3,843 declarations with no failure.

### Re-recorded

- **The evaluation baseline, version 10** (`tests/fixtures/evaluation-baseline.json`,
  five samples, three warm runs, at this branch's merge with main `216b7a6f`): its Euclid,
  factorial and divisibility workloads are the library's, with
  `divides_decide` for the decision, and `euclid-7-prime` and its `!!!` twin
  record the library's depth failure. The unary arithmetic workloads import
  `unat` alone: their entries' outcomes, instructions and runtime steps
  are version 9's, their ticks within 14 and their arena one node larger. The cubical ones keep their
  outcomes and instructions; their query ticks moved by under 2%, the net of
  the driver fix below (+2.5% for the winding numbers, measured alone) and of
  main's `hlevels` gaining `subtype_injective` (#333). Recorded first at
  `27c0cc38` with this change, the record was taken again after the merge:
  #333's lemma moved every library entry's ticks by 0.2–2.3% and its
  instruction steps by a few, outcomes and runtime steps unchanged. With
  #322's recursion guards in the kernel, restoring `hlevels.cubist` alone
  restores the first record's counters of `factorial-4` and `winding-2`. The scratch closure
  experiment, which reads unary numbers only and which the runtime
  replaced, is retired with its series. The unary series keeps its
  revisions: version 9, at main `27c0cc38`, is its last record.
- **The driver trace** (`tests/fixtures/driver-trace.json`) is unchanged.
- **The Files index** (`web/cubist-files.json`), for the renamed and deleted
  files.

### Before and after

The baseline's workloads, version 9 (the archive's unary Euclid) against
version 10 (the library's). Ticks are the entry's kernel query steps,
runtime steps the runtime's transitions; times are cold medians of five
samples on one machine (Node 24.13.0, Apple M3 Pro, shared with other
jobs), not speed claims. The archive's decision was
`nontrivial_divisibility_decidable(d - 2, n)`. A library entry's ticks
include its binary literals' elaboration, under 1,200 ticks a literal; the
`print` workloads not shown repeat their REPL rows.

| Workload | Archive, version 9 | Library, version 10 |
| --- | --- | --- |
| `evaluate euclid(3);` | `(7, (5, <path>, <fun>), tt)`; runtime, 227,045 steps; 90.0 ms | `(7, (tt, <fun>), tt)`; fallback after 3,690 steps; 26,777 ticks; 9.0 ms |
| `evaluate !!!euclid(3);` | normal form, 1,000 characters shown; 204,903 ticks; 199 ms | normal form, 1,000 characters shown; 402,932 ticks; 125 ms |
| `evaluate euclid(4);` | `(5, (3, <path>, <fun>), tt)`; runtime, 1,291,262 steps; 245 ms | `(5, (tt, <fun>), tt)`; fallback after 3,935 steps; 60,854 ticks; 12.6 ms |
| `evaluate !!!euclid(4);` | K344; 518,252 ticks; 216 ms | normal form, 1,000 characters shown; 882,773 ticks; 141 ms |
| `evaluate euclid(4) expecting (5, _);` | K344; 507,667 ticks; 196 ms | `(5, <unevaluated>)`; 57,138 ticks; 10.1 ms |
| `evaluate euclid(4) expecting !!!(5, _);` | K344; 518,252 ticks; 227 ms | normal form, 1,000 characters shown; 884,004 ticks; 146 ms |
| `evaluate euclid(3).1;` | `7`; runtime, 75,921 steps, 1 tick; 52.7 ms | `7`; fallback after 3,693 steps; 23,664 ticks; 8.0 ms |
| `evaluate euclid(3).1 expecting 7;` | `7`; 131,988 ticks; 58.2 ms | `7`; 25,089 ticks; 9.0 ms |
| `evaluate euclid(4).1;` | `5`; runtime, 430,638 steps, 1 tick; 105 ms | `5`; fallback after 3,938 steps; 56,373 ticks; 10.0 ms |
| `evaluate !!!euclid(4).1;` | K344; 507,653 ticks; 161 ms | `5`; 56,389 ticks; 8.6 ms |
| `evaluate euclid(5).1;` | `11`; runtime, 26,058,119 steps, 1 tick; 2287 ms | `11`; fallback after 4,177 steps; 159,499 ticks; 18.9 ms |
| `evaluate !!!euclid(5).1;` | K344; 686,783 ticks; 293 ms | `11`; 159,517 ticks; 14.2 ms |
| `evaluate euclid(7).1;` | — | K344; fallback after 4,655 steps; 654,611 ticks; 43.8 ms |
| `evaluate !!!euclid(7).1;` | — | K344; 654,611 ticks; 41.0 ms |
| `evaluate factorial(4);` | `24`; runtime, 3,773 steps; 15.1 ms | `24`; fallback after 3,350 steps; 13,649 ticks; 7.7 ms |
| `print(evaluate(factorial(5)));` | `120`; runtime, 10,922 steps; 19.4 ms | `120`; fallback after 3,589 steps; 16,989 ticks; 7.5 ms |
| `evaluate divides_decide(3, 6);` | `left((2, <path>))`; runtime, 4,803 steps; 14.0 ms | `left((2, <path>))`; runtime, 11,340 steps, 1,751 ticks; 9.1 ms |
| `evaluate divides_decide(4, 6);` | `right(<fun>)`; runtime, 11,203 steps; 18.3 ms | `right(<fun>)`; runtime, 9,523 steps, 1,751 ticks; 9.6 ms |
| `evaluate divides_decide(5, 121);` | `right(<fun>)`; runtime, 2,890,660 steps; 216 ms | `right(<fun>)`; runtime, 15,622 steps, 2,482 ticks; 11.3 ms |
| `evaluate !!!divides_decide(5, 121);` | K344; 753,697 ticks; 288 ms | normal form, 1,000 characters shown; 1,354,892 ticks; 148 ms |

The archive's value forms were the runtime's, with no query; the library's
fall back at a composition after 3,350–4,655 runtime steps, and the
kernel's queries compute them in 13,649–159,499 ticks. (Part one's probe
measured about 65,000 steps and a 16,140-node snapshot on the runtime from
before #324's lazy copy, SHA-256 prefix `12e703bc`; on today's, `f7c269bb`,
`node tools/runtime-repl-probe.mjs euclid-5-prime runtime` falls back after
4,177 steps, having copied 385 nodes.) Every full normal form the archive
could not reach past `euclid(3)` computes: `!!!euclid(4)` in 882,773 ticks,
`!!!euclid(5).1` in 159,517. The divisibility decisions run in the runtime
either way; the library's decides 5 against 121 in 15,622 steps where the
archive's quotient search took 2,890,660.

### Findings

**The instruction driver's alpha equality dropped a face's dimension.**
Re-deriving every definition behind the library's Euclid in instruction
mode failed at one, `bnat_peano`'s `bnat_total_same_index`: the derived
term was not alpha-equal to the checked one, though they differ only in the
names of their dimensions. Where a composition's tube sits at a face that
names a dimension its body does not mention, the driver pruned that
dimension's renaming before comparing the face, so the face compared by raw
indices (`web/cubical-syntax.mjs`'s `freeDimensionMask` left a system link's
face out when it read the link alone). The fix counts a link's face; the
same pruning had also let a face naming one binder compare equal to a face
naming another. All 359 definitions behind Euclid now derive.

Counting the face made two neighbouring faults reachable, which the review
of #334 found, and which this change also fixes. A face was renamed into
the left side's indices, so a dimension bound on one side met a free one of
the same index: `PLam(2, Comp(3, 2 = 0))` against
`PLam(1, Comp(3, 1 = 0 ∧ 2 = 0))` compared equal. And a composition's
faces were compared under its own binder, which scopes its tubes' bodies
only, so a binder that shadowed an outer one captured the face's name. A
face now reads each dimension as names are read, bound by the depth of its
binding on its side or free by its index, and the term that holds a system
compares its faces, under its own dimensions: a composition, a transport
and a Glue type or term. `tests/instruction-driver.test.mjs` checks the
cases on raw syntax, and compares the driver with the kernel's own alpha
equality on 400 generated terms whose path abstractions, transports and
compositions bind dimensions beside free ones of the same few indices, half
of them equal; without these fixes the two disagree on 26. A browser
test's stale locator is recorded in the [follow-up](pr-334-todo.md).
