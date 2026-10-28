# Runtime value forms in the REPLs

The first slice of the work plan's step 2.3 (EVAL3/EVAL4 integration),
2026-10-26, on main `e7b67376`. The value form, which `print(evaluate(e));`
and the REPL's `evaluate e;` show, is computed through
[#289](https://github.com/KanHarI/cubist-math/pull/289)'s runtime query, with
one specified fallback to the kernel's head queries. Patterns, exact
expected values and the demand marks stay on the kernel's queries. The
[shared runtime report](shared-runtime-evaluation.md) describes the query.
The second slice, 2026-10-28, on main `a30189f5`, executes the point
constructors of quotients and other higher and truncated sorts, so that
binary integers and rationals compute their value forms in the runtime
([below](#higher-sorts-point-constructors)), and since
[#324](https://github.com/KanHarI/cubist-math/pull/324) a query copies from
the kernel only what its walk reaches; the sections that follow
describe the integration as it now stands, and the first slice's
measurements are kept as they were taken.

## What computes what

`print(evaluate(e));` unmarked is the one entry point
(`valueFormOf` in `web/translator/translate.mjs`). Every REPL that runs
entries as modules reaches it: `evaluate e;` and a term alone are
`print(evaluate(e));` (`web/repl-session.mjs`), in the CLI REPL, the REPL
page, the reference pages' REPL bar and the proof workspace's console, and
so do files and the command-line checker.

1. The term is checked and its assumptions inventoried as before
   (`checker.evaluated`, `requiredAssumptions`); a term that uses one is
   refused (E324) before anything is computed.
2. `checker.runtimeQuery` (`web/cubical-elaborator.mjs`) makes a
   `RuntimeQuery` over the closed typing judgement the check derived. A
   judgement with a context gets none and is walked by the kernel's queries
   alone; a print is top-level, so none has been seen. The query reads the
   judgement, and copies each node, definition and signature from the
   kernel when its walk first demands it
   ([below](#the-query-copies-only-what-the-walk-reaches)).
3. `valueForm` (`web/translator/evaluation.mjs`), unchanged, walks the value
   form; its head query is the runtime's `observeNow`, synchronous, one
   query of the directive's fuel per head as the kernel's head query spends.
4. **The fallback, specified once:** a `RuntimeError` of kind
   `unsupported` from the snapshot or any observation abandons the
   runtime's walk, which is not shown, and the same walk is computed again
   from the start by the kernel's head queries (`demandQueries`), exactly
   once. Unsupported demand is: a path applied, a path constructor (a
   truncation's squash among them), a composition (`Comp`, `HComp`,
   `Trans`), Glue, a Glue term, `unglue`, `abort`, a constructor with
   cubical recursive positions, and η of a path abstraction.
5. A stop at the runtime's limits is reported and not retried: E487 (work,
   100M steps), E488 (allocation, 20M cells) or E489 (time, 30 s a part),
   and, when the declaration's time limit set the runtime's deadline, that
   limit's E629 as the kernel's queries report it. Any other runtime
   failure on checked input is a defect, E490.

The print directive records which computed its value form, with the
runtime's counters (`valueForm` on each entry of `prints`). A fallback
records its reason and the runtime's counters up to it.

Until the second slice, a step between 1 and 2 (`checker.runtimeRefusal`)
asked the kernel for the weak head of the term's type, within 100,000
steps, and took the fallback before any snapshot when it was a declared
type the runtime did not execute, a quotient or another higher or truncated
sort. The runtime now executes such a type's point constructors, and a
closed value of it has one at its weak head or a composition, so no type
decides the fallback: that step is removed, and each observation again
spends exactly the fuel of the head query it stands for.

Unchanged, on the kernel's queries: `evaluate !e` (the weak head as the
kernel leaves it, which needs kernel terms for its arguments), `!!`, `!!!`,
`witness`, every `evaluate … expecting …` (patterns, exact expected values
and marks), `evaluate nonempty/empty … by …`, and the proof workspace's
contextual console, whose `evaluate` shows a weak head in its context,
possibly open, by the elaborator's `nf`, and computes no value form.

## Trust

The kernel checks the evaluated term's typing judgement, its closedness and
its assumption inventory, as before. The value form shown is an
observation. Before this change it came from the kernel's weak-head query
(`cc_kernel_whnf`), which certifies nothing but is the reviewed C reducer;
now, for supported demand, it comes from the runtime, which is unreviewed
JavaScript (EVAL8's review is outstanding). No runtime result enters a
judgement, a conversion, an instruction or a directive's verdict: a print
directive has none, and the directives that do, `evaluate … expecting`, are
unchanged. The second slice widens the supported demand to the point
constructors of higher and truncated sorts and their eliminators, which
EVAL8's review covers too, and changes nothing else here. The REPL page, the language reference's printing section and
the CLI guide say that the value is computed for display and certifies
nothing. A test's `// Output:` comment compares the shown text; those in
the repository were written from the kernel's queries, so a runtime
difference fails them.

## Observation changes

Shallow observations now classify the weak head the kernel computes, which
the value form's markers need:

- η: a lambda whose body applies a function to its variable, not free in
  that function, is that function, read from syntax as `ck_whnf` reads it,
  with `ck_term_free`'s binders. Level lambdas alike.
- A partially applied constructor is a constructor with the arguments so
  far and its `arity`, as the kernel's head is an application spine; before,
  a function.
- Level functions, unapplied path abstractions and type formers (but Glue)
  are observations. A path abstraction whose body is a path application is
  unsupported, since η there reads interval formulas.
- `observeNow` drives the same machine without yielding. The asynchronous
  `observe` is unchanged. A stop carries its counters and limit.

## Differential coverage

Every value form below is compared with the one the kernel's queries alone
compute, and each is the kernel's.

- The demand marks' [constructs](../roadmaps/historical/evaluation-demand-marks/constructs.json),
  197 closed examples of every construct, each printed by the runtime and by
  the kernel's queries alone (`tests/evaluation-demand-marks.test.mjs`).
  The runtime computes 156; 37 fall back (20 compositions, 8 path
  constructors, 4 path applications, 3 η of a path abstraction, 1 Glue, 1
  `unglue`); 4 assumptions are refused. On 2026-10-26 it computed 135, and
  58 fell back, 34 of them at a higher or truncated sort, 18 of those
  decided from the value's type before any snapshot.
- Every module with a `print(evaluate(…))` among `cubist-tests/`,
  `library/` and `tests/fixtures/`, all 31 of them in `cubist-tests/`,
  with 146 prints, checked both ways in a separate run, again on
  2026-10-28: identical prints and failures; 89 value forms by the runtime
  and 2 fallbacks, at a composition and a path applied (70 and 21 on
  2026-10-26). The reference's examples and REPL transcripts state their
  outputs, written from the kernel's queries, and `npm test` checks them
  with the runtime.
- The binary integer, integer-domain and rational contracts
  (`tests/fixtures/contracts/`), each evaluated term printed in place of its
  directive, whose expected value stays on the kernel's queries
  (`tests/runtime-evaluation.test.mjs`): 41 value forms, 40 by the runtime.
  The domain's zero decision of a zero integer holds the quotient's path
  constructor and falls back.
- `tests/runtime-evaluation.test.mjs`: capture and shadowing, an unused
  path argument and an unused argument that would cost 2^24 calls, a thunk
  shared by both components of a pair, fuel equal by either computation;
  the points of a quotient, a circle, a truncation and a `trunc(1)` type,
  alone, in pairs and through a match, computed by the runtime, and their
  path constructors, paths applied and transported values, which fall back
  with their reasons; binary integer and rational arithmetic, inverses and
  decisions, components past 64 and 128 bits, and values inside pairs, sums
  and lists; the depth and budget cuts by either computation (in
  `tests/evaluation-demand-marks.test.mjs`), values past the kernel's
  syntax depth guard, a stop at the allocation cap reported as E488 and not
  retried, and the declaration's time limit.
- `tests/cubical-runtime.test.mjs`: η, partial constructors, level
  functions, types and path abstractions against the kernel's own weak
  heads; `observeNow` against `observe`, its deadline and disposal; the
  eliminators' point clauses of a quotient, a circle and a truncation
  against the kernel's normal forms; path constructors, the squash and
  cubical positions refused only when demanded, each with its reason; and
  the lazy copy's laziness, isolation and budgets
  ([below](#the-query-copies-only-what-the-walk-reaches)).
- The evaluation baseline, version 9 since 2026-10-28, records a runtime
  phase and the runtime's counters for each value form, bounded as the
  kernel's work is; a value form demands no kernel weak head, where version
  8 counted the type's, and its query copies only what its walk reaches.
- `tests/site.browser.mjs` checks the REPL page's worker: a value past the
  kernel's guard, then E488, then a further entry.

## Measurements

`node tools/runtime-repl-probe.mjs` checks each workload's setup in a fresh
REPL session and measures one `evaluate` entry, by the runtime and by the
kernel's queries alone, each sample in a process of its own. This table is
the first slice's, measured with its check of the term's type; the second
slice's binary integers and rationals are measured
[below](#measurements-of-binary-integers-and-rationals). Every row was
re-measured after the first review round, which found that a run naming
workloads measured them in one process; the table had been taken by the
run naming none, whose samples were already separate. The type check of
step 2 changed the rational's row. Three runs at `1f283e42` plus that
round's changes, Node 24.13.0, macOS arm64 (Apple M3 Pro), runtime SHA-256
prefix `12e703bcb1787daf`; every counter was the same in all three. The
machine was shared with other heavy jobs (load average 11–58 during the
runs), so the times are medians of three loaded samples, not speed claims.
Each runtime time here also includes the probe's own measurement of
retained memory, a garbage collection inside the entry, which no kernel
sample paid; since #324 the probe takes it out
([all rows re-measured](#measurements-with-lazy-copying)).
Steps are runtime transitions, ticks the kernel's query steps; the units
differ. Retained memory is measured after a collection with the query still
alive: the runtime objects reachable from its roots and the heap above the
entry's start.

| Workload | Kernel's queries | Runtime | Runtime steps | Cells allocated | Retained objects / heap | Median entry ms (runtime / kernel) | Max RSS MiB (runtime / kernel) |
| --- | --- | --- | ---: | ---: | --- | --- | --- |
| `euclid(3)` | value, 150,918 ticks, 38,736 nodes | same value | 247,542 | 145,770 | 18,962 / 1.8 MiB | 53 / 29 | 144 / 146 |
| `euclid(4).1` | K344 after 655,030 ticks | `5` | 469,175 | 267,045 | 52,493 / 4.0 MiB | 66 / 108 | 147 / 161 |
| `euclid(4)` | K344 after 652,129 ticks | `(5, (3, <path>, <fun>), tt)` | 1,385,819 | 771,843 | 104,930 / 7.6 MiB | 162 / 187 | 170 / 157 |
| `euclid(5).1` | K344 after 887,726 ticks | `11` | 28,187,952 | 15,566,553 | 3,382,822 / 229.2 MiB | 3,281 / 154 | 606 / 165 |
| `euclid(6).1` | K336 after 465,336 ticks | E488 at 20M cells | — | 20,000,000 | — / 268.0 MiB | 1,837 / 84 | 510 / 158 |
| `count_into(2 * 255, 0)` | K344 after 44,646 ticks | `510` | 67,835 | 38,927 | 10,247 / 1.3 MiB | 67 / 23 | 127 / 121 |
| `(2 * 255, 2 * 255)` | value, 16,645 ticks | same value | 63,698 | 37,172 | 9,250 / 1.6 MiB | 118 / 67 | 133 / 135 |
| `doubling(8)` | value, 8,918 ticks | same value | 15,143 | 8,572 | 1,869 / 0.1 MiB | 50 / 18 | 119 / 121 |
| BNat product of two 20-digit numerals | value, 921,830 ticks | same value | 655,044 | 369,444 | 108,197 / 8.1 MiB | 221 / 229 | 275 / 286 |
| `factorial(40)`, BNat | value, 51,104,955 ticks | fallback at a composition | 26,009 before it | 32,125 | 45 / 1.3 MiB | 7,798 / 8,457 | 303 / 302 |
| `2/3 + 1/6`, binary rationals | value, 56,153 ticks | fallback from its type, no snapshot | none | none | none | 91 / 126 | 547 / 545 |
| `duplicated-calls-24` | `tt`, 1,141 ticks | E488 at 20M cells | — | 20,000,000 | — | 1,735 / 3 | 110 / 93 |
| list parity, 200,000 cells retained | K336 after 141,381 ticks (since #321; "Invalid cubical session." before) | E488 at 20M cells | — | 20,000,000 | 2,496,166 / 475.6 MiB | 3,049 / 12 | 910 / 140 |

The runtime builds no kernel syntax: each runtime row's arena grew only by
the entry's own checking and its type's weak head (1 to 272 nodes, and
3,646 for the product's binary literals), where the kernel's walk allocates
up to 231,050 nodes before K344. In the evaluation baseline, also recorded
under load, the decision whether 5 divides 121 shows `right(<fun>)` where
the kernel's queries stop with K344.

Before the type check, the rational's fallback was mostly its snapshot:
32,015 copied nodes, reachable through 383 definitions (30,380 without
definition and constructor types), and 121,925 runtime steps for 149 forces
before the quotient's constructor (192 against 64 ms in that loaded
sample). With the type check, its type's weak head decided the fallback,
for 604 kernel ticks and 89 arena nodes more than the kernel's queries
alone spend, and no snapshot. Since the second slice the runtime computes
its value form, and since #324 it copies 1,256 of those nodes.

## Higher sorts' point constructors

The second slice of step 2.3, 2026-10-28, on main `a30189f5`.

**What the runtime executes.** The query compiles a descriptor for each
constructor of every admitted signature whose constructors it meets, where
before it did so only for untruncated types with no path constructor. A
constructor with no
dimensions in its admitted record (`kernel.signature`), whose recursive
positions have the sort itself as their cube, gets the arity descriptors
ordinary data has: the point constructors of quotients (`class`), of other
higher inductive types (a circle's `base`) and of truncations (`point`, a
`trunc(1)` type's `gpoint`), and so of binary integers and rationals, which
are quotients of differences of binary naturals and of fractions over them.
Elimination is the same rule as for ordinary data: an eliminator of any
admitted signature is a function value, and applied to a fully applied
point constructor it applies that constructor's clause to its arguments and
hypotheses. That is the iota of `ck_eliminate` (`kernel/src/eliminators.c`)
for a constructor with no dimensions, applied at no interval point. An
eliminator's path and squash clauses are never demanded.

**What stays unsupported, and where it is met.** Each is refused where the
walk meets it, and the fallback computes the whole value form again by the
kernel's head queries.

- A path constructor, any constructor with dimensions, the generated squash
  of a truncation among them (it has the truncation's level plus two):
  refused at the constructor, before its arguments. A closed value of a path
  type can have one at its weak head (`loop`, `relate(1, 3, tt)`,
  `squash(point(1), point(2))`), which the kernel's walk shows with its
  fields.
- A point constructor with a recursive position whose cube is a path type:
  refused, as before.
- A path applied. Outside a composition, the kernel's weak-head computation
  of a closed term applies a path constructor only at an endpoint, which it
  takes to its boundary before an eliminator sees it.
- A composition (`Comp`, `HComp`, `Trans`). A closed value of a higher sort
  whose weak head is no point constructor is a formal composition; an
  eliminator applied to one takes the kernel's composition rule
  (`ck_eliminate_hcomp`), the eliminator applied to the composition's tubes
  under its binder, where a path clause can be selected.

The first slice's check of the term's type is removed
([What computes what](#what-computes-what)): no type decides the fallback.
The [differential coverage](#differential-coverage) above includes this
slice's: of the demand marks' 34 constructs refused at a higher or
truncated sort before, the runtime computes 21, such as a circle's base, a
quotient's class and a match on them, and meets a path constructor in 8, a
path applied in 2 and a transport's composition in 3.

### The query copies only what the walk reaches

Measured first with #289's eager copy, at `7cab2503`, a binary rational's
value form took the runtime about three times as long as the kernel's
queries, a time that also held the probe's own collection
([below](#measurements-with-lazy-copying)): `2/3 + 1/6` in 127 against 38
ms, 146,459 steps and 174,773 cells.
A query over the same term made outside the REPL spent 120,950 of those
steps and 160,516 of those cells copying the closure of its judgement,
32,015 nodes through 383 definitions, the laws' proofs of the field
`binary_rationals` among them (as `bnat_add_assoc`), which the walk never
reaches. Since #324 the query copies only what the walk reaches:

- **What is read, and when.** Making the query reads only the judgement.
  The walk reads a node when it first forces syntax there, a definition's
  value when it first forces a reference to it, and a declared type's
  descriptors when it first meets one of its constructors; each read is
  copied into the query, whose cells hold no kernel object. A definition
  the walk never reaches is never copied. The runtime's counters say what
  was copied (`snapshotNodes`, `snapshotDefinitions`): `2/3 + 1/6` copies
  1,256 nodes through 50 definitions.
- **Isolation.** The query reads the judgement as it was checked. A kernel
  handle keeps its node, definition or signature while the session is
  open, except the handles made since a declaration's checkpoint, which its
  commit compacts and its rollback drops (`kernel/src/checkpoint.c`). The
  kernel's wrapper counts those ends and knows whether a checkpoint is open
  (`handleToken` and `handlesHeld` in `web/cubical-kernel.mjs`; the
  declaration's transaction opens it). A query made with no checkpoint open
  reads correctly until the session is disposed; one made inside a
  checkpoint, as a value form's is, until that checkpoint ends. A read
  after either fails as `expired` instead of reading another state, and
  what the query copied and computed before stays observable. A value form
  makes and disposes of its query inside one check, before its
  declaration's checkpoint ends, so it never meets an expiry: one there
  would be a runtime defect, E490, not a fallback.
- **Budgets.** Each read is work, and each copied node cells, of the
  observation that demands it, counted as the eager copy's were in the
  query's construction: the work, cell and time limits, cancellation and
  the asynchronous observation's slices apply to copying as to forcing.
- **Tests.** In `tests/cubical-runtime.test.mjs`: a pair copies its
  reference, the identity application that ascribes its type and the pair
  node, but neither component's definition until that component is
  demanded; a query made outside a checkpoint reads correctly after later
  declarations, accepted and refused; one made inside a checkpoint expires
  at its commit and at its rollback, and every query at the session's
  disposal, with what it read still observable; a cell or work limit stops
  a query in the middle of a read. In `tests/runtime-evaluation.test.mjs`,
  the unused argument's definitions are never copied, and `2/3 + 1/6`
  copies under a tenth of the closure's 32,015 nodes. The differential
  coverage is unchanged and passes.

### Measurements with lazy copying

Every workload of `node tools/runtime-repl-probe.mjs`, the first slice's and
the binary ones, each sample in a process of its own, three runs at
`0855d52d` with no modification, Node 24.13.0, macOS arm64 (Apple M3 Pro),
runtime SHA-256 prefix `ef8a2c2dd9086ee8`; every counter was the same in
all three. The machine was shared with other heavy jobs (load average 3 to
29 during the runs), so the times are medians of three loaded samples, not
speed claims. The probe now takes its own measurement of retained memory,
a collection and a walk inside the entry, out of the entry's time. The
kernel's walk is its ticks less the entry's own checking, which reads
literals by evaluation, measured on the runtime's path; on a fallback
the runtime's path pays the kernel's walk too.

| Workload | Kernel's queries | Runtime | Runtime steps | Cells allocated | Copied nodes / definitions | Retained objects / heap | Median entry ms (runtime / kernel) | Max RSS MiB (runtime / kernel) |
| --- | --- | --- | ---: | ---: | --- | --- | --- | --- |
| `euclid(3)` | value, 150,918 ticks | same value | 237,172 | 132,529 | 289 / 10 | 18,962 / 1.1 MiB | 16 / 13 | 143 / 147 |
| `euclid(4).1` | K344 after 655,030 ticks | `5` | 458,724 | 253,593 | 245 / 9 | 52,493 / 3.3 MiB | 17 / 64 | 146 / 161 |
| `euclid(4)` | K344 after 652,129 ticks | `(5, (3, <path>, <fun>), tt)` | 1,375,459 | 758,632 | 296 / 10 | 104,930 / 6.9 MiB | 74 / 53 | 174 / 161 |
| `euclid(5).1` | K344 after 887,726 ticks | `11` | 28,177,499 | 15,553,101 | 246 / 9 | 3,382,822 / 228.5 MiB | 617 / 87 | 608 / 166 |
| `euclid(6).1` | K336 after 465,336 ticks | E488 at 20M cells | — | 20,000,000 | 206 | — / 269.2 MiB | 839 / 52 | 566 / 161 |
| `count_into(2 * 255, 0)` | K344 after 44,646 ticks | `510` | 67,172 | 38,837 | 317 / 3 | 10,247 / 1.5 MiB | 27 / 8 | 127 / 120 |
| `(2 * 255, 2 * 255)` | value, 16,645 ticks | same value | 63,080 | 37,107 | 297 / 2 | 9,250 / 1.6 MiB | 37 / 33 | 134 / 135 |
| `doubling(8)` | value, 8,918 ticks | same value | 15,038 | 8,517 | 43 / 2 | 1,869 / 0.1 MiB | 12 / 10 | 118 / 119 |
| BNat product of two 20-digit numerals | value, 921,830 ticks, walk 909,984 | same value | 652,229 | 366,493 | 392 / 11 | 108,197 / 7.8 MiB | 41 / 68 | 277 / 286 |
| `factorial(40)`, BNat | value, 51,104,955 ticks | fallback at a composition | 3,744 before it | 3,464 | 330 / 15 | 45 / none measurable | 1,959 / 1,823 | 307 / 306 |
| `duplicated-calls-24` | `tt`, 1,141 ticks | E488 at 20M cells | — | 20,000,000 | 161 | — / 0.9 MiB | 574 / 2 | 111 / 93 |
| list parity, 200,000 cells retained | K336 after 141,381 ticks | E488 at 20M cells | — | 20,000,000 | 188 | 2,496,181 / 475.7 MiB | 971 / 12 | 949 / 144 |
| `2/3 + 1/6` | value, 56,153 ticks, walk 32,755 | same value | 28,170 | 20,643 | 1,256 / 50 | 1,881 / 0.4 MiB | 36 / 32 | 623 / 627 |
| `bq_inv(-(2^128 - 1)/(2^64 - 1))`, as decimal literals | value, 644,085 ticks, walk 598,470 | same value | 1,202,115 | 676,882 | 1,388 / 54 | 172,595 / 12.9 MiB | 88 / 88 | 621 / 623 |
| `bq_decide(1/2, 2/3)` | `right(<fun>)`, 49,378 ticks, walk 26,353 | same value | 23,890 | 18,046 | 1,183 / 48 | 1,507 / 0.2 MiB | 31 / 28 | 641 / 627 |
| `bq_decide(1/2 + 1/3, 5/6)` | `left(relate(…))`, 76,259 ticks | fallback at the path constructor | 44,381 before it | 30,760 | 1,539 / 59 | 2,730 / 0.4 MiB | 41 / 51 | 621 / 621 |
| `(2^128 - 1) * (2^128 - 1)`, binary integers | value, 6,982,169 ticks, walk 6,962,688 | same value | 4,329,313 | 2,425,751 | 764 / 27 | 737,577 / 53.1 MiB | 264 / 694 | 584 / 580 |
| `bint_decide(2^128 - 1, -1)` | `right(<fun>)`, 42,802 ticks, walk 22,619 | same value | 49,942 | 31,380 | 717 / 29 | 4,252 / 0.6 MiB | 102 / 110 | 565 / 540 |

Against the kernel's walk, the runtime's steps are fewer for `2/3 + 1/6`
(28,170 against 32,755 ticks), the decision of distinct rationals (23,890
against 26,353) and both binary products, where the eager copy had made
`2/3 + 1/6` cost 146,459 steps. Three binary rows are still slower in
steps, said plainly:

- the wide inverse: 1,202,115 steps against the walk's 598,470 ticks, both
  in a median of 88 ms;
- `bint_decide(2^128 - 1, -1)`: 49,942 steps against 22,619 ticks, in 102
  against 110 ms;
- the decision of equal rationals falls back at the path constructor: its
  44,381 runtime steps come on top of the kernel's walk.

The units differ: a runtime step is a transition of the machine or an
allocation, a tick a step of the kernel's reducer, so a row can be slower
in steps and not in time, as both of the first two are here. In every
binary row the copy is now at most 1,539 nodes and 59 definitions.

**A decision that finds two values equal falls back.** Its `left` holds the
quotient's path constructor applied to its data, `relate(…)`, which this
slice refuses as specified; the entry then pays for both walks, 44,381
runtime steps before the kernel's. Showing that constructor needs
no dimension or composition: the kernel's walk shows it as a constructor
with its fields. Whether the runtime may show it so is recorded in the
runtime roadmap for the user's decision; it is not done.

## Findings

**Sharing.** The kernel's weak-head cache is keyed by interned syntax, so
in a closed computation a term that occurs twice is computed once wherever
it occurs. The runtime shares a thunk by occurrence: a function's argument,
a definition and a structural recursion's hypothesis are shared, but a call
written twice, `both(g(u), g(u))`, is two thunks. `duplicated-calls-24`
nests 24 such definitions: the kernel's queries answer in 1,141 ticks and
the runtime stops at its allocation cap. A per-environment memo of delayed
syntax was tried and withdrawn: on `euclid(5).1` it left the forces
unchanged (3,967,646 against 3,968,762) and raised the retained objects from
3,382,827 to 8,450,145 and the heap after measurement from 456 to 1,406 MiB.

**Memory.** The 20M-cell cap bounds the runtime's memory; it is not
calibrated in bytes. At the cap the probe measured a process peak of 510 MiB
(`euclid(6).1`) and 910 MiB with every cell retained (list parity), against
about 140–165 MiB for the kernel's walk of the same setups. Closed-environment
pruning and a byte calibration remain EVAL4 work.

**Responsiveness.** The runtime runs inside the check, synchronously, as
the kernel's queries do: the browser worker answers no message during an
entry either way, and the page's watchdog still bounds a REPL entry. The
runtime adds its own bounds: 100M steps, 20M cells and a time limit (the
declaration's, else 30 seconds a part). A responsive snapshot copy matters
for the asynchronous `observe` only. Since #324 making a query copies
nothing: each read happens inside an observation, counted in its work and
checked between the slices at which `observe` yields, and at most 1,539
nodes are copied in the workloads measured. What still runs within one
transition is the η check's walk of a function's syntax and a declared
type's descriptors.

**Fixed on main by #321.** The list-parity setup's evaluation by the
kernel's queries reported "Invalid cubical session." on main `e7b67376` too:
nested eliminators overflowed the 2 MiB WASM stack, placed after the static
data, and overwrote the bridge's session table. Since #321 the stack comes
first with 8 MiB, and the kernel's queries stop at the recursion guard, K336,
after 141,381 ticks (re-measured on this branch merged with main `b7482e84`).

## Decisions of 2026-10-26

The two questions this slice left open were decided the same day:

- **Constructor patterns stay on the kernel's queries** until typed
  readback and the applicable EVAL8 review (the work plan's step 2.4). A
  pattern's verdict is a check: an `evaluate … expecting` directive passes
  or fails, and contracts gate on it, so the runtime's observations, which
  are not kernel evidence, may not decide it. Patterns' expression leaves
  also compare a part's normal form with the leaf's by conversion, and a
  runtime part has no kernel term until typed readback. The options
  considered were a runtime verdict for the pattern's skeleton, in files
  and the REPL or in the REPL only as a labelled observation, and runtime
  verdicts confirmed by the kernel's queries, which save nothing.
- **A stop at the runtime's limits stays reported, not retried**, so
  `duplicated-calls-24` shows E488 where the kernel's queries show `tt`;
  `evaluate !!e` still asks the kernel. Sharing a call written twice is
  EVAL4 work, by a memo whose retention is measured. The option considered
  was a second fallback on a stop, which would give today's outcome at up
  to the runtime's limits in wasted work and would not report the stop.
