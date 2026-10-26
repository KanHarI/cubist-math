# Runtime value forms in the REPLs

The first slice of the work plan's step 2.3 (EVAL3/EVAL4 integration),
2026-10-26, on main `e7b67376`. The value form, which `print(evaluate(e));`
and the REPL's `evaluate e;` show, is computed through
[#289](https://github.com/KanHarI/cubist-math/pull/289)'s runtime query, with
one specified fallback to the kernel's head queries. Patterns, exact
expected values and the demand marks stay on the kernel's queries. The
[shared runtime report](shared-runtime-evaluation.md) describes the query.

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
2. `checker.runtimeRefusal` asks the kernel for the weak head of the term's
   type, within 100,000 steps, for one query of the directive's fuel. If it
   is a declared type the runtime does not execute (`ordinarySignature` in
   `web/cubical-runtime.mjs`: a quotient or another higher or truncated
   sort), the value's weak head is a constructor of that type or a
   composition, both of which the runtime refuses: the fallback of step 5
   is taken here, before any snapshot, with the reason the runtime would
   give. A type whose head does not come within the budget decides nothing.
3. `checker.runtimeQuery` (`web/cubical-elaborator.mjs`) makes a
   `RuntimeQuery` over the closed typing judgement the check derived. A
   judgement with a context gets none and is walked by the kernel's queries
   alone; a print is top-level, so none has been seen. The query copies the
   reachable syntax, definitions and admitted signatures.
4. `valueForm` (`web/translator/evaluation.mjs`), unchanged, walks the value
   form; its head query is the runtime's `observeNow`, synchronous, one
   query of the directive's fuel per head as the kernel's head query spends.
5. **The fallback, specified once:** a `RuntimeError` of kind
   `unsupported` from step 2, the snapshot or any observation abandons the
   runtime's walk, which is not shown, and the same walk is computed again
   from the start by the kernel's head queries (`demandQueries`), exactly
   once. Unsupported demand is: a path applied, a composition (`Comp`,
   `HComp`, `Trans`), Glue, a Glue term, `unglue`, `abort`, a higher or
   truncated sort, a constructor with cubical recursive positions, and η of
   a path abstraction.
6. A stop at the runtime's limits is reported and not retried: E487 (work,
   100M steps), E488 (allocation, 20M cells) or E489 (time, 30 s a part),
   and, when the declaration's time limit set the runtime's deadline, that
   limit's E629 as the kernel's queries report it. Any other runtime
   failure on checked input is a defect, E490.

The print directive records which computed its value form, with the
runtime's counters (`valueForm` on each entry of `prints`). A fallback
records its reason, and the runtime's counters only when a query was made:
a fallback decided in step 2 has none.

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
unchanged. The REPL page, the language reference's printing section and
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

- The demand marks' [constructs](../roadmaps/historical/evaluation-demand-marks/constructs.json),
  197 closed examples of every construct, each printed by the runtime and by
  the kernel's queries alone (`tests/evaluation-demand-marks.test.mjs`):
  every value form is the kernel's. The runtime computes 135; 58 fall back
  (34 higher or truncated sorts, 18 of them decided from the value's type
  before any snapshot, 17 compositions, 2 path applications, 3 η of a path
  abstraction, 1 Glue, 1 `unglue`); 4 assumptions are refused.
- Every module with a `print(evaluate(…))` among `cubist-tests/`,
  `library/` and `tests/fixtures/`, all 31 of them in `cubist-tests/`,
  with 146 prints, checked both ways in a separate run: identical prints and
  failures; 70 value forms by the runtime, 21 fallbacks. The reference's
  examples and REPL transcripts state their outputs, written from the
  kernel's queries, and `npm test` checks them with the runtime.
- `tests/runtime-evaluation.test.mjs`: capture and shadowing, an unused
  path argument and an unused argument that would cost 2^24 calls, a thunk
  shared by both components of a pair, a fallback with its reason, fuel
  equal by either computation but for the type's weak head, values of a
  quotient, a higher inductive type and a binary rational decided from
  their types with no snapshot while a pair containing a quotient and
  ordinary data still ask the runtime, the depth and budget cuts by either
  computation (in `tests/evaluation-demand-marks.test.mjs`), values past
  the kernel's syntax depth guard, a stop at the allocation cap reported as
  E488 and not retried, and the declaration's time limit.
- `tests/cubical-runtime.test.mjs`: η, partial constructors, level
  functions, types and path abstractions against the kernel's own weak
  heads; `observeNow` against `observe`, its deadline and disposal.
- The evaluation baseline, version 8, records a runtime phase and the
  runtime's counters for each value form, bounded as the kernel's work is;
  the type's weak head that decides whether to ask the runtime is a demand.
- `tests/site.browser.mjs` checks the REPL page's worker: a value past the
  kernel's guard, then E488, then a further entry.

## Measurements

`node tools/runtime-repl-probe.mjs` checks each workload's setup in a fresh
REPL session and measures one `evaluate` entry, by the runtime and by the
kernel's queries alone, each sample in a process of its own. Every row was
re-measured after the first review round, which found that a run naming
workloads measured them in one process; the table had been taken by the
run naming none, whose samples were already separate. The type check of
step 2 changed the rational's row. Three runs at `1f283e42` plus that
round's changes, Node 24.13.0, macOS arm64 (Apple M3 Pro), runtime SHA-256
prefix `12e703bcb1787daf`; every counter was the same in all three. The
machine was shared with other heavy jobs (load average 11–58 during the
runs), so the times are medians of three loaded samples, not speed claims.
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
| list parity, 200,000 cells retained | "Invalid cubical session." | E488 at 20M cells | — | 20,000,000 | 2,496,166 / 475.6 MiB | 3,049 / 12 | 910 / 140 |

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
sample). Now its type's weak head decides the fallback, for 604 kernel
ticks and 89 arena nodes more than the kernel's queries alone spend, and no
snapshot.

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
for the asynchronous `observe` only; the snapshot here is at most 6,043
nodes in the workloads measured (`factorial(40)`), and a binary rational
takes none.

**Pre-existing, on main.** The list-parity setup's evaluation by the
kernel's queries reports "Invalid cubical session." on main `e7b67376` too
(the error message of a freed kernel session), with or without this
change; it is not investigated here.

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
