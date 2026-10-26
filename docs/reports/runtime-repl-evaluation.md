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
2. `checker.runtimeQuery` (`web/cubical-elaborator.mjs`) makes a
   `RuntimeQuery` over the closed typing judgement the check derived. A
   judgement with a context gets none and is walked by the kernel's queries
   alone; a print is top-level, so none has been seen. The query copies the
   reachable syntax, definitions and admitted signatures.
3. `valueForm` (`web/translator/evaluation.mjs`), unchanged, walks the value
   form; its head query is the runtime's `observeNow`, synchronous, one
   query of the directive's fuel per head as the kernel's head query spends.
4. **The fallback, specified once:** a `RuntimeError` of kind `unsupported`
   from the snapshot or any observation abandons the runtime's walk, which
   is not shown, and the same walk is computed again from the start by the
   kernel's head queries (`demandQueries`), exactly once. Unsupported demand
   is: a path applied, a composition (`Comp`, `HComp`, `Trans`), Glue, a
   Glue term, `unglue`, `abort`, a higher or truncated sort, a constructor
   with cubical recursive positions, and η of a path abstraction.
5. A stop at the runtime's limits is reported and not retried: E487 (work,
   100M steps), E488 (allocation, 20M cells) or E489 (time, 30 s a part),
   and, when the declaration's time limit set the runtime's deadline, that
   limit's E629 as the kernel's queries report it. Any other runtime
   failure on checked input is a defect, E490.

The print directive records which computed its value form, with the
runtime's counters (`valueForm` on each entry of `prints`).

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
  (29 higher or truncated sorts, 20 compositions, 4 path applications, 3 η
  of a path abstraction, 1 Glue, 1 `unglue`); 4 assumptions are refused.
- Every module with a `print(evaluate(…))` among `cubist-tests/`,
  `library/` and `tests/fixtures/`, all 31 of them in `cubist-tests/`,
  with 146 prints, checked both ways in a separate run: identical prints and
  failures; 70 value forms by the runtime, 21 fallbacks. The reference's
  examples and REPL transcripts state their outputs, written from the
  kernel's queries, and `npm test` checks them with the runtime.
- `tests/runtime-evaluation.test.mjs`: capture and shadowing, an unused
  path argument and an unused argument that would cost 2^24 calls, a thunk
  shared by both components of a pair, a fallback with its reason, equal
  fuel by either computation, the depth and budget cuts by either
  computation (in `tests/evaluation-demand-marks.test.mjs`), values past
  the kernel's syntax depth guard, a stop at the allocation cap reported as
  E488 and not retried, and the declaration's time limit.
- `tests/cubical-runtime.test.mjs`: η, partial constructors, level
  functions, types and path abstractions against the kernel's own weak
  heads; `observeNow` against `observe`, its deadline and disposal.
- The evaluation baseline, version 8, records a runtime phase and the
  runtime's counters for each value form, bounded as the kernel's work is.
- `tests/site.browser.mjs` checks the REPL page's worker: a value past the
  kernel's guard, then E488, then a further entry.

## Measurements

`node tools/runtime-repl-probe.mjs` checks each workload's setup in a fresh
REPL session and measures one `evaluate` entry, by the runtime and by the
kernel's queries alone, in fresh processes. Three runs at `38d8e585` plus
the probe's own uncommitted additions, Node 24.13.0, macOS arm64 (Apple M3
Pro), runtime SHA-256 prefix `421deb2f985f38ce`; every counter was the
same in all three. The machine was shared with other heavy jobs (load
average 20–35), so the times are medians of three loaded samples, not
speed claims. Steps are runtime transitions, ticks the kernel's query
steps; the units differ. Retained memory is measured after a collection
with the query still alive: the runtime objects reachable from its roots
and the heap above the entry's start.

| Workload | Kernel's queries | Runtime | Runtime steps | Cells allocated | Retained objects / heap | Median entry ms (runtime / kernel) | Max RSS MiB (runtime / kernel) |
| --- | --- | --- | ---: | ---: | --- | --- | --- |
| `euclid(3)` | value, 150,918 ticks, 38,736 nodes | same value | 247,542 | 145,770 | 18,962 / 1.8 MiB | 64 / 21 | 142 / 142 |
| `euclid(4).1` | K344 after 655,030 ticks | `5` | 469,175 | 267,045 | 52,493 / 4.0 MiB | 65 / 102 | 149 / 160 |
| `euclid(4)` | K344 after 652,129 ticks | `(5, (3, <path>, <fun>), tt)` | 1,385,819 | 771,843 | 104,930 / 7.6 MiB | 128 / 125 | 175 / 160 |
| `euclid(5).1` | K344 after 887,726 ticks | `11` | 28,187,952 | 15,566,553 | 3,382,822 / 229.2 MiB | 3,144 / 198 | 621 / 165 |
| `euclid(6).1` | K336 after 465,336 ticks | E488 at 20M cells | — | 20,000,000 | — / 269.6 MiB | 1,566 / 97 | 511 / 161 |
| `count_into(2 * 255, 0)` | K344 after 44,646 ticks | `510` | 67,835 | 38,927 | 10,247 / 1.3 MiB | 77 / 16 | 127 / 122 |
| `(2 * 255, 2 * 255)` | value, 16,645 ticks | same value | 63,698 | 37,172 | 9,250 / 1.6 MiB | 68 / 56 | 133 / 133 |
| `doubling(8)` | value, 8,918 ticks | same value | 15,143 | 8,572 | 1,869 / 0 MiB | 26 / 18 | 120 / 121 |
| BNat product of two 20-digit numerals | value, 921,830 ticks | same value | 655,044 | 369,444 | 108,197 / 8.1 MiB | 129 / 128 | 276 / 285 |
| `factorial(40)`, BNat | value, 51,104,955 ticks | fallback at a composition | 26,009 before it | 32,125 | 45 / 1.3 MiB | 4,129 / 3,998 | 305 / 305 |
| `2/3 + 1/6`, binary rationals | value, 56,153 ticks | fallback at the quotient | 121,925 before it | 161,110 | 97 / 7.8 MiB | 192 / 64 | 595 / 617 |
| `duplicated-calls-24` | `tt`, 1,141 ticks | E488 at 20M cells | — | 20,000,000 | — | 732 / 4 | 109 / 94 |
| list parity, 200,000 cells retained | "Invalid cubical session." | E488 at 20M cells | — | 20,000,000 | 2,496,166 / 475.6 MiB | 2,962 / 14 | 904 / 141 |

The runtime builds no kernel syntax: each runtime row's arena grew only by
the entry's own checking (14–272 nodes), where the kernel's walk allocates
up to 231,050 nodes before K344. In the evaluation baseline, also recorded
under load, the decision whether 5 divides 121 shows `right(<fun>)` where
the kernel's queries stop with K344.

The rational's fallback is mostly its snapshot: 32,015 copied nodes,
reachable through 383 definitions (30,380 without definition and
constructor types), for 149 forces before the quotient's constructor.

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
calibrated in bytes. At the cap the probe measured a process peak of 511 MiB
(`euclid(6).1`) and 904 MiB with every cell retained (list parity), against
about 140–165 MiB for the kernel's walk of the same setups. Closed-environment
pruning and a byte calibration remain EVAL4 work.

**Responsiveness.** The runtime runs inside the check, synchronously, as
the kernel's queries do: the browser worker answers no message during an
entry either way, and the page's watchdog still bounds a REPL entry. The
runtime adds its own bounds: 100M steps, 20M cells and a time limit (the
declaration's, else 30 seconds a part). A responsive snapshot copy matters
for the asynchronous `observe` only; the snapshot here is at most 32,015
nodes in the workloads measured.

**Pre-existing, on main.** The list-parity setup's evaluation by the
kernel's queries reports "Invalid cubical session." on main `e7b67376` too
(the error message of a freed kernel session), with or without this
change; it is not investigated here.

## Decisions needed

**Constructor patterns.** The work plan has the REPLs compute constructor
patterns through the runtime as well. A pattern's verdict is a check: an
`evaluate … expecting` directive passes or fails, and contracts gate on it.
The runtime's observations are not kernel evidence, so a runtime verdict
would let unreviewed code pass a check the kernel's queries would decide.
Patterns' expression leaves also compare a part's normal form with the
leaf's by conversion, and a runtime part has no kernel term until typed
readback (step 2.4). Options:

1. Keep patterns on the kernel's queries until typed readback and the
   applicable EVAL8 review (step 2.4), where a read-back part can be checked
   by the kernel. Nothing changes for directives. **Recommended**: it
   preserves every existing check, and the value form already shows what
   the runtime can compute.
2. Let the runtime decide a pattern's skeleton (holes, `!_`, pairs,
   injections and constructors), falling back whole on any leaf that needs a
   kernel term. Directives pass on runtime verdicts; this needs the
   decision that an unreviewed observation may pass a directive.
3. As 2, but in the REPL only, with the verdict shown as a runtime
   observation and files kept on the kernel's queries: two meanings for one
   directive.
4. Runtime verdicts confirmed by the kernel's queries: no saving, and no
   verdict where the kernel's queries stop.

**Stops at the runtime's limits.** A stop is reported, as the slice's
contract states, so `duplicated-calls-24` shows E488 where the kernel's
queries show `tt`. Options:

1. Keep reporting the stop (this change); track sharing of repeated calls,
   by a memo whose retention is measured, as EVAL4 work. **Recommended**:
   the stop is controlled and bounded, `evaluate !!e` still asks the kernel,
   and the fallback stays a single, stated rule.
2. Also fall back to the kernel's queries on a stop: every outcome is then
   today's, at up to the runtime's limits in wasted work (about 0.7–3 s and
   up to 0.9 GiB in the rows above), and the runtime's stop is not reported.
