# Typed readback: the EVAL8 record (W4)

W4 of [typed readback](../roadmaps/runtime/typed-readback.md#8-work-items),
written on 2026-11-01 on main `398e89ba` (#344 merged). It goes through
[section 6](../roadmaps/runtime/typed-readback.md#6-eval8-interaction)'s
list for what is on main, and records for each item what was checked, how,
at which revision, the result and any finding. The applicable suites of the
W4 row were run at the same revision. Review rounds follow the roadmap's
rule ([below](#review-rounds)).

## Scope

- **W1, readback by value and by origin with its oracle** (#337), is on
  main and internal: `RuntimeQuery.readback` (`web/cubical-runtime.mjs`)
  is called only by tests and `tools/runtime-repl-probe.mjs`. No checker,
  REPL, page or verdict reads a value back (D1). This record reviews its
  readback fragment.
- **The fallback boundary on main is the whole-walk restart**
  (`valueFormOf` in `web/translator/translate.mjs`), which W1 left as it
  was. This record reviews it.
- **W2, the per-node fallback, is held** (#342, decided on 2026-10-30) on
  branch `typed-readback-w2`, so its boundary is not reviewed here: section
  4 has W4 close each work item, and W2's boundary is reviewed when W2
  lands, by that PR's W4 pass. The held branch waits for "a design faster
  end to end", so the boundary it would integrate may change, and a review
  of it now would review code that is not in production.
- **W3 is not taken:** M3, in #343 (a draft, open on 2026-11-01), found no
  gain for printed `!!` through the runtime. There is no W3 code.

## Summary

| Section 6 item | Result | Evidence |
| --- | --- | --- |
| No kernel reducer replaced, no instruction added or changed | Holds | W1 changed no file under `kernel/`, `wasm/` or the kernel's JavaScript bridge; no commit since touches `kernel/` or `wasm/` ([1](#1-the-kernel-is-unchanged)) |
| The named rules, compared | Each runtime and readback step agrees with the kernel rule it imitates ([2](#2-the-rules-the-correspondence-imitates)) | Source, the oracle |
| Claims 1–6 of 3.6 | Hold on everything measured; claim 4, a target, is met wherever decided | The oracle over 293 value forms, W1's tests, a closedness census of 7,994 readbacks, probes ([3](#3-claims-1-to-6)) |
| Lazy annotations | `R` forces nothing and demands no definition | Source; a test ([4](#4-lazy-annotations)) |
| The fallback boundary | The restart on main computes every value form as the kernel's queries do; W2's is reviewed when W2 lands | Source, tests, CLI and browser ([5](#5-the-fallback-boundary)) |
| The generation | Checked at entry, before each write and before a handle is returned | Source, W1's tests, the bridge's test ([6](#6-the-generation)) |
| Budgets and cancellation in the middle of a readback | Stop as specified, and the query reads back correctly after | Tests (F2, covered) ([7](#7-budgets-and-cancellation-in-the-middle-of-a-readback)) |
| A malformed handle | Refused | A test ([8](#8-a-malformed-handle)) |
| Query-before-instruction isolation | Holds | A test in the manner of `kernel/tests/test_isolation.c` (F1, covered) ([9](#9-query-before-instruction-isolation)) |
| Syntax equality and conversion stay apart | Holds | Source of the tests and the oracle ([10](#10-syntax-equality-and-conversion)) |

No defect was found in W1's readback or in the restart. The findings are
two gaps in the repository's tests (F1, F2), which this branch closes with
tests made from the record's probes, and one broken browser test on main,
unrelated to readback, whose harness this branch fixes (F3).

## Revision, environment and suites

Every run was made on `398e89ba`, after `rm -f web/dist/cubical.mjs
web/dist/cubical.wasm && make wasm` and `rm -rf kernel/build`, with
`node tools/build-stamp.mjs check` passing, one heavy job at a time, on
Node 24.13.0, macOS 26.5.1 arm64 (Apple M3 Pro, 36 GiB), emcc 6.0.9, Apple
clang 17.0.0, on AC power under `caffeinate -dimsu`.

| Suite | Command | Outcome |
| --- | --- | --- |
| C kernel | `make -C kernel test` | passed: 16 test programs, `instruction isolation: ok`, `bridge handle generations: ok` |
| C sanitizer | `make sanitize SANITIZERS=undefined` (ASan runs in CI) | passed: the same 16, no UBSan report |
| C lint | `make lint` | passed: 44 of 44 files |
| JavaScript | `npm test`, through the full-suite lock | passed: 2,138 tests, 2,138 pass, in 478 s; W1's 13 readback tests and the oracle's three surfaces among them. Again at `ab9df858`, with the tests that close F1 and F2: 2,142 tests, 2,142 pass, in 508 s |
| Canonicity fixtures | `tests/hott-automation.test.mjs` (in `npm test`); `node cli/repl.mjs check docs/examples/hott-automation/canonicity.cubist` | passed; 17 declarations in 69,207 kernel steps, its evaluations `6`, `left(2)` and `tt` |
| CLI evaluation | `tests/cli.test.mjs` (in `npm test`); the entries of [5](#5-the-fallback-boundary) | passed; each entry as expected |
| Browser evaluation | `npm run test:browser`, `test:browser:contextual`, `test:browser:cubical`, `test:browser:statement`, `test:browser:proof-navigation`, `test:browser:landing`; `node tools/build-site.mjs && npm run test:site`; the value-form pages, by the per-page recipe | passed, `test:browser:cubical` after its harness fix (F3); the site test's 28 PASS lines, "REPL page: the runtime's value forms and its limits" among them; 234 examples on 9 reference pages, 33 with printed or evaluated values, each the Node checker's |
| Archive checking | `node tools/audit-cubical.mjs --all` | passed: 3,527 declarations checked in 353 modules, none failed, in 33 s |
| Definition re-derivation | `npm run test:coverage` | passed: the archive checked with the driver's guide, 3,527 of 3,527 declarations in 348 modules, 0 gaps; 3,632 of 3,632 definitions derive in instruction mode (100.0%) |
| Isolation | `kernel/tests/test_isolation.c` (in the kernel and sanitizer runs); the test of [9](#9-query-before-instruction-isolation) | passed |

The record's checks began as probes, a scratch test file, 7 tests, all
passing. Their isolation, partway, handle and forcing cases became four
tests in `tests/runtime-readback.test.mjs`, and their K344 case two
checks in W1's K344 test there (`ab9df858`, [below](#findings)); `npm
test` passed again with them.
The rest stay scratch, and their cases are given where they are used: the
large readbacks' closedness and the tower of claim 5, the closedness
census, which preloads a module that checks every term `readback` returns,
by `NODE_OPTIONS=--import=…`, into the test files that read back, and the
per-page browser recipe.

## 1. The kernel is unchanged

Readback builds syntax with `cc_kernel_term`, reads nodes, compares the
projected terms of a pair of two projections with `cc_kernel_alpha_equal`,
and asks `cc_kernel_whnf` for a level's universe; it uses no instruction.
W1's merge (`26131abd`) changed 11 files: the runtime, its tests, the
probe and four documents.
`git diff 26131abd^1 26131abd -- kernel wasm web/cubical-kernel.mjs
web/cubical-instructions.mjs web/cubical-instruction-driver.mjs` is empty,
and `git log 26131abd..398e89ba -- kernel wasm` lists nothing. The one
widening W1 made is JavaScript's, decided as D3: `readback` adds its term
to `kernel.derivedHandles`, the guard of `CubicalKernel.normalize` and
`normalizeFolded`, which no instruction reads.

## 2. The rules the correspondence imitates

Each row compares the runtime's or readback's code with the kernel function
section 6 names for it, read at `398e89ba`.

| Step | Runtime or readback | Kernel | Compared |
| --- | --- | --- | --- |
| β | `#run`'s `apply` frame binds the argument cell, unforced, at the λ's symbol in a frame over the λ's environment | `weak`'s `App` case: `ck_substitute(body, payload, argument)`, the argument unreduced | Same contraction, by environment instead of substitution |
| Readback redexes | a telescope `App(…App(L1(x1; D1, … Ln(xn; Dn, code)…), R(c1))…, R(cn))`, each `Li` the binder the frame's β contracted, its domain as written (`#telescope`) | `ck_substitute`, through `weak`'s `App` case, outermost first | The arguments are closed (claim 1), so the kernel's substitution captures nothing |
| Level redexes | a level variable is read through its frame; any other level that mentions one is read off `kernel.head` of the universe at it, closed by its telescope (`#levelTask`) | `ck_level_instantiate`, through `weak`'s `LApp` case | The kernel substitutes and canonicalizes; no level arithmetic in JavaScript |
| η | `#eta`: a `Lam` whose body is `App(f, x)`, an `LLam` whose body is `LApp(f, x)`, `x` not free in `f` by `#free`; a `PLam` over a `PApp` is unsupported | `weak`'s `LLam`, `Lam` and `PLam` cases, `ck_term_free` | The same syntactic test; `#free` binds as `ck_term_free` (`Pi`, `Lam`, `Sigma`, `LPi`, `LLam` bind their payload in child 1, as `ck_term_binder` lists them) |
| ι, point constructors | `#run`'s `eliminate` frame: the clause applied to the constructor's data and positions, then a hypothesis per position, `elim(q)` first-order and a `Lift` value standing for `λ ys. elim(q(ys))` | `ck_eliminate`: `reduct` applied to the `p.count` arguments, then `d.shown[j]` from `lifted`, `app(eliminator, y)` at the sort | The same order; path constructors, cubical positions and formal compositions are unsupported in the runtime, so its ι is the kernel's with no path application |
| Projections, sum and `Unit` eliminations | `project`, `sum` and `unit` frames | `weak`'s `Fst`/`Snd`, `SumRec` and `UnitRec` cases | The same selection. The runtime's `Pair` is a value without `weak`'s surjective-pairing contraction of `(t.1, t.2)`; for a closed term both heads are pairs whose fields compute the same values, and a normal-form readback keeps such a pair as written (W1's report, item 8) |
| δ | one cell per definition, its value read at first demand (`DefRef`) | `weak`'s `DefRef` case | Same |
| Origins | a non-data cell read back by the code and environment it was forced from, and every cell inside by its origin; data by value outside every non-data part | `folding_head`, which keeps the first definition spine its own steps pass, and `computed_data` | The folded oracle agrees wherever it decides ([3](#3-claims-1-to-6), claim 4) |
| W2's shortcuts | not on main | `ck_expose`, `weak`'s `PApp` and `Unglue` cases | Reviewed with W2 |

Every other node kind, compositions, transports, Glue, `unglue`, glue
terms, `abort`, paths applied and path constructors, is `unsupported` in
the runtime and falls back ([5](#5-the-fallback-boundary)).

## 3. Claims 1 to 6

1. **Closed and well typed.** Typing by instructions, too costly for every
   readback (1.4, D3), runs on every root readback of at most 400 nodes as
   a tree, and a failure fails the test. Counted by the census below: the
   constructs 144 (which their test asserts), the contracts' test file 47
   of its 66 runtime value forms, the Cubist test modules 88; all typed.
   W1's tests type a closure capturing `A : U0` and `x : A`, a type value,
   a constructor of `Box(A)` read back from a closure, a glue term's
   literal `Glue` type, a pair and an injection over bound variables, the
   shadowing cases and a level argument. Closedness was checked on every
   readback the test files make,
   by the census: 7,994 terms (W1's tests 94, the constructs 1,614, the
   contracts' file 3,578, the Cubist test modules 2,708; DAGs up to 2,048
   nodes), none with a free variable, binding as `ck_term_free` binds. The
   probe also reads back `2/3 + 1/6` and the wide inverse
   `bq_inv(-340282366920938463463374607431768211455/18446744073709551615)`
   by value and by origin, DAGs of 2,048, 338, 2,028 and 881 nodes, millions
   as trees: all closed. Well-typedness past 400 nodes rests on the
   argument (subject reduction, and a telescope is the context its code was
   checked in), as D3 decided.
2. **`R(c) ≡ t`.** The redexes are β ([2](#2-the-rules-the-correspondence-imitates)),
   and the runtime's steps are the kernel's; claim 3 tests the consequence.
3. **The oracle.** Read back by value, the full normal form of `R(root)` is
   the kernel's of the term wherever both complete within 2M steps, and so
   for each head an observation returned after η. On today's run no
   comparison disagrees and no readback is refused, over the constructs'
   156 runtime value forms (undecided: exactly the 3 slow full normal forms
   the test names), the binary contracts' 40 (undecided: exactly the 4
   widest the test names) and the Cubist test modules' 97, besides the
   contracts' file's other runtime value forms. W1's 18 mutations each
   fail an oracle the unchanged runtime passes.
4. **Folding, by origin.** The folded normal form of `R(root)` with origins
   is the kernel's of the term for all 156 constructs (asserted), and no
   comparison disagrees on the other two surfaces, where an undecided one
   is allowed; W1's eight folding regressions pass. A target, not a
   guarantee (3.4); a mismatch would fail a `!!` text test, never a
   verdict.
5. **Size.** W1's scaling test checks the bound on n closures over n
   variables (n = 4, 8, 16, growing as n²). The probe adds a tower of
   two-argument constructors, `grow(n) := mk(grow(m), grow(m))`, whose
   arguments EVAL4 shares: for n = 20, 50, 100 and 150 the readback's DAG
   is 2n + 3 nodes, within the cells (3n + 1) and copied nodes reached;
   writes are 6n − 1, interning merging the rest.
6. **No capture; nearest binding.** `#binding` takes the nearest binding,
   as `#run`'s `lookup` does. W1's capture and shadowing tests (one symbol
   bound twice, an inner domain naming the outer binder, a closure escaping
   the scope that shadows its variable) pass, the mutations "the farthest
   binding instead of the nearest" and "a free variable skipped" are
   killed, and the census found no free variable.

## 4. Lazy annotations

No readback path reaches the machine: `#readOut` and its tasks never call
`#run` or `#head`, nor set a cell's state, and a definition with no cell
is kept as its reference, never demanded. Besides building syntax and
reading nodes, a readback asks the kernel only for a level's weak head and
for the syntactic comparison of a pair's two projected terms. An unforced
annotation, a λ's domain, a pair's or an injection's type, a constructor's
instance, an eliminator's motive, is read back as its closure.

The test "a readback forces nothing" reads back, by value and by origin,
`(fun (n : UNat) => typed(Tag(count_into(n, 0)) and Unit, (tag, slow(n))))(2 * 200)`
and a λ whose domain is `Tag(count_into(n, 0))` at the same `n`. Across
each readback the query's forces, β and ι counts and its definitions are
unchanged, the kernel answers no query, and the readback's full normal form
is the kernel's.

## 5. The fallback boundary

On main, `valueFormOf` makes the query, walks the value form with
`observeNow`, and disposes of the query in a `finally`:

- a `RuntimeError` of kind `unsupported` abandons the walk, which is not
  shown, and the kernel's head queries walk the whole value form again
  from the start, once; the print records `by: "kernel"` with the refused
  demand and the runtime's counters;
- a stop at the runtime's limits is reported and not retried (`runtimeStop`:
  E487, E488, E489, and the declaration's own time limit as the kernel's
  queries report it);
- any other runtime failure on checked input, `expired` among them, is a
  defect, E490;
- a kernel fault or error during the walk is located and passed on.

No type decides the fallback, nothing the runtime computed is shown after
one, and no readback is made. The walk spends a query of the evaluation's
fuel per head on either path, so a restart spends the part walked twice:
at most the printer's 4,000 nodes each time, within a declaration's 50,000.

Evidence on `398e89ba`: the demand marks' 197 constructs, 156 value forms
by the runtime and 37 by the restart, each the kernel's, and 4 that use an
assumption refused before anything is computed (asserted, with the demand
each restart met); the binary contracts, each print written twice, once
per path; the library Euclid's fallback at NUM1's compositions; "a stop at
the runtime's limits is reported, not retried"; and "a failure in a
runtime value form's kernel reads ends the entry, and a rebased session
goes on", all in `npm test`. In the CLI (`node cli/repl.mjs "…"`):

| Entry | Shown | Computed by |
| --- | --- | --- |
| `count_into(2 * 255, 0)` | `510` | runtime; the kernel's queries stop with K344 |
| `typed(UNat and UNat, (2 * 255, 2 * 255))` | `(510, 510)` | runtime |
| `2/3 + 1/6` | `class((class((bnat.(15), bnat.(0))), class((bnat.(18), bnat.(0))), <fun>))` | runtime |
| `fun (x : Unit) => x` | `<fun>` | runtime |
| `to_out(node(fun (u : Unit) => leaf))`, a higher-order hypothesis | `branches(<fun>)` | runtime |
| library `euclid(3)` | `(7, (tt, <fun>), tt)` | restart at a composition |
| `bq_decide(1/2 + 1/3, 5/6)` | `left(relate(…, relate((bnat.(30), bnat.(0)), (bnat.(30), bnat.(0)), <path>)))` | restart at the path constructor |
| `parity(big)` over a list of 200,000 | E488 at 20,000,000 cells | runtime, not retried |
| `count_into(2 * 3, 0) expecting 6` | `6` | the kernel's queries |

In the browser, the site test's REPL page computes the runtime's value
forms and meets its limits, and the 33 printed or evaluated values of the
reference pages are the Node checker's.

Lazy annotations under the fallback: the kernel's walk is its weak-head
queries, and the runtime meets the unsupported node where its walk demands
it, never by forcing an annotation first.

## 6. The generation

`readback` checks `handlesHeld` (`#kernel()`) when it starts, before every
write (`#write`), before a level's head query and before it returns; a
node not yet copied is read through `#kernel()` too. On expiry it fails as
`expired` and drops its memo. Within a readback nothing can move the
generation: it calls only `term`, `head`, `node` and `alphaEqual`, and the
generation moves only at `cb_rollback`, `cb_commit_checkpoint` and freeing
(`handles_moved` in `wasm/cubical_bridge.c`), whose one caller is
`CubicalDeclarationTransaction.finish`; that call also drops
`derivedHandles`, so a readback's admission to the normalize queries ends
with its transaction. A spent generation is 0, in which no handle is held.
W1's tests expire a readback that writes, a closed code's own handle and a
memoized handle after a rollback and after a commit, and the mutation "a
memo reused across generations" is killed; the bridge's own test passes in
the kernel run. A scratch probe confirms that a readback's term, admitted to
`normalize`, is refused after its transaction rolls back, and that the
query then expires. No user path holds a query across a session
operation.

## 7. Budgets and cancellation in the middle of a readback

Readback is synchronous; its steps and cells are the query's, checked by
`Budget.tick` and `allocate`, with the deadline and the signal checked at
its start and every 1,024 steps. W1's test stops a readback within its
first two steps. The test "a readback stopped partway leaves no partial
memo entry" stops one on the pair of the unary numerals `2 * 200` and
`3 * 100`, whose readback takes more than 3,072 steps:

- at a step budget halfway through it, as `budget` with that limit, after
  writes; the query's limits are cumulative, so it reads back no more, as
  after an observation's stop;
- at a cell budget halfway, as `resource`, after writes;
- at a deadline, the clock standing still for the readback's start and its
  first check, as `deadline`, after writes; the next readback of the same
  query is the term a fresh query reads back;
- by a signal aborted before the call, as `cancelled`, before its first
  step; the next readback is the fresh query's term.

W1's test "a lifted hypothesis is refused, and a value past the kernel's
syntax depth fails with K344" now also has the kernel accept the next
instruction after the K344, and the same query read back a part of the
value. The scratch probe did the same on `2/3 + 1/6`, whose readback takes
14,198 steps and 9,822 cells, by value and, at a step budget halfway
through its 2,883 steps, by origin.

A memo entry is made only when its term is complete, and an unstable one
serves only the readback that made it, so a stop leaves no partial entry
to reuse; the deadline and cancellation cases confirm it. A signal cannot
arrive during a readback, as during `observeNow`.

## 8. A malformed handle

`readback` takes only the query's own opaque handles (`#begin`, `#unwrap`).
The test "a readback refuses a handle that is not its query's own"
refuses, as `input`: another query's handle, a forged object, a kernel
handle, `null`, the head of a handle never observed, a readback by origin
of a query made without origins, and a value form's query; and, as
`disposed`, a disposed query's handle. A scratch probe also showed the
normalize guard refusing raw syntax that no instruction derived, and the
kernel refusing a child handle that names no node (`ck_make`).

## 9. Query-before-instruction isolation

Section 6 asks for a test that shows an instruction's verdict unchanged
with and without a readback before it, in the manner of
`kernel/tests/test_isolation.c`. W1 added none (F1); the test "an
instruction's verdict is the same with and without a readback before it",
in `tests/runtime-readback.test.mjs` since the kernel's C tests cannot run
the runtime, does it with
`def endo := (fun (B : U0) => (fun (A : U0) => A -> A)(B))(Unit);`, whose
readback by value is `(λ (A : U0). A -> A)(Unit)`, one node the readback
writes, as the test asserts. In each of three fresh sessions,
`x : (λ (A : U0). A -> A)(Unit)`, on that node (the readback's own handle
where the readback comes first, the same syntax built by hand elsewhere),
is refused as an argument of `λ (y : Unit -> Unit). y` ("The argument has
the wrong type."), and after a `Beta` step converts its type, `Apply`
accepts. One session makes no readback; one reads back by value and by
origin, and asks `normalize`, `normalizeFolded` and `head` of the
readback, before the instructions; one does so between two rounds of them.
The refusals and the accepted judgements' statements are identical across
all three. The kernel's own isolation test passes in the kernel and
sanitizer runs.

## 10. Syntax equality and conversion

W1's tests compare by `kernel.alphaEqual` only, and the oracle compares
normal forms by `alphaEqual` within a fixed step budget, counting an
undecided comparison apart. Neither calls `checker.equal` or any
conversion; the instruction driver appears only to type terms.

## Findings

1. **F1: section 6's isolation test was not in the repository;** W1's
   acceptance did not list it. Not a defect: the probe showed the property
   on main. **Covered** by "an instruction's verdict is the same with and
   without a readback before it" (`ab9df858`,
   [9](#9-query-before-instruction-isolation)).
2. **F2: the repository's readback tests did not stop a readback partway,**
   by a budget, a deadline or a signal, nor read back a foreign, forged or
   disposed handle, nor show that a readback forces nothing, nor use the
   query and the kernel after a K344. Not a defect: the probes showed each
   on main. **Covered** (`ab9df858`) by "a readback stopped partway leaves
   no partial memo entry", "a readback refuses a handle that is not its
   query's own", "a readback forces nothing", and two more checks in W1's
   K344 test ([4](#4-lazy-annotations),
   [7](#7-budgets-and-cancellation-in-the-middle-of-a-readback),
   [8](#8-a-malformed-handle)).

   Each new check fails when the property it states breaks. Under each of
   these temporary mutations, applied alone, the test named fails, and the
   unchanged code passes it:

   | Mutation | Test that fails |
   | --- | --- |
   | `Apply` compares the argument's type through the weak-head cache (`cc_instr_apply`, kernel rebuilt): the session without a readback refuses, the others accept | isolation |
   | a memo entry made when its frame is pushed, before its term is complete | stopped partway |
   | `readback` never clears its running flag | stopped partway; K344 |
   | no check of the signal at a readback's start | stopped partway |
   | an unknown handle read as the root | refuses a handle |
   | a disposal that leaves the query open | refuses a handle |
   | a head read where no observation computed one | refuses a handle |
   | a readback by origin of a query made without origins | refuses a handle |
   | a value form's query read back | refuses a handle |
   | an unforced cell forced while it is read back | forces nothing |
   | a kernel head query after each readback | forces nothing |
   | a refused term's kernel error left uncleared (`CubicalKernel.term`) | K344 |
3. **F3: `tests/cubical.browser.mjs` fails on main** (`398e89ba`), outside
   CI. Since `179c883b` (2026-10-20) the workbench has two `details`
   elements, and its `details summary` locator is ambiguous; with that made
   specific, its check of a raw syntax error asserts the diagnostic at once,
   while the check is answered asynchronously. Unrelated to readback. This
   branch fixes the harness minimally (`98ad1e49`): the locator names "Edit
   native syntax", and the test waits for the diagnostic; the test then
   passes.

## Review rounds

By the roadmap's rule this record's pull request is reviewed at `xhigh`
effort until a round returns no findings. Each round's findings and their
resolution are added here.
