# Derivations shared by the scope they read

Measuring typed readback for #329 found that `evaluate 2/3 + 1/6 expecting
5/6;` over the binary rationals took 43.5 s, 27.7M instructions and 4,739 MiB
before failing with `E326`. The verdict is right: the sum computes to the
representative 15/18, and no lowest-terms presentation is chosen. The cost
was the instruction driver deriving a shared folded normal form once per
path to each of its nodes. This change memoizes a derivation by the part of
its scope it reads. The kernel is unchanged, and every judgement is still
derived by kernel instructions.

## Where the sharing was lost

The smallest program is `evaluate 1/2 expecting 1/2;`, which succeeds, and
cost as much: 27,650,485 instructions, 42.9 s, 4,477 MiB. Its path:

- `Translator.evaluate` (web/translator/translate.mjs) computes the term's
  folded normal form (`checker.normalForm`, line 408) and the expected
  value's (`checker.verify`, line 429), and compares them with
  `scope.equal` (line 432; `Scope.equal`, web/translator/elaboration.mjs).
- `NativeCubicalElaborator.equal` (web/cubical-elaborator.mjs) infers the
  left side, then checks `<i> left` against `Path(type, left, right)`:
  each a derivation by the driver (`derived` → `InstructionDriver.infer`,
  `check`). The second derives the normal form again, under the path
  lambda's dimension.

The phases before the derivation keep the sharing. The kernel's folded
normal form of 1/2 is 963 nodes as a graph and 5,380,201 as a tree; the
decoded term is 975 objects, as `CubicalSyntax.decode` caches each node;
`CubicalSyntax.encode` caches each object, so the term reaches the driver
as the same graph. The derivation does not: `census.mjs` types that normal
form in a rolled-back checkpoint.

| Typing 1/2's folded normal form | main | this change |
| --- | ---: | ---: |
| Instructions | 12,792,293 | 50,262 |
| Instruction steps | 14,552,838 | 1,528,301 |
| `deriveNode` calls | 6,730,385 | 4,197 |
| Distinct handles derived | 2,296 | 2,227 |
| Distinct scopes | 1,663,078 | 1,313 |
| `agree` calls | 2,027,560 | 56,742 |
| Time | 19.4 s | 0.6 s |
| Peak memory | 2,902 MiB | 624 MiB |

`InstructionDriver.derive` memoized a derivation by
`${scopeKey(scope)}|${handle}`, the whole scope. Each Π, Σ and λ binder
extends the scope with its entry, so a subterm met under binders it does
not mention, as the nonzero proof's closed types are, was derived again
under each; and a binder met in several scopes made several scopes of its
own, so the scopes multiplied along paths. The kernel's instruction memo
returned the same judgements, but the driver walked the graph per path,
issued every instruction again, ran `agree` on every application, and kept
6.7M long string keys.

## The change

`InstructionDriver.narrow` (web/cubical-instruction-driver.mjs) gives a
derivation the part of its scope it reads, and nothing else:

- the entries of its free variables (`freeTermSymbols`), each derived
  from its own entry;
- every live dimension, as a binder inside whose dimension is live is
  renamed apart from it;
- the faces, which restrict a variable whose type mentions them;
- the dimensions the types of all the scope's variables mention, kept as
  a mask (`MENTIONED`), as a path binder's renaming reads them
  (`typesMention`).

A variable bound inside the term gets the entry its name and type give it,
whatever else is in scope, so the derivation in the narrowed scope is the
one the whole scope would give; each judgement's context is the union of
its premises', so it combines with any around it. Narrowing the live
dimensions to those the term mentions was tried first: a composition's
binder could then stay at a live index the whole scope would rename it
from, and the unglue equivalence's normal form failed to check again with
a type mismatch (tests/translator/univalence-derived.test.mjs). Where in
the search that mismatch arose was not traced.

The derivation's cost exposed a second dependence. With
`2/3 + 1/6 expecting 5/6`, the conversion fails, `settle` normalizes both
sides (3.2M and 2.8M steps), and `convertTo` then offered the two `Path`
types to `Lift`, whose `ck_syntactic_cumulative` compares them whole
before refusing. On main that took 4.4M steps and refused (`E326`), after
the repeated derivations had run in the same kernel; after narrowing, with
far less work before it, the same `Lift` ran past one instruction's
10M-step budget (`K338`). `Lift` includes one type in another only along
Π, Σ and level Π binders ending in universes, so `convertTo` now offers it
only such types (`cumulative`). That needed a fix in the driver's alpha
comparison: `freeDimensionMask` (web/cubical-syntax.mjs) did not count the
face of a composition's tube or a Glue type's piece met alone, so the
comparison dropped the renaming of a binder around it, and
`<i> comp^k A [i = 0 ↦ u] a` differed from `<j> comp^k A [j = 0 ↦ u] a`.
`Lift` had made up for it: with the `Lift` change and without the fix,
checking `import propositions;` refuses `retract_has_level`,
`inverse_point_square` and `glue_path_idtoequiv` with type mismatches, and
every declaration that depends on them, `prop_type_is_set` among them. In
that check the driver's comparison refused three pairs of types that the
kernel's alpha equality accepts.

## Measurements

Each workload ran in its own process with `probe.mjs`, main (c00d960a) and
this change built from one WASM kernel, Node 24.13.0, macOS arm64, under
`caffeinate`, one at a time, on a machine other jobs may have shared.
Times are single runs; no speed claim is made beyond them. Instructions are exact;
steps depend on the kernel's caches. `results.jsonl` holds every line.

| Workload | main | this change |
| --- | ---: | ---: |
| `evaluate 1/2 expecting 1/2;` | 27,650,485 instr., 42.9 s, 4,477 MiB | 119,984 instr., 1.2 s, 650 MiB |
| `evaluate 2/3 + 1/6 expecting 5/6;` (`E326` both) | 27,678,916 instr., 40.5M steps, 43.5 s, 4,739 MiB | 121,296 instr., 8.5M steps, 2.1 s, 906 MiB |
| `evaluate typed(BQ, 1/2) expecting !!(1/2);` | 27,650,481 instr., 42.1 s, 4,466 MiB | 119,981 instr., 1.2 s, 656 MiB |
| `evaluate typed(BQ, 1/2) expecting !!_;` | 91 instr., 31 ms | 87 instr., 31 ms |
| `evaluate rationals.(2/3) expecting rationals.(2/3);` | 27,554,837 instr., 43.0 s, 4,547 MiB | 117,974 instr., 1.2 s, 631 MiB |
| `evaluate 12 * 12 expecting 144;` (BInt) | 53,257 instr., 82 ms | 3,172 instr., 37 ms |
| `evaluate bnat_mul(bnat.(12), bnat.(12)) expecting bnat.(144);` | 179 instr., 5 ms | 175 instr., 5 ms |
| `evaluate euclid(3).1 expecting 7;` | 42 instr., 9 ms | 42 instr., 9 ms |
| binary_rational_contracts.cubist | 1,395,132 instr., 12.1M + 8.1M steps, 8.4 s, 774 MiB | 493,285 instr., 11.2M + 7.5M steps, 7.6 s, 717 MiB |
| binary_integer_contracts.cubist | 859,069 instr., 5.9M + 32.1M steps, 6.7 s, 675 MiB | 386,801 instr., 5.7M + 40.8M steps, 6.7 s, 647 MiB |
| cubist-tests/rational_examples.cubist | 964,754 instr., 3.6M + 3.3M steps, 5.8 s, 609 MiB | 412,045 instr., 3.0M + 3.3M steps, 5.4 s, 591 MiB |
| Archive audit (`--all`), 3,858 declarations, 0 failures | 5,136,255 instr., 13.1M + 13.4M steps, 34.5 s, 2,318 MiB | 2,852,361 instr., 10.8M + 13.0M steps, 32.2 s, 2,295 MiB |

File rows give instruction steps + query steps; each file's outcomes,
evaluations and diagnostics have the same digest before and after. The
setup of the entries is `import binary_rationals; use binary_rationals;`,
`import rationals;`, `import binary_integers; use binary_integers;`,
`import bnat_notation;` and `import euclid; use unat;`. The driver trace
fixture (tests/fixtures/driver-trace.json) goes from 15,010 issued
instructions to 15,000 with the `Lift` change and to 10,642 with
narrowing; its weak-head queries and checked declarations are unchanged.

One query costs more. In binary_integer_contracts.cubist the
`wide_product_decision` evaluation's normal form takes 37.1M query steps,
where main takes 28.6M, with the same outputs; measured cold, in a
rolled-back checkpoint, 37.0M against 28.1M. The admitted definitions are
alpha-equal on both sides (all 877 after `import binary_integers`); four,
`quotients.quotient_induction`, `quotients.descend`,
`h1_truncation.mere_eliminate` and `h1_truncation.mere_map`, differ only
in the numbers of binders the kernel renamed (`native4428_174` against
`native3305_174`), and the arena's handles differ throughout. The kernel's
syntax memo is direct-mapped by handles and symbols
(kernel/src/syntax_cache.c), and the debugging plan records ticks as
fixture-dependent. On main alone, allocating 1,123 symbols before the
import moves the same cold query from 28.1M to 33.1M steps (500 and 2,000
leave it at 28.0M); this change takes 36.8M to 37.0M cold under the same
shifts. The difference is recorded here, not attributed further.

## Other paths

- `!!_` and `!!!_` compute a normal form and match a hole: nothing derives
  it, and nothing changes (the table's `!!_` row).
- An expression under `!!` or `!!!`, an expression leaf of a pattern
  (`observe`, `mismatch` in web/translator/evaluation.mjs) and a typed
  pattern's annotation (`sameType`) compare by `scope.equal`, the same
  derivation: the `!!(1/2)` row.
- `witness` reads a closed truncation's witness with `scope.accepts`, a
  check, the same derivation.
- Every check and definition derives through `InstructionDriver.derive`:
  the audit's instructions fall by 44%.
- The driver's alpha comparison and guide already cut renamings to what
  the two sides mention (tests/normalization-sharing.test.mjs).

A failed exact comparison still normalizes both sides fully before it
refuses (`settle`): of the 8.5M instruction steps of `2/3 + 1/6`, about 6M.
Typed patterns ask the weak-head comparison (`differ`) first for that
reason; the exact comparison does not, and whether `differ` separates
these two values was not measured.

## Tests

tests/normalization-sharing.test.mjs:

- "a graph shared beneath different binders is derived once per node":
  a type whose levels each reach the one below by three paths, 3^40 in all,
  closed and over a variable in a path type, derived within 10 instructions
  a level. Main stops at the test's bound of 2,000 issued instructions
  within its first levels.
- "an exact expected value on a binary rational derives its folded normal
  form by its graph": checks the graph (under 2,000 nodes) and the tree
  (over a million) of 1/2's folded normal form, then `evaluate 1/2
  expecting 1/2;` within 1,000,000 instructions. Main stops at 1,000,001;
  this change issues about 120,000.
- "dimension pruning keeps the renamings a system's faces read": the
  alpha comparison and the kernel agree on compositions and Glue types
  whose faces name a renamed binder. Main's comparison finds them
  different.

tests/evaluation-demand-marks.test.mjs looked for the evaluation's first
weak head among every query of the program, but a handle is a number that
an earlier declaration's rolled-back work may have used; with fewer nodes
allocated, one did. It now looks among the evaluation's own queries.

`npm test` passes (1,908 tests), and `node tools/audit-cubical.mjs --all`
checks 3,858 declarations with 0 failures.
