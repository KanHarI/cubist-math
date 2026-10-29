# Derivations shared by the scope they read

Measuring typed readback for #329 found that `evaluate 2/3 + 1/6 expecting
5/6;` over the binary rationals took 43.5 s, 27.7M instructions and 4,739 MiB
before failing with `E326`. The verdict is right: the sum computes to the
representative 15/18, and no lowest-terms presentation is chosen. The cost
was the instruction driver deriving a shared folded normal form once per
path to each of its nodes. This change memoizes a derivation by the part of
its scope it reads. The kernel is unchanged, and every judgement is still
derived by kernel instructions.

The public rationals are the binary ones since #319: below, programs read
`import rationals; use rationals;`, and `Q` is `BQ`. The numbers are
measured on main at 6f0cc3a4 and on this change merged into it; the
census below, at 216b7a6f, gives the same counts at 6f0cc3a4.

## Where the sharing was lost

The smallest program is `evaluate 1/2 expecting 1/2;`, which succeeds, and
costs as much: 25,545,661 instructions, 47.6 s, 4,488 MiB on main. Its path:

- `Translator.evaluate` (web/translator/translate.mjs) computes the term's
  folded normal form (`checker.normalForm`, line 409) and the expected
  value's (`checker.verify`, line 431), and compares them with
  `scope.equal` (line 435; `Scope.equal`, web/translator/elaboration.mjs).
- `NativeCubicalElaborator.equal` (web/cubical-elaborator.mjs) infers the
  left side, then checks `<i> left` against `Path(type, left, right)`:
  each a derivation by the driver (`derived` → `InstructionDriver.infer`,
  `check`). The second derives the normal form again, under the path
  lambda's dimension.

The phases before the derivation keep the sharing. The kernel's folded
normal form of 1/2 is 956 nodes as a graph and 5,380,191 as a tree; the
decoded term is 968 objects, as `CubicalSyntax.decode` caches each node;
`CubicalSyntax.encode` caches each object, so the term reaches the driver
as the same graph. The derivation does not: `census.mjs` types that normal
form, `typed(Q, 1/2)`'s, in a rolled-back checkpoint.

| Typing 1/2's folded normal form | main | this change |
| --- | ---: | ---: |
| Instructions | 11,644,803 | 49,846 |
| Instruction steps | 13,400,974 | 1,520,269 |
| `deriveNode` calls | 6,128,368 | 4,333 |
| Distinct handles derived | 2,334 | 2,334 |
| Distinct scopes | 1,511,915 | 1,382 |
| `agree` calls | 1,856,518 | 55,913 |
| Time | 18.8 s | 0.6 s |
| Peak memory | 2,779 MiB | 663 MiB |

`InstructionDriver.derive` memoized a derivation by
`${scopeKey(scope)}|${handle}`, the whole scope. Each Π, Σ and λ binder
extends the scope with its entry, so a subterm met under binders it does
not mention, as the nonzero proof's closed types are, was derived again
under each; and a binder met in several scopes made several scopes of its
own, so the scopes multiplied along paths. The kernel's instruction memo
returned the same judgements, but the driver walked the graph per path,
issued every instruction again, ran `agree` on every application, and kept
millions of long string keys.

## The change

`InstructionDriver.narrow` (web/cubical-instruction-driver.mjs) gives a
derivation the part of its scope it reads, and nothing else:

- the entries of its free variables (`freeTermSymbols`), each derived
  from its own entry;
- every live dimension, as a binder inside whose dimension is live is
  renamed apart from it;
- the faces, which restrict a variable whose type mentions them;
- the dimensions the types of the scope's other variables mention, kept
  as a mask (`MENTIONED`), as a path binder's renaming reads them
  (`typesMention`); a variable the term binds again is kept whole instead,
  as under that binder its entry is replaced and its type's dimensions no
  longer count, which a mask could not undo.

The second review of #331 found the last point missing: with x : p @ i in
scope, λ(x : Unit) over 64 path binders on i renamed each of them apart
from i and ran out of dimensions (tests/normalization-sharing.test.mjs).

A variable bound inside the term gets the entry its name and type give it,
whatever else is in scope, so the derivation in the narrowed scope is the
one the whole scope would give; each judgement's context is the union of
its premises', so it combines with any around it. Narrowing the live
dimensions to those the term mentions was tried first: a composition's
binder could then stay at a live index the whole scope would rename it
from, and the unglue equivalence's normal form failed to check again with
a type mismatch (tests/translator/univalence-derived.test.mjs). Where in
the search that mismatch arose was not traced.

The derivation's cost exposed a second dependence, measured on c00d960a,
before #319. With `2/3 + 1/6 expecting 5/6`, the conversion fails,
`settle` normalizes both sides (3.2M and 2.8M steps), and `convertTo` then
offered the two `Path` types to `Lift`, whose `ck_syntactic_cumulative`
compares them whole before refusing. On main that took 4.4M steps and
refused (`E326`), after the repeated derivations had run in the same
kernel; after narrowing, with far less work before it, the same `Lift`
ran past one instruction's 10M-step budget (`K338`). Main itself does so
at 6f0cc3a4, after #334, #323 and #332, where 216b7a6f answered `E326`:
`settle` takes 3.0M and 2.7M steps, and `Lift` runs out at 10M. `Lift`
includes one type in another only along Π, Σ and level Π binders ending
in universes, so `convertTo` now offers it only such types (`cumulative`). That needed a
fix in the driver's alpha comparison: `freeDimensionMask`
(web/cubical-syntax.mjs) did not count the face of a composition's tube or
a Glue type's piece met alone, so the comparison dropped the renaming of a
binder around it, and `<i> comp^k A [i = 0 ↦ u] a` differed from
`<j> comp^k A [j = 0 ↦ u] a`. `Lift` had made up for it: with the `Lift`
change and without the fix, checking `import propositions;` refuses
`retract_has_level`, `inverse_point_square` and `glue_path_idtoequiv` with
type mismatches, and every declaration that depends on them,
`prop_type_is_set` among them. In that check the driver's comparison
refused three pairs of types that the kernel's alpha equality accepts.
#334's fix is on main, and this change takes it: it counts the same face
in `freeDimensionMask`, compares a system's faces under the term that
holds it (`sameHead`, `sameFaces`), and reads a face's dimensions as bound
by binding depth or free by index (`sameFormula`), with a property test
against the kernel. Counting the face had exposed both comparisons, as the
second review of #331 reproduced: `<i> comp^i X [i = 0 ↦ a] a` against its
derivation's term compared unequal one way, and
`<d0><d0> comp^d3 Unit [d0 = 0 ↦ tt] tt` equal to
`<d1><d2> comp^d3 Unit [d1 = 0 ↦ tt] tt`. Both agree with the kernel on
the merged tree, and tests/normalization-sharing.test.mjs checks them. The
search's congruence (`agreeParts`) descends into a composition's tubes
only after `sameHead` has compared its faces at the composition, under
the dimensions around it, so it compares no face under the composition's
own binder.

## Measurements

Each workload ran in its own process with `probe.mjs`, main (6f0cc3a4) and
this change merged into it built from one WASM kernel, Node 24.13.0, macOS
arm64, under `caffeinate`, one at a time, while two other heavy jobs ran on
the machine: main's 25.5M-instruction rows took 40 s to 178 s for the same
work. Times are single runs; no speed claim is made beyond them.
Instructions are exact; steps depend on the kernel's caches.
`results.jsonl` holds every line.

| Workload | main | this change |
| --- | ---: | ---: |
| `evaluate 1/2 expecting 1/2;` | 25,545,661 instr., 47.6 s, 4,488 MiB | 118,558 instr., 1.5 s, 736 MiB |
| `evaluate 2/3 + 1/6 expecting 5/6;` | `K338` after 25,571,241 instr., 44.2M steps, 47.7 s, 4,616 MiB | `E326` after 119,774 instr., 8.8M steps, 6.8 s, 935 MiB |
| `evaluate typed(Q, 1/2) expecting !!(1/2);` | 25,545,657 instr., 177.7 s, 2,811 MiB | 118,555 instr., 4.3 s, 704 MiB |
| `evaluate typed(Q, 1/2) expecting !!_;` | 91 instr., 166 ms | 87 instr., 181 ms |
| `evaluate rationals.(2/3) expecting rationals.(2/3);` | 25,545,746 instr., 125.8 s, 3,466 MiB | 118,642 instr., 2.3 s, 721 MiB |
| `evaluate 12 * 12 expecting 144;` (BInt) | 53,245 instr., 153 ms | 3,160 instr., 95 ms |
| `evaluate bnat_mul(bnat.(12), bnat.(12)) expecting bnat.(144);` | 179 instr., 7 ms | 175 instr., 8 ms |
| `evaluate euclid(3).1 expecting 7;` | 181 instr., 25,089 query steps, 14 ms | 176 instr., 25,347 query steps, 8 ms |
| binary_rational_contracts.cubist | 1,375,250 instr., 12.0M + 7.4M steps, 14.0 s, 729 MiB | 494,416 instr., 11.2M + 7.5M steps, 11.9 s, 748 MiB |
| binary_integer_contracts.cubist | 853,219 instr., 6.0M + 33.0M steps, 9.5 s, 696 MiB | 388,588 instr., 5.6M + 36.3M steps, 8.4 s, 669 MiB |
| cubist-tests/rational_examples.cubist | 2,122,476 instr., 17.7M + 5.2M steps, 11.6 s, 686 MiB | 621,954 instr., 16.1M + 5.2M steps, 9.0 s, 685 MiB |
| Archive audit (`--all`), 3,844 declarations, 0 failures | 5,123,124 instr., 13.1M + 13.0M steps, 49.3 s, 2,422 MiB | 2,846,249 instr., 10.7M + 12.9M steps, 46.1 s, 2,375 MiB |

File rows give instruction steps + query steps; each file's outcomes,
evaluations and diagnostics have the same digest before and after. The
setup of the entries is `import rationals; use rationals;` for the first
four, then `import rationals;`, `import binary_integers; use
binary_integers;`, `import bnat_notation;` and `import euclid; use nat;`,
the library's binary Euclid since #334.
On c00d960a, before #319, `rationals.(2/3)` was the unary construction's,
and its exact comparison took 27,554,837 instructions, then 117,974. The
driver trace fixture (tests/fixtures/driver-trace.json) goes from 23,423
issued instructions to 23,407 with the `Lift` change and to 14,125 with
narrowing (15,010, 15,000 and 10,642 before NT1's lemmas joined it); its
weak-head queries and checked declarations are unchanged. The evaluation
baseline (tests/fixtures/evaluation-baseline.json) is recorded again, at
its version 10: its outcomes, normalizations and comparisons are
unchanged, each entry issues at most as many instructions as before
(`euclid(3).1 expecting 7`, 181 to 176), its query steps move between
-6.9% and +3.9%, and its imports issue fewer instructions (the library
Euclid's 235,246 to 142,671).

Some queries cost more. At 216b7a6f, in binary_integer_contracts.cubist the
`wide_product_decision` evaluation's normal form, measured cold in a
rolled-back checkpoint after the same setup, takes 33.6M query steps where
main takes 30.6M, with the same outputs. The admitted definitions are
alpha-equal on both sides (all 890 after `import binary_integers`); four,
`quotients.quotient_induction`, `quotients.descend`,
`h1_truncation.mere_eliminate` and `h1_truncation.mere_map`, differ only
in the numbers of binders the kernel renamed (`native4428_174` against
`native3305_174` on c00d960a), and the arena's handles differ throughout.
The kernel's syntax memo is direct-mapped by handles and symbols
(kernel/src/syntax_cache.c), and the debugging plan records ticks as
fixture-dependent. Allocating 1,123 symbols before the import moves main
to 30.9M and this change to 34.3M; on c00d960a the same shift moved main
from 28.1M to 33.1M, where this change took 36.8M to 37.0M. The
difference is recorded here, not attributed further.

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
refuses (`settle`): about 6M of the 8.8M instruction steps of
`2/3 + 1/6`. Typed patterns ask the weak-head comparison (`differ`) first
for that reason; the exact comparison does not, and whether `differ`
separates these two values was not measured.

## Tests

tests/normalization-sharing.test.mjs:

- "a graph shared beneath different binders is derived once per node":
  a type whose levels each reach the one below by three paths, 3^40 in all,
  closed and over a variable in a path type, derived within 10 instructions
  a level. Main stops at the test's bound of 2,000 issued instructions
  within its first levels.
- "an exact expected value on a rational derives its folded normal form by
  its graph": checks the graph (under 2,000 nodes) and the tree (over a
  million) of `typed(Q, 1/2)`'s folded normal form, then `evaluate 1/2
  expecting 1/2;` within 1,000,000 instructions. Main stops at 1,000,001;
  this change issues about 120,000.
- "dimension pruning keeps the renamings a system's faces read": the
  alpha comparison and the kernel agree on compositions and Glue types
  whose faces name a renamed binder. Before #334, main's comparison found
  them different.
- "a composition's faces are read under the binders around it, each by its
  own identity": the second review's two reproductions, above, which this
  branch failed before it took #334's comparison.
- "a variable the term binds again no longer mentions its type's
  dimensions under that binder": λ(x : Unit) over 64 path binders on i,
  with x : p @ i in scope, keeps each binder's index.

tests/evaluation-demand-marks.test.mjs looked for the evaluation's first
weak head among every query of the program, but a handle is a number that
an earlier declaration's rolled-back work may have used; with fewer nodes
allocated, one did. It now looks among the evaluation's own queries, as
main's version of the test since does.

`npm test` passes, and `node tools/audit-cubical.mjs --all` checks every
archive declaration with 0 failures.
