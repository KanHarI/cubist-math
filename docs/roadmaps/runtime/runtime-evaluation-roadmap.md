# Runtime evaluation and binary numerical foundations

Status: planned on 2026-10-07, following a local investigation at
`825c8b8896e02364e9d5cd53f5079014362738ab`. EVAL0 is implemented: its
[baseline](#measurements) was recorded on 2026-10-08. The early numerical
foundation is `UNat` and `BNat`, with binary naturals underlying `Z`, `Q`
and later numerical constructions. At the main `fc0362d3` starting point,
none of the NUM packages or other EVAL packages was implemented. The
[#266](https://github.com/KanHarI/cubist-math/pull/266) implementation includes
EVAL1's one-pass REPL path and a version-3 baseline.
[#269](https://github.com/KanHarI/cubist-math/pull/269) implements EVAL2, caching
completed full normalizations by exact syntax identity. NUM0's source
representations and bit arithmetic are implemented below. NUM1's semiring
agreement, universe transport, bitwise equality/setness and comparison
correctness are implemented, together with dependent Peano/strong recursion
and factorial. The default-`Nat` migration is implemented below; its release checks pass.
NUM2 is in progress: the binary integer ring/domain and rational field are
constructed; certificate-normalization validation and the default `Z`/`Q`
migration remain. EVAL3–EVAL8 remain open:
[#289](https://github.com/KanHarI/cubist-math/pull/289) adds a
[first internal EVAL3/EVAL4 query](#first-implementation-289) for ordinary
data, which no checker, REPL or page uses yet. EVAL5's observation contract
has shipped as the [demand marks](../historical/evaluation-demand-marks.md) and
[folded normal forms](../historical/folded-normal-forms.md); its typed readback has not.
[#284](https://github.com/KanHarI/cubist-math/pull/284)'s explicit-evidence
directives, `evaluate nonempty P by w;` and `evaluate empty P by r;`, check
evidence without normalizing it.
The [open quotient normalization fix and API audit](../../reports/open-quotient-normalization.md)
extend EVAL2: dimension substitution preserves shared work, partial bodies
normalize under their face conditions, shared universe levels avoid repeated
expansion, and interrupted substitution queries report failure consistently.
This addresses the open `bint_mul` failure found during NUM2 without changing
the arithmetic definitions or raising kernel limits.
The [elaborator audit](../../reports/elaborator-path-family-normalization.md)
addresses false dependence in constant path families and local reduction
budget failures. The [nondependent descent change](../../reports/nondependent-quotient-descent.md)
closes the generic quotient gate. The quotient-free transport gates and the
binary-rational inverses' full normalization remain open. The binary-rational
API was released on the inverses' folded normal forms (2026-10-26), and the
default `Z`/`Q` migration is gated the same way, by the decision of that day.
These fixes do not complete NUM2.
The [explicit normalization stack](../../reports/normalization-stack.md) covers
the existing full normalizer's traversal. The
[weak-head tail loop](../../reports/weak-head-tail.md) also removes native
recursion for chains of definition unfolding and tail contractions;
prerequisite head queries and composition helpers remain guarded native calls.
The [bounded substitution traversals](../../reports/substitution-stack.md)
move term/dimension substitution, capture-avoidance renaming and dependency
scans onto explicit stacks, including tube lists inside substitution and
free-dimension analysis. Composition, Glue and HIT tube helpers remain
recursive. The syntax-depth guard remains. The
[comparison and level worklists](../../reports/comparison-level-stacks.md)
replace native recursion in syntactic and tube-list comparison, cumulative
type descent, level arithmetic and level canonicalization. Composition/Glue/HIT
tube construction, the Glue-step reduction comparison (`normal_agree`/
`parts_agree`), prerequisite head queries and frontend traversals remain
open, and the fixed four larger BNat cases still hit the syntax guard.
Joint EVAL3/EVAL4 evaluator integration and the remaining protected traversals
are still open.
A [small arithmetic-free reproduction and partial-reduction report](../../reports/rational-normalization.md)
now records the remaining failure. Its
[completion path](#rational-full-normalization-completion-path) below assigns
the structural work to EVAL3/EVAL4/EVAL8 and keeps full rational normalization
separate from lazy data execution.
The [selected rational literal diagnosis](../../reports/rational-literal-normalization.md)
adds a fixed 100,000-tick `SameRatio` reproduction using main's library alone.
It isolates expensive retained relation syntax without the BQ parser and
does not close the existing inverse or transport gates.
The [debugging plan](rational-normalization-debug-plan.md) of 2026-10-21,
re-measured after the demand marks, reproduces the small inverse on main
alone and attributes its cost to the setness-of-propositions evidence inside
the negative integer equality certificate, which every literal of main's
public rationals also carries. It attributes the smaller costs to the
quotient induction behind two-argument descent and the integers' laws, and
orders the library, kernel and host experiments against fixed gates.
A versioned scratch evaluator supplies feasibility evidence only.
The [work plan](../work-plan.md#runtime-evaluation-track) schedules this track;
the [computation notation roadmap](../high-level-abstractions/computation-notation-roadmap.md) owns
`do` and arrows, which are independent of these evaluator changes.

**Scope directed on 2026-10-17:** runtime optimization is the current priority.
Keep the numerical library to naturals, integers and rationals, adding only
ordered-ring and ordered-field definitions. Make binary naturals the public
`Nat` once NUM0/NUM1 and the unary-client migration pass; retain explicit
`UNat`. Do not start the reals roadmap, `PosRat`, Archimedean bounds or
completeness. After performance work, return to language features, monads,
categories and homology/cohomology. The existing EVAL7 natural-number pilot
stays within its stated contract.

**Decisions of 2026-10-26:**
- The default `Z`/`Q` switch is gated on folded normal forms, as the
  binary-rational API's release was.
- This phase also connects the runtime query of #289 to the REPLs, adds
  typed readback and lands EVAL7.
- EVAL7 moves primality and divisibility to `library/`, as step NT2 of moving
  all of the archive's number theory there. The archive's `euclid`, `primes`
  and numeral modules are deleted once their consumers move
  ([archive retirement](../archive-retirement.md#number-theory-in-the-library)).
- The [work plan](../work-plan.md#first-actions) orders these steps after the
  site-publication fix and B8 of the
  [debugging plan](rational-normalization-debug-plan.md).

## Goal and current failure

Make small, closed mathematical constructions practical to execute while
preserving their checked types, assumptions and computational meaning.
The first workload is [Euclid's construction](../../../archive/first-library/euclid.cubist):
`euclid(n)` returns a prime above `n`, together with its certificates, by
finding a prime divisor of `factorial(n) + 1`.

At the baseline, `euclid(3)` returns a pair beginning with `7`, but both
`euclid(4)` and `euclid(4).1` fail with:

```text
K344: Native prototype syntax depth exceeds 512.
```

This is the limit in [term_store.c](../../../kernel/src/term_store.c), reached
during normalization. `factorial(4)` returns `24`; `typeof euclid(4)` also
succeeds. The failed projection allocated about 136,000 intermediate
syntax nodes before reaching the limit. Its deepest chain repeatedly
passes through applications, pairs, projections and lambda-domain types.
The current reducer substitutes arguments through this syntax, including
annotations. Requesting just the prime already avoids normalizing the
final certificate, but does not avoid building these intermediate terms.
Raising the depth limit alone does not address their growth.

Reproduce in separate CLI sessions after `make wasm`:

```sh
node cli/repl.mjs 'import euclid; use nat; evaluate euclid(3);'
node cli/repl.mjs 'import euclid; use nat; print(evaluate(euclid(3)));'
node cli/repl.mjs 'import euclid; use nat; evaluate euclid(4);'
node cli/repl.mjs 'import euclid; use nat; evaluate euclid(4).1;'
node cli/repl.mjs 'import euclid; use nat; evaluate factorial(4);'
```

Read the reported result or diagnostic, not just the process exit status:
the REPL currently reports evaluation errors without failing the process.

## Measurements

EVAL0's [harness](../../../tools/evaluation-baseline.mjs) recorded the
investigation's observations as a versioned baseline. The figures in this
section are historical EVAL0 evidence; the current record includes EVAL1,
whose measurements follow below. Each sample is a new
Node process that checks the workload's imports and runs its entry as the
CLI REPL does, once cold and three times warm. Five samples per workload
were recorded on 2026-10-08 at `b5a261c8` with Node 24.13.0 on
macOS/arm64, Apple M3 Pro, in the
[original baseline record](https://github.com/KanHarI/cubist-math/blob/fc0362d30b2fafef4b8d5f0b75a1f56a89f148b6/tests/fixtures/evaluation-baseline.json). Its kernel
work and arena counters are deterministic; every workload's five cold
samples agree on them. Times are medians on that machine, not portable
targets. To repeat this historical behavior, use an isolated checkout of
`b5a261c8` (or the pre-EVAL1 `fc0362d3`) and rebuild there with `make wasm`.
Running these commands on the current sources measures EVAL1 instead:

```sh
npm run baseline:evaluation
node tools/evaluation-baseline.mjs --only=euclid-3,euclid-3-print --samples=3
```

| Workload | Result | Normalizations | Comparisons | Instructions | Cold |
| --- | --- | --- | --- | --- | --- |
| `evaluate euclid(3);` | `(7, …)` | 2 | 2 | 258,730 | 435 ms |
| `print(evaluate(euclid(3)));` | `(7, …)` | 1 | none | 12 | 32 ms |
| `evaluate euclid(3).1;` | `7` | 2 | 2 | 42 | 8 ms |
| `evaluate euclid(4);` | K344 | 1, failed | none | 13 | 31 ms |
| `evaluate euclid(4) expecting (5, _);` | K344 | 1, failed | none | 13 | 32 ms |
| `evaluate euclid(4).1;` | K344 | 1, failed | none | 14 | 31 ms |
| `evaluate euclid(5).1;` | K344 | 1, failed | none | 15 | 44 ms |
| `evaluate 2 * 255;` | K344 | 2 | 2, one failed | 529 | 14 ms |
| `print(evaluate(2 * 255));` | `510` | 1 | none | 264 | 9 ms |
| `evaluate winding(integer_loop(negative(2)));` | `right(2)` | 2 | 2 | 59 | 36 ms |

Before EVAL1, the REPL's [evaluate method](../../../web/repl-session.mjs) built
`evaluate e expecting e`. The [translator](../../../web/translator/translate.mjs)
then verifies and normalizes both sides, and asks for checked equality of
their types and normal forms. That comparison takes 400 of the 435 ms of
`evaluate euclid(3)` and 258,718 of its 258,730 instructions: the instruction
kernel derives the expanded certificate's equality with itself. Its two
normalizations take 16 ms. The print path checks and normalizes once,
without the self-comparison.

The record also shows:

- Each Euclid failure happens in the first normalization, before any
  comparison: `euclid(4).1` allocates 136,134 nodes and 571,099 steps
  before K344, `euclid(5).1` 231,033 nodes. Printing fails identically.
  The pattern `(5, _)` repeats plain `euclid(4)`'s counters exactly.
- A unary natural is a successor chain, so its normal form's syntax depth
  grows with its value: printed, `2 * 255` reaches depth 512, the limit,
  and `2 * 256` fails. The REPL's self-comparison wraps the normal form
  once more, so plain `evaluate 2 * 255` fails where printing succeeds.
- A REPL entry leaves the session's names as they were, but not its arena:
  the failed `euclid(4).1` leaves its 136,150 nodes there, and a successful
  `evaluate euclid(3)` leaves 95,592.
- Warm runs of the same entry reuse the session's kernel caches: the failed
  `euclid(4).1` takes under 1 ms warm, and `evaluate euclid(3)` 58 ms.

A separate JavaScript experiment, now
[versioned](../../../tools/closure-evaluation-experiment.mjs), evaluates checked
syntax with environments and memoized thunks. It keeps lambda domains, pair
types, eliminator motives and unused fields suspended. It supports the
ordinary data operations used by this workload and refuses unsupported
operations; it does not implement general H1 elimination or cubical
computation. The baseline runs it as a separate series on the checked
definition `probe := euclid(n)`:

| Prime component requested | Scratch result | Evaluation time | Thunks forced | Deepest forcing | Peak memory |
| --- | --- | --- | --- | --- | --- |
| `euclid(3).1` | `7` | 6 ms | 13,210 | 120 | 156 MiB |
| `euclid(4).1` | `5` | 20 ms | 75,342 | 352 | 179 MiB |
| `euclid(5).1` | `11` | 1.2 s | 4,561,663 | 1,648 | 1,340 MiB |
| `euclid(6).1` | JavaScript call-stack overflow | 10 ms before failure | about 13,000 | about 3,500 | 154 MiB |

These runs ask the kernel nothing and allocate no kernel syntax. They do not
normalize or certify the returned proof fields. Peak memory is the sample
process's, about 140 MiB of which loading and checking the imports already
use. Where the stack overflows depends on how far the JIT has compiled the
evaluator, so the failed run's counts are observations, not counters.

### EVAL1 measurements (2026-10-17)

The [EVAL1 baseline](https://github.com/KanHarI/cubist-math/blob/f675a07cec93c9a73c272208742e65ad0aec91eb/tests/fixtures/evaluation-baseline.json),
version 3, recorded three cold samples and three warm runs per sample on
Node 24.13.0, macOS/arm64, Apple M3 Pro. A seven-workload pre-change run
from `fc0362d3` is retained in
[eval1-before.json](../../reports/eval1-before.json). The after record is
explicitly marked modified relative to that base revision. To reproduce the
seven-workload before run, build an isolated checkout of `fc0362d3` with
`make wasm`, then run:

```sh
node tools/evaluation-baseline.mjs --samples=3 --only=euclid-3,euclid-3-print,euclid-3-prime-expected,multiply-2-255,multiply-2-255-print,euclid-4,euclid-4-prime
```

The retained report is a copy of that checkout's `build/evaluation-baseline.json`
(the tool writes JSON there; stdout is a text summary). On that implementation,
`node tools/evaluation-baseline.mjs --samples=3 --write` records all 26
workloads in the version-3 after baseline.

| Workload | Before | After |
| --- | --- | --- |
| `evaluate euclid(3);` | 2 normalizations, 2 comparisons, 258,730 instructions; 416.5 ms cold median | 1 normalization, no comparison, 12 instructions; 29.2 ms cold median |
| `evaluate 2 * 255;` | K344 during self-comparison | `510`, one normalization |
| `evaluate euclid(3).1 expecting 7;` | 2 normalizations, 2 comparisons, 42 instructions | Unchanged |
| Full `euclid(4)` and its prime projection | K344 in normalization | Still K344 |

The Euclid normal-form digest and displayed value are unchanged. Its entry's
node growth falls from 95,592 to 54,783. Timings are local observations;
regressions assert outcomes, normalization/comparison counts and bounded work.
EVAL1 does not solve substitution growth, persistent arena growth or the
remaining syntax-depth failures.

## Contracts to preserve

### Execution, observation and normalization

Keep three outcomes distinct:

1. **Value execution:** compute a demanded value, such as `euclid(4).1`.
2. **Lazy observation:** expose a pair or constructor and expand its fields
   on demand, retaining suspended terms and their checked types.
3. **Full normalization:** produce the typed normal form currently promised
   by `evaluate` and used by the kernel's normalization step.

A successful prime projection does not establish that full `euclid(4)`
normalizes. A renderer that shows a suspended certificate must identify it
as suspended. It must not silently present a partial value as a normal
form. EVAL5 specifies any new observation interface before changing the
existing CLI/browser behavior or `evaluate ... expecting ...` contract.

### Types and computation

For an already checked judgement `Γ ⊢ t : A`, the judgement's type need
not accompany every execution step. Checking-only annotations inside `t`
may likewise be suspended or erased where their role permits it. The
current normalizer receives the expression handle, not a separate expected
type, but the expression still contains embedded annotations.

Type-valued expressions used by computation must remain executable.
Transport's family, Glue equivalences and composition's type structure
cannot simply disappear. Information currently read from an annotation,
such as a neutral path's endpoint, must remain available or be compiled
into an equivalent operation. Preserve recorded universe distinctions and
the signature's existing rules for erased universe parameters.

No blanket proof erasure is proposed. A path or certificate can be used by
computation. Laziness means not forcing an unused field; it does not mean
replacing that field by reflexivity or declaring all proofs equal.

### Trust and lifecycle

Only checked inputs enter the user-facing execution path, with the same
closedness and non-computing-assumption checks as today. A suspended or
unused field must not hide an assumption from that inventory.

An evaluator query certifies no equality. If its result is used in a proof,
the kernel must validate a reduction derivation or compute it using a
reviewed trusted reducer. Checking only that the output has the expected
type is insufficient. A query's caches must never change an instruction's
verdict; preserve [instruction isolation](../../../kernel/tests/test_isolation.c).

Give runtime objects an explicit arena/session lifetime. Rollback,
compaction, disposal and handle reuse must invalidate or relocate every
reference they retain. Evaluation keeps bounded work and memory accounting,
cooperative deadlines and cancellation, and useful failure diagnostics.

## Early numerical foundations: UNat, BNat, Z and Q

Define both representations early, independently of the new evaluator:

- `UNat` is the unary natural number type, retaining structural induction
  for mathematical arguments and constructions where unary naturals are
  convenient.
- `BNat` is the binary natural number type, with a canonical zero and
  nonzero bit representation. Its arithmetic operates on bits directly.
  Alongside bit-structural induction, provide strong induction and
  computation from results at all smaller numerical values.
- `BNat` is the default foundation for numerical constructions. In
  particular, `Z` is built from pairs of `BNat`, and `Q` is the field of
  fractions of that binary-backed `Z`. They must not implement arithmetic
  by converting magnitudes through `UNat`.

This is a new numerical library. The existing
[integers](../../../library/integers.cubist) and
[rationals](../../../library/rationals.cubist) provide construction evidence;
comparison maps, isomorphisms and universe paths to those old types are
outside this track. The unary/binary natural equivalence remains an early
deliverable because both representations are useful. Here `BNat` names the
binary carrier explicitly; once NUM0/NUM1's correctness and compatibility
gates pass, expose it as the new default `Nat` as directed on 2026-10-17.
The retained equivalence then becomes `UNat` ↔ `Nat`. Document the name and import
transition for existing unary clients before switching the public name.

The ordered-ring and ordered-field definitions landed in
[#267](https://github.com/KanHarI/cubist-math/pull/267), alongside the algebra
lattice refactor supported by #268's inherited operation implementations.
They do not supply ordered `Z`/`Q` models,
decidable order, completeness or real-number constructions.

Naturals form commutative **semirings**, not rings: they have no additive
inverses. The required `UNat`/`BNat` isomorphism therefore preserves zero,
one, addition and multiplication as a commutative-semiring isomorphism.
Establish nontriviality, additive cancellation, multiplicative cancellation
by a nonzero factor, and absence of zero divisors. Establish the new
binary-backed integers' ring and integral-domain properties and the new
rationals' field laws directly from these foundations.

Also construct equality of the natural carriers as members of `U0`, using
the library's [computational univalence](../../../library/univalence.cubist).
The required path has the following schematic signature:

```text
unary_binary : UNat =[U0] BNat
```

Build this path from the underlying equivalence of the natural semiring
isomorphism. Prove that transporting an element along the path
agrees with the forward conversion and transporting along its reversal
agrees with the inverse. Prove agreement of the transported operations
with the destination operations. This universe equality is an explicit
deliverable alongside the semiring isomorphism. It permits checked
transport of dependent constructions; it does not make unary and binary
constructor syntax definitionally equal.

The archive already contains useful source evidence:
[canonical binary data](../../../archive/first-library/binary_naturals.cubist),
[bitwise arithmetic](../../../archive/first-library/binary_arithmetic.cubist),
[round trips and equivalence](../../../archive/first-library/binary_equivalence.cubist),
and [arithmetic correctness](../../../archive/first-library/binary_arithmetic_correct.cubist).
Reuse their mathematics and checked examples while building the foundational
modules in `library/`; do not make the library depend on archived `primes`
or other archive-only prerequisites. Keep numeral types and basic arithmetic
below the algebraic model layer to avoid an import cycle through `algebra`.

## Milestones

EVAL0 is done. EVAL1 is implemented in #266; EVAL2 and NUM0 are implemented below.
NUM1's semiring, transport, equality/order and dependent-recursion work is
implemented. The default-`Nat` compatibility migration is implemented with
release validation passed (#278, 2026-10-18). NUM2, EVAL3/EVAL4 and EVAL5 are
partly delivered, as their rows say; the other rows remain. Sizes are relative
scope, as in the work plan.

| Package | Deliverable | Dependencies | Size |
| --- | --- | --- | --- |
| EVAL0 | Reproducible workload and phase measurements. **Done** on 2026-10-08 | Existing CLI, counters and build stamps | S |
| EVAL1 | One-pass REPL evaluation; implemented in #266 | EVAL0 | S |
| NUM0 | Explicit UNat and canonical BNat with direct binary arithmetic; implemented | Current inductive declarations; archive evidence | M |
| NUM1 | Natural semiring isomorphism, U0 path/transport, bitwise setness, comparison correctness, H1 binary Peano view, coherent strong recursion and factorial; implemented | NUM0; semiring and order laws; H1 dependent elimination; computational univalence | L |
| NUM2 | New binary-backed Z and Q, ring/domain/field laws and default APIs. In progress: generic fractions (#279), binary integers (#280, #281) and the binary-rational API, released on folded normal forms (#283), and binary generic ring numerals; the default `Z`/`Q` migration and rendering remain | NUM1; current quotients, rings and fractions | L |
| EVAL2 | Memoized full normalization; implemented | EVAL0; independent of EVAL1 | M |
| EVAL3 | Closure evaluator for a specified data fragment. A first internal query for ordinary data (#289); integration remains | EVAL0 and semantic contract | L |
| EVAL4 | Explicit evaluation stack and bounded runtime. #289's machine loop; snapshot responsiveness and memory calibration remain | EVAL3 design; implement alongside it | M |
| EVAL5 | Lazy observation and typed readback. The observation contract is implemented: demand marks (#304–#306) and folded normal forms (#309, #310); typed readback remains | EVAL3, EVAL4 | L |
| EVAL6 | Packed BNat runtime values and checked specialization | NUM0–NUM2, EVAL3, EVAL4; new profile | L |
| EVAL7 | Efficient checked divisibility and search over BNat | NUM1, EVAL0; independent of the new evaluator | M |
| EVAL8 | Cubical integration, semantic review and release | Packages selected for release | L |

### EVAL0: measure the work separately

Add a versioned harness for full results, prime projections, factorial,
divisibility, ordinary data recursion, and representative cubical terms.
Separate import/checking, evaluator execution, typed readback, comparison,
decoding and rendering. Record revision, build stamp, runtime and machine,
settings, result/diagnostic, cold/warm runs, repeated timing samples, kernel
work, allocated nodes, peak live memory, thunk forces/cache hits and maximum
machine-stack depth where available. Include failed queries and time spent
before failure; do not count only successful normalization.

Keep the archived Euclid algorithm fixed for evaluator comparisons until EVAL7
replaces it (decided 2026-10-26). Then the comparisons move to the library
Euclid under a new baseline version, and the unary series keeps its recorded
revisions. A source algorithm change gets a separate series. Keep scratch evaluator
results separate from trusted normal forms and measure their different
output contracts explicitly.

**Acceptance:** reproduce the depth failure and REPL/print discrepancy,
and publish enough commands and artifacts to repeat both. Use deterministic
work/allocation regressions where practical; avoid hardware-specific CI
time thresholds.

**Implemented** on 2026-10-08. The
[harness](../../../tools/evaluation-baseline.mjs) runs 22 kernel workloads:
full Euclid results, their prime projections under the REPL, print,
exact-value and pattern contracts, factorial, divisibility decisions, unary
arithmetic at the depth limit, closed transport and winding numbers.
Eight failed in the original EVAL0 record; seven fail in the EVAL1 record. It also runs the four scratch projections as a separate
series. Each sample is a new process; one more times the cold entry
unobserved, and another measures syntax depth. The phases are elaboration,
checking, normalization, normal-form decoding, the assumption inventory,
comparison, rendering and the rest. The kernel's normalizer returns
syntax, so readback has no phase of its own there; the scratch series
times execution and readback apart. Thunk forces, memo hits and the
deepest force nesting are the scratch evaluator's. For the kernel, whose
C stack is not observable, the harness reports the syntax depth that each
normalization, comparison and check allocates, with the deepest chain.
The REPL displays at most 1000 characters of a value, so an outcome also
records a digest of the whole normal form evaluated, with bound variables
and dimensions numbered by binding depth: `euclid(3)`'s normal form prints
as about 340,000 characters.
[Its test](../../../tests/evaluation-baseline.test.mjs) keeps the recorded
outcomes, normal forms included, and normalization and comparison counts
exact, and lets the deterministic counters fall but grow by at most a
quarter. The EVAL0 test asserted the REPL/print discrepancy. The current
EVAL1 test asserts agreement, the successful `510` result and the remaining
K344 failures, and compares no times. It runs the scratch series on `euclid(3)`
and `euclid(4)` and reads the larger two from the record. A change past
those bounds records the baseline again with `--write`, and its reason.

### EVAL1: remove redundant REPL work

Implemented on 2026-10-17 in #266: `ReplSession.evaluate`
uses a scratch `print(evaluate(term))` entry. The existing print path checks
closedness and assumptions and normalizes once, displaying exactly as
`print(evaluate(term))` does. This also adopts the print path's behavior after
a call-form model selection, such as `use pick(0);`: it can display a
natural as `3` where the earlier REPL displayed `nat.(3)`. A selected model
without numeral notation still cannot read that bare numeral; use `nat.(3)`
for input. This is an existing print limitation, now shared by plain evaluation.
Explicit expected-value directives keep their independent comparisons.
See the [measurements](#eval1-measurements-2026-10-17).

Route plain REPL evaluation through one checked normalization and display,
sharing the existing print path where appropriate. Retain exact expected
value checks for source directives that actually supply an expected value.
Preserve notation selection, assumption diagnostics, scratch-entry lifetime,
failed-entry recovery and browser/CLI agreement.

**Acceptance:** one normalization for a successful plain evaluation;
the same full normal forms and assumption refusals, with print-equivalent display; the Euclid self-equality
instruction overhead disappears. In the baseline that comparison takes 400
of the 435 ms of `evaluate euclid(3)`, and plain `evaluate 2 * 255` fails
in it where printing shows `510`; both workloads measure the change. This
package does not claim to fix the syntax-depth failure.

### NUM0 and NUM1: representations, algebraic agreement and numerical induction

**NUM0 implementation (2026-10-17).** [unat.cubist](../../../library/unat.cubist)
exposes the existing unary carrier as `UNat` with an explicit `unat` notation.
[bnat.cubist](../../../library/bnat.cubist) defines canonical positive bits,
`BNat`, bitwise successor/predecessor, addition, multiplication, comparison
and computed equality/order predicates. The binary core imports no unary
module. The explicit conversions and their round trips live in
[bnat_unary.cubist](../../../library/bnat_unary.cubist); NUM1 now derives
binary setness from bitwise equality, as described below.
The successor/predecessor laws also check for arbitrary inputs.

[bnat_notation.cubist](../../../library/bnat_notation.cubist) supplies
`import bnat_notation; use bnat;` and direct decimal and `0b…` literals,
separately from the binary core. Decimal parsing accumulates a binary value;
only individual glyph digits and diagnostic character offsets are unary.
Decimal underscores count toward diagnostic positions. Computed values print
in decimal directly from their bits, using an available notation for the
checked binary literal parser; unreduced literals retain decimal or binary
spelling. Closed input/output round trips cover the 31/32-, 53-, 63/64/65-
and 127/128-bit boundaries. NUM2 extends this to integers and rationals.
Checked examples cover carries/borrows beyond 64 bits and a dense 128-bit
product; the differential suite proves 712 closed identities against
independent integer results. A dependency check confirms that the complete
binary core loads without the unary carrier and that equality/setness loads
without magnitude conversion; explicitly importing `bnat_unary` loads that
conversion as the positive control. Parser refusal cases pin invalid prefixes, digits and
their character offsets. All new modules import only the foundational library.

**NUM1 algebra implementation (2026-10-17).**
[bnat_arithmetic.cubist](../../../library/bnat_arithmetic.cubist) proves that
decoding preserves addition and multiplication for arbitrary binary values.
[semirings.cubist](../../../library/semirings.cubist) defines `CommSemiring`
as a general interface.
[bnat_semiring.cubist](../../../library/bnat_semiring.cubist) proves the binary
laws, cancellation, nontriviality and no zero divisors. The optional
[bnat_models.cubist](../../../library/bnat_models.cubist) packages both natural
models, conversion homomorphisms and `unat_bnat_semiring_iso`. The proofs
use the explicit conversion; the arithmetic operations still recurse on
bits. These results check without assumptions.

**NUM1 equality and comparison implementation (2026-10-17).**
[bnat_equality.cubist](../../../library/bnat_equality.cubist) connects the
computed equality predicate to paths, derives decidable equality from the
existing bit comparator and proves setness by Hedberg. It imports no
magnitude conversions. The shared `bnat_decode_injective` helper now returns
the bitwise equality certificate on a positive decision; its unary argument
is used only to refute an impossible negative decision. A forced 64-bit
semiring-law certificate checks by reduction; restoring the old helper
makes that same example exhaust the native reduction depth.
[bnat_order.cubist](../../../library/bnat_order.cubist) proves that the
binary comparator and its non-strict/strict predicates agree with numerical
order on the explicit unary decodings, and that both predicates are
propositions. These are proof-level comparisons; executable equality and
order still follow the bits.

**NUM1 transport implementation (2026-10-17).**
[bnat_transport.cubist](../../../library/bnat_transport.cubist) constructs
`unat_bnat_path : UNat =[U0] BNat` through `glue_path` using the semiring
isomorphism's maps and their checked inverse laws. General Glue transport
lemmas prove forward/reverse agreement with the explicit conversions.
Transporting zero, one and the whole addition/multiplication functions
agrees with the binary operations. Transported unary functions still evaluate
through the conversions; the agreement paths justify using the direct binary
operations. Closed forward/reverse examples compute by conversion; a
data-carrying dependent function family is transported, and its closed first
projection computes in [binary_transport.cubist](../../../cubist-tests/binary_transport.cubist).
These proofs add no assumptions or kernel rules.

**NUM1 recursion implementation (2026-10-18).**
[bnat_peano.cubist](../../../library/bnat_peano.cubist) defines dependent
`advance(p, a)` over positive offsets by bit recursion, with known binary
offsets and checked reindexing paths. Starting at zero gives `bnat_peano`,
whose zero/successor equations hold for arbitrary dependent families in
every finite universe.
The proof compares total dependent values with homogeneous iteration and
uses setness only for the binary index. That total-state iterator is proof
machinery; the executable dependent iterator uses its known binary offsets.
[bnat_recursion.cubist](../../../library/bnat_recursion.cubist) constructs
`BNatBelow`, decomposes `m < succ(n)` using binary decisions, and proves the
coherence of smaller-value callbacks. Its strong-recursion equation has no
proposition-valued restriction on the result family. Unary comparison
evidence is used only to refute impossible negative decisions.

Binary factorial uses that recursor and has checked zero/successor laws.
[binary_recursion.cubist](../../../cubist-tests/binary_recursion.cubist)
computes `0! = 1`, `5! = 120`, a data-carrying dependent witness, and digit
counts whose recursive call halves the input. It refuses a callback at its
own bound without strict-decrease evidence. A step ignoring smaller results
computes at a 64-bit bound without enumerating them. The `Below` construction
can still walk through intervening predecessor bounds when a smaller result
is requested; this is not a sublinear-time or memoization claim.
**Default migration (2026-10-18; release validation passed).** Public
`Nat` now aliases `BNat`. Its facade uses direct binary operations and calls
`bnat_literal` directly for decimal/`0b` input. The original unary declaration
and proofs live in `unat`: structural clients import `unat`, use `UNat`, and
call `unat_*` laws. Frontend numeral construction, lexical digits/offsets and
h-level indices refer to that explicit unary declaration. No default unary
magnitude limit applies to binary literals; the bounded unary diagnostic
points to `nat`.

Source printing records identity unary readers by their retained notation
identity: only the selected identity reader prints unary numerals bare;
other views print `unat.(n)`. The source and mathematical printers share
literal recognition, preserve literal spelling, and show computed binary
magnitudes in decimal. The migration fixture covers 64-bit carry, a dense
128-bit product, comparison, factorial, dependent recursion, mixed-carrier
printing and setness. Library, archive, browser and independent rechecking
remain release gates; passing the focused fixture alone does not release
the migration. The library README records constructor/import compatibility.
NUM2's integer/rational representations and EVAL3–EVAL8 remain separate work.

The default facade retains numerical induction but does not load the general
algebra models. Moving those five models to `bnat_models` reduces its checked
imports from 816 to 266 and native checking steps from 138,611 to 40,376 for
`import nat; def probe : Unit := tt;`. The former unary import checks 29
imports in 4,128 steps. These are deterministic import costs, not evaluator
benchmarks or wall-time speed claims. Public equational laws state their
conclusions in `nat` notation so `rw`, `simp` and `simpa` match public goals.

The [version-4 baseline](../../../tests/fixtures/evaluation-baseline.json)
records the fixed archive workloads with `UNat` identities and `unat`
notation. Their algorithms are unchanged. A fresh
[before report](../../reports/default-nat-before.json) on `81478e09` and the
after run on `553a1f17` use the same kernel build, three cold samples and one
warm run per sample. All 22 kernel entries have identical deterministic
work, allocations, phase calls/failures and measured syntax depths. Their
success/error outcomes match; normal-form digests and three rendered hashes
change with the renamed unary identities. All three successful closure
experiments retain identical work counts; the fourth still overflows the
host stack, whose stopping depth is not a performance counter. The fixture
is refreshed for this representation change, without changing its tests or
counter bounds. This comparison makes no wall-time speedup claim.

Display migration gates from #277:

- [x] Qualify unary numerals under non-identity notation views.
- [x] Show `0b` and rational literal-rule values readably in mathematical
  output, with readable numerical types in the proof workspace.

Expose the existing unary naturals as `UNat`, with a documented compatibility
policy for `Nat`, constructor names and imports. Define `BNat` with one
representation of zero and no redundant leading-zero forms. Implement
successor, predecessor, addition, multiplication, equality and comparison
directly over bits, plus named conversions in both directions. Prove both
round trips, setness and preservation of zero, one, addition and multiplication.

Add the necessary commutative-semiring interface alongside the existing
algebraic hierarchy and construct its two models and their isomorphism.
Prove or transfer cancellation, nontriviality and no-zero-divisors through
the checked maps. Also prove comparison/order agreement for the algorithms
that use it; a bare equivalence of carrier types is not enough. The bitwise
equality decision now supplies setness before NUM2 quotient computations
can force a unary-retraction proof. The semiring law fields share
`bnat_decode_injective`, which returns a binary path on a positive decision,
retaining the unary proof only to refute an impossible negative decision.
Conversions remain explicit computational functions. From this same equivalence,
construct `UNat =[U0] BNat` through computational univalence and prove its
forward/reverse transport laws and agreement of transported semiring
operations. This is a checked path in the universe, not a new definitional
equality rule. It does not wait for general theory structure-identity
machinery.

Establish well-founded induction for the numerical strict order on `BNat`
using H1 dependent elimination. Do not declare the usual indexed
accessibility family `Acc(n)`: its recursive occurrence `Acc(m)` changes a
parameter, which H1 refuses (E515); that direct declaration needs H2.
NUM1 instead constructs a binary Peano view and course-of-values induction
as ordinary definitions, with the following proof obligations:

1. Given `P : BNat -> U` and a successor step, define
   `advance(k, a) : P(a) -> P(a + k)` by structural recursion on the bits
   of `k`. Zero does nothing and one takes one successor step; an even
   digit applies the half's advance twice at successive offsets, and an
   odd digit takes one further successor step. Prove the index equalities
   needed for dependent transport. Starting at zero gives a dependent
   zero/successor eliminator over binary values; prove its zero and
   successor equations.
2. Apply this eliminator to the ordinary function type
   `Below(n) := forall m : BNat. m < n -> P(m)`. Its zero case eliminates
   `m < 0`. To extend `b : Below(n)` to `Below(succ(n))`, decide whether
   `m < n` or `m = n`: reuse `b` in the first case and transport
   `step(n, b)` in the second. Prove this order decomposition and that the
   order evidence is proposition-valued.
3. Let `below(n)` be the resulting function and set
   `F(n) := step(n, below(n))`. Prove coherence:
   `below(n)(m, smaller) = F(m)` whenever `m < n`, using the Peano view's
   equations and dependent function extensionality. This supplies the
   strong recursor's computation law for arbitrary dependent `P`, without
   restricting it to propositions or assuming the computation law.

This H1 construction is implemented in `bnat_peano` and `bnat_recursion`;
H2 and archived `W` are not dependencies. The zero and
bit-constructor clauses unfold by H1 computation; the public successor
and strong-recursion equations require checked path proofs, including
their transports and coherence. No new definitional computation rule is
promised. NUM1's larger size includes these proofs.

The strong-induction step receives
the result for **every smaller value**, independently of that value's bit
structure. Make it usable for definitions as well as propositions, with
the following schematic interface (names are provisional):

```text
bnat_induction(U < UU0, P : BNat -> U,
  step : (forall n : BNat. (forall m : BNat. m < n -> P(m)) -> P(n))) :
  forall n : BNat. P(n)
```

For `F := bnat_induction(U, P, step)`, prove the computation equation
`F(n) = step(n, fun (m : BNat, smaller : m < n) => F(m))`. State which
equations compute definitionally and which have checked path proofs.
Expose the zero/successor view as a convenient induction and recursion API.
Order lemmas may be transferred through the natural equivalence, but the
executable recursor above must keep binary values
instead of converting the bound to a unary counter. Earlier results are
available on demand; the interface does not require an eager table of
every prior value. Recursion through every predecessor can still take
work proportional to the numerical input.

Define binary factorial through this recursor and prove
`factorial(0) = 1` and `factorial(succ(n)) = succ(n) * factorial(n)`.
Also include a definition that requests a smaller value other than the
immediate predecessor, to exercise the full strong-induction interface.

**Acceptance:** both representations and their operations are available
without the new evaluator; conversion and arithmetic laws check without
new assumptions; the `U0` path and its transport laws check, including
closed forward/reverse examples and a dependent family transported along
the path; canonical binary boundary/carry cases compute; numerical
arithmetic operations use bit recursion without a hidden unary round trip;
the H1 Peano view, `Below` construction and coherence proofs check without
indexed declarations; strong induction works for a dependent family, its
recursion equation checks, and binary factorial computes `0! = 1` and
`5! = 120`. Check a recursive call that skips the immediate predecessor,
and require strict
decrease evidence for every recursive call. Preserve the existing unary
induction API through the documented migration policy.
The archive remains a compatibility corpus, not a library dependency.

### NUM2: build the new binary-backed integers and rationals

**Generic fraction layer (2026-10-18).**
[fractions.cubist](../../../library/fractions.cubist) now holds the existing
field-of-fractions construction independently of the integer instance.
Its quotient relation, operations, field laws and decidable equality are
unchanged. `rationals` imports this layer and instantiates it at `integers`.
The moved definitions keep their ordinary imported names; their qualified
inspection names now use the `fractions__` prefix.
The public integer and rational carriers and their numeral readers are still
unary; their default migration remains NUM2 work.

**Binary integer ring (2026-10-18).**
[binary_integers.cubist](../../../library/binary_integers.cubist) supplies `BInt`,
the same-difference quotient of `BNat` pairs. Both integer instances reuse
[differences.cubist](../../../library/differences.cubist), the ring of
differences of an additively cancellative commutative semiring with decidable
equality. Its proofs use the existing semiring distributivity and
commutative-monoid regrouping laws; they are not reimplemented for `BNat`.
The unary semiring model lives separately in `unat_models`, so the unary
compatibility integers do not import binary arithmetic. Public wrappers
instantiate the generic universe explicitly. Negation, addition and
multiplication respect the quotient; the commutative-ring laws, decidable
equality, nontriviality and an injective natural embedding preserving zero,
one, addition and multiplication are checked without assumptions. Its
`binary_integers` notation reads decimal and `0b` magnitudes directly into
binary pairs. Computed output still shows quotient representatives; this
is not a canonical signed presentation. The public `Z`/`Q` APIs and generic
`Ring.of_nat` compatibility path have not switched. The binary fraction instance
and integer-to-rational embedding are supplied below. Generic binary numeral
interpretation and the default migration remain open. This source
representation work changes no evaluator or kernel code.

**Shared integer domain proofs (2026-10-18).** `differences` derives absence
of zero divisors from nonzero-factor multiplicative cancellation and an
additive trichotomy witness. The existing unary domain statements become
typed instances of this proof; `bint_mul_nonzero` supplies the binary instance.
The natural equivalence supplies the binary additive-gap justification,
without comparison maps to the old integer carrier.

A quotient-respecting zero observer gives `bint_decide_zero` a compact
negative certificate. It compares the representative's components and uses
only constant 0/1 flags, independent of magnitude. The domain proof first
uses this zero decision on the product. For concrete nonzero products, its
certificate avoids evaluating the additive-gap justification or the general
quotient-effectiveness family parameterized by a large representative.
The constructor, arithmetic, equality and domain laws add no assumptions;
this source-level change does not alter the kernel or its resource limits.

The domain contracts check assumption-free nonzero-product certificates with
64/128-bit components and an instance of `fraction_field`. Disequalities are
checked as inhabited types, rather than by fully normalizing their proof
functions: `evaluate empty P by proof;` checks evidence of `P -> Void`, and
`evaluate nonempty P by proof;` checks evidence of `P`. Neither requires a
particular proof normal form. Equality decisions retain checks of
their computed branch. These tests do not establish full rational-value
normalization. A separate probe before the
open-normalization fix,
`evaluate fraction_field(binary_integers, bint_decide, bint_mul_nonzero,
bint_zero_ne_one).one expecting _;`, written `expecting !!_` since #304,
exhausted the term arena (`K347`) even
though its type checks and the individual nontriviality and product
certificates fully normalize.
The [kernel normalization fix](../../reports/open-quotient-normalization.md)
resolves this failure. This expression and the isolated quotient operation
now have permanent full-normalization regressions under a fixed work budget.
The default migration remains NUM2 work.

**Binary rational API (in progress).**
[binary_rationals.cubist](../../../library/binary_rationals.cubist) instantiates
the existing fraction field at `binary_integers`; it adds no second quotient
or field-law construction. `BQ` has the field operations, `bq_decide`, total
inverse `bq_inv`, and `bq_of_int`. The shared `fractions` layer now proves the
coefficient embedding injective and preserving zero, one, addition,
multiplication and negation; the binary instance uses those proofs.
Its literal reader accumulates binary integer/fraction magnitudes and decimal
scales directly. `0b` integers and binary denominators also use the binary
reader. Unary values hold only individual glyph digits and source positions.

Initial contracts check the field and embeddings without assumptions,
arithmetic/equality decisions, 64/128-bit fraction components, large decimals,
and the normal forms of wide values and an inverse under `!!_`, the
[folded normal form](../historical/folded-normal-forms.md), which computes their data in full
and keeps their certificates named. Their full normal forms are not gated:
measured on 2026-10-24 in fresh programs, `!!!_` of the wide inverse stops at
the kernel's normal-form depth (`K337`) after about 127M query ticks, and of
`bq_decide(1/2, 2/3)`, whose certificate is negative, at its syntax depth
(`K344`) after about 82M; their folded normal forms take 689,608 and 89,617.
The new API is released on these folded normal forms (2026-10-26). Public
`Z`/`Q` and numerical rendering still require their migration; generic ring
numerals are binary (below). No canonical signed or lowest-terms
presentation is claimed.

The original bounded follow-up probes localized the growth to full normalization of the
open integer multiplication function within the quotient's cross-multiplication
relation. The raw fraction `(1, 1, nonzero proof)` normalized in about 57 ms;
`SameRatio`, `Frac`, `q_one`, and `bint_mul` each exceeded a 10-second probe
deadline, reaching roughly 5.3 million terms. The `bint_mul` probe reproduced
on merged main after #280, before these domain changes. Closed large integer
products still normalize. These timings are diagnostic observations on one
machine, not benchmark thresholds or a change to normal evaluation limits.

**Generic ring numerals (2026-10-26).** `Ring.of_nat`, the derived
operation marked `notation numeral`, now takes a `BNat` and doubles from the
leading bit: `bp_even(q)` is `(one + one) * of_bpositive(q)` and `bp_odd(q)`
is one more. The unary operation is kept as `of_unat`. When a theory's
numeral operation takes the canonical `BNat`, the translator builds the
numeral's bits directly (`binaryNatural` in `web/translator/translate.mjs`),
so its size is the number of bits and the unary limit of 256 does not apply.
[ring_numerals.cubist](../../../library/ring_numerals.cubist) proves, in any
ring, that `of_nat` agrees with `of_unat` through the explicit conversions,
and that a map from `BNat` preserving zero, one, addition and multiplication
agrees with `of_nat`, as `bint_of_nat` does. A 128-bit numeral in a section
over an arbitrary commutative ring computes at `binary_integers`. At
`binary_rationals` each doubling also composes a nonzero-denominator
certificate: a 64-bit numeral's folded normal form computes, and a 128-bit
one stops at the syntax depth (`K344`). The rationals' own literal rule
builds the value directly and is unaffected.
A named notation's numeral rule over `BNat`, `numeral(n : BNat) := e`, reads
the bits the same way. `bnat_numerals` in the import-free `bnat` module is
one, so where `bnat_notation`'s literal reader is not imported, a binary
value prints as `bnat_numerals.(n)`, which reads back as the same bits. A
generic numeral, `CommRing.of_nat(A, n)` for a numeral `n`, prints as `A.(n)`
when `A` reads numerals by its theory: a model variable, or a model whose
module added no numeral or literal rule. It prints bare only where the
selected model is that declared model. A model with rules of its own would
read the text otherwise, so its numeral prints as the call (`theoryNumeral`
in `web/cubical-source-text.mjs`). Before, a unary numeral printed as
`CommRing.of_nat{{U}}(A, unat.(2))`.
Every numeral or literal abbreviation, bare or `name.(n)`, now prints only
where the scope it is printed for establishes that it reads back.
`notationContext` (`web/translator/notation-context.mjs`) asks the scope
what `name.(…)` selects there, through the elaborator's own resolution:
`selectionTarget`, which `selected` (`web/translator/theories.mjs`) calls to
decide the same question, on the scope's environment, where a model's
opening is an alias of each name it opens; or, in a scope with a retained
lexical context, `LexicalContext.selector`, deciding a slot or an opening by
the scope's outcomes. A lookup costs a few map reads, never a walk of the
environment. `selects`, `qualifies` and `readBack` in `sourceText` require a
positive answer; where the scope cannot give one, or a context has no
lookups, the term prints as written, a call or constructors. Every context
that shows text is given a real scope: a declaration's own, the module's
final one for terms shown after checking (the scope a definition appended
to it reads, its uses applied), and contextual queries. A declaration's
messages print before its scope is entered, in the selection its file-level
uses make (`notationForUses`); after a use that opens a model, whose fields
may hide any name but a named notation's, only named notations are trusted.
Generated-Cubist displays read no environment and print explicit forms. A
shadowed `unat` or `bnat_numerals` prints a value as its constructors, and
a model variable whose name a named notation takes prints its numeral as
the call; this also covers `unat.(n)` and the literal readers' qualifiers,
which main printed by name alone. A model's name is no qualifier where the
display writes that name for a variable, a binder or a dimension: the
printer collects the names as it writes them (`printedNames` in
`web/cubical-source-text.mjs`), so a binder it leaves out, as an
equality's coordinate, takes no name, and a display of several texts, as
a proof step's locals, goal and term or a mismatch's two types, reads the
names all of them write (`unitNames`). Operators and a model's bare operators
keep the name-only check
([pr-318-todo](../../reports/pr-318-todo.md)).
`tests/numeral-readback.test.mjs` combines each way of shadowing a reader's
name (a named notation, a binder, `use`, an import, a section opening) with
each numeral kind, and reads every printed text back on each surface: a
print, a type mismatch, a `use` message, the elaboration view, a REPL and a
contextual `typeof`. It also counts a printing scope's environment reads, so
displays stay linear in the number of terms shown, classifies every form the
printer handles or the core has by the binders it prints, checks that each
display's names are exactly the variable, binder and dimension names its
texts show, and reads back a numeral under a path dimension of its reader's
name, a proof step's goal under its locals, and a literal in an equality.
[ring_numeral_display.cubist](../../../cubist-tests/ring_numeral_display.cubist)
and [numeral_display_scopes.cubist](../../../cubist-tests/numeral_display_scopes.cubist)
check these displays with only the algebra and the number modules imported,
each read back, and the contracts check mixed bit patterns against the
binary integers' literal reader.

Construct `Z` from pairs of `BNat`, using the existing same-difference
relation and quotient approach with binary addition and multiplication.
Construct `Q` as fractions over this `Z`, retaining its nonzero-denominator
evidence and existing quotient semantics. Reuse the generic field-of-fractions
construction in [fractions.cubist](../../../library/fractions.cubist), instantiated
at the new integer ring with its checked decidable equality, nontriviality
and no-zero-divisor proofs. Its generic layer is separate from the current
integer instance; adapt numeral handling to avoid retaining a unary
arithmetic dependency. Canonical fraction normalization is a separate
feature; changing the natural representation does not itself put every
rational in lowest terms.

NUM2 owns these new carriers, arithmetic, algebraic laws and default APIs.
The [reals roadmap's R1](../mathematics/reals-roadmap.md#milestones) consumes them: it owns
their decidable orders and ordered-ring/field laws, `PosRat`, the
Archimedean property and later canonical presentations. R1's order
work remains proposed under the [number-order decision](../work-plan.md#open-decisions);
the 2026-10-17 direction includes only ordered-ring/field definitions and
keeps this further work paused. NUM2 does not wait for it. R2 and the later real constructions target the
new `Q`, with positive-rational precision and binary natural bounds. The
older unary-backed carriers remain compatibility clients, rather than a
second target for the new order development. No comparison to them is
required here. The later signed-integer and lowest-terms presentations
must use binary magnitudes and present these same new carriers.

Prove that the new operations respect their quotient relations. Establish
`Z`'s commutative-ring laws, decidable equality, nontriviality and absence
of zero divisors, then construct `Q` and prove its field laws. State the
domain properties explicitly; do not assume an `IntegralDomain` theory
is already present in the library. Prove the natural-to-integer and
integer-to-rational embeddings preserve the relevant operations. These
are embeddings within the new numerical hierarchy.

Make ordinary numerical APIs, integer magnitudes, rational components and
future number-system constructions use `BNat` by default. Extend the direct
decimal/binary input and printing established for the natural-number
migration above to integers and rationals, including numerical casts and
numeral interpretation over binary values. In particular, a large numeral
must not first become a unary `Nat` merely to enter a binary-backed ring.
Adapt the current numeral-rule and `CommRing.of_nat` paths with a binary
entry point and checked agreement; use repeated doubling/bit operations
where appropriate. Retain explicit `UNat` conversions for compatibility
and structural arguments. Carry the earlier `Nat` name and notation
migration through these APIs; the binary storage of `Z` and `Q` does not
depend on that spelling decision.

**Acceptance:** the default `Z` representatives contain `BNat` components,
and default `Q` fractions contain the resulting `Z`; the ring/domain/field
laws and numerical embeddings check without new assumptions. Arithmetic,
literals and rendering work on large binary magnitudes without allocation
proportional to their unary value. Update consumers and notation for the
new APIs; keep the archive checking under the documented imports and
unary-natural compatibility policy.
The binary rational API (#283) is released on the folded normal form: its
small and wide inverse contracts check under `!!_`, by the user's decision of
2026-10-26. By the decision of the same day, the default `Z`/`Q` switch is
gated the same way: the migrated API's contracts check under folded normal
forms. Full normalization of the small and wide rational inverses, including
their surviving certificates and annotations, remains a target, not a gate.
It does not require finishing every EVAL3–EVAL8 package: an earlier general
kernel/elaborator fix can meet it, together with any needed NUM
proof-algorithm change. The
[completion path](#rational-full-normalization-completion-path)
tracks the structural work currently planned to address the failures.
Record the new library's source-representation gains separately from
evaluator gains.

### EVAL2: preserve sharing during full normalization

Implemented on 2026-10-17. [Full normalization](../../../kernel/src/term_normalize.c)
now caches completed results by exact immutable syntax handle, alongside the
weak-head cache. There are no hash collisions. Reduction consults no local
context or assumed face; substitution and restriction create distinct syntax,
and referenced definitions and admitted signatures are immutable. Cache hits
still charge a kernel step and check the deadline. In-progress and failed
results are never published. Completed children can remain cached after a
sibling fails; rollback and compaction clear every entry before handles are
reused or relocated, including forward references created during failed work.

The table costs four bytes per arena capacity slot, included in the reported
arena memory. The [native regression](../../../kernel/tests/test_normalize.c)
normalizes forty shared sums (2^40 expanded leaves) in 122 steps, with or
without syntax interning; a repeated query takes one step. It also checks
typed instruction use, budget/deadline failures, scope and dimension
restriction, rollback, compaction and allocation before a later failure.
The existing instruction-isolation and cubical eta regressions remain gates.

Measured against the version-3 EVAL1 record with three cold samples and one
warm run per sample (`node tools/evaluation-baseline.mjs --samples=3 --warm=1
--only=euclid-3,euclid-3-prime,euclid-4-prime,factorial-5-print,multiply-12-12,transport-closed,winding-2`):

| Workload | EVAL1 normalization steps | EVAL2 normalization steps |
| --- | ---: | ---: |
| Full `euclid(3)` | 478,867 | 200,615 |
| `euclid(3).1` | 130,694 | 130,675 |
| `euclid(4).1`, before K344 | 595,614 | 595,611 |
| `factorial(5)` | 6,250 | 5,892 |
| `12 * 12` | 5,271 | 4,841 |
| Closed transport | 167 | 154 |
| Winding number 2 | 241,297 | 241,291 |

All seven outcomes, including full normal-form digests, match the existing
record exactly, and each workload allocates the same number of syntax nodes.
Full `euclid(3)` saves 58% of normalization steps; its reported peak arena
includes an additional 262,144 bytes for 65,536 cache slots. These are
deterministic work measurements, not a wall-clock speedup claim. K344 still
limits the larger Euclid inputs. The version-3 fixture served as the regression
reference: its allowed counter decreases covered this optimization. The
default-Nat migration records version 4 for the renamed unary identities.
The negative polynomial-root fixture now reaches its intended E606 type
mismatch instead of exhausting the K338 reduction budget; its expected
diagnostic is updated accordingly.

Finishing formerly budget-limited normal forms exposed a second sharing
problem: the driver's alpha comparison retained irrelevant term-binder
renamings, revisiting shared subterms under each enclosing scope. It now
prunes those renamings using exact free-symbol sets, preserving shadowing,
domains, annotations and level variables. A native-derived normal-form
regression with 2^40 expanded leaves compares in fewer than 2,000 node reads.
The archived `f4_galois_is_cyclic_two` re-derivation that exposed this took
about 11 seconds with only the kernel cache, and 16 ms with the comparison
fix (10 ms before EVAL2); the standard five-second deadline remains unchanged.

The [follow-up in #270](https://github.com/KanHarI/cubist-math/pull/270)
uses the kernel's existing syntactic-equality routine to compare
normal forms when no outer term or dimension renaming is needed. Its query
does no reduction, produces no judgement, and distinguishes failure from
inequality. The driver remembers the answer in its existing empty-scope memo;
the eventual instruction still validates equality. Scoped comparisons retain
the existing JavaScript implementation, which is also the fallback if the
native query cannot answer. Deadlines end the comparison. This avoids
rebuilding free-symbol
sets for the large normalized graph, without introducing a second scope
analysis or changing proof search.

In [seven alternating fresh-process pairs](../../reports/eval2-f4-comparison.json),
F4 re-derivation improves from a 16.7 ms median to 12.1 ms on the recorded
machine. Total kernel steps change from 200,348 to 200,349: the new query does
the comparison work otherwise performed by the eventual instruction. These
timings compare the follow-up against EVAL2, not against pre-EVAL2; they do
not establish that the residual regression against pre-EVAL2 is gone. The
original larger-input syntax-depth failures are unchanged.

**Acceptance:** shared graphs and repeated normalization avoid redundant
traversal; typed normal forms, eta behavior, failure recovery and instruction
isolation remain unchanged. Cache collisions cannot establish equality.
This reduces repeated work; it does not eliminate deep substitutions.

### EVAL3 and EVAL4: evaluate with environments and an explicit stack

Represent a delayed computation as syntax plus an environment. Function
application extends the environment rather than substituting the argument
through the body. Force demanded thunks once and share the result. Retain
constructor fields and annotation computations lazily. Existing syntax
interning and weak-head caches remain useful, but do not by themselves
remove substitution-generated terms.

Specify support for functions, pairs, sums, Unit and ordinary declared data.
Compile admitted constructor/eliminator metadata into reduction descriptors
instead of reconstructing clause types and displayed hypotheses at every
ordinary data step. Higher-order recursive positions need their own rule;
the scratch experiment's Nat-only layout is not a general H1 interpreter.
Unsupported constructs must fall back through a specified typed readback
boundary to the current reducer, or explicitly report unsupported execution.
Neither route may guess a result or repeatedly restart the same fallback.

Use continuation frames and an explicit work loop for evaluation and
readback. Do not replace the kernel syntax-depth failure with host stack
overflow, unbounded heap growth or an unresponsive worker. Budget thunk
forcing, environment lookup, allocations and fallback work. Ensure unused
arguments stay unused and shared thunks remain shared after suspension.

**Acceptance:** a written reduction/readback correspondence for the supported
fragment; differential checks against current reduction on tractable terms;
capture/shadowing and unused-argument cases; `euclid(4).1 = 5` and
`euclid(5).1 = 11` without materializing the substitution chains. The
`euclid(6).1` workload either completes or returns a controlled resource
diagnostic, never a host stack overflow. Measure retained closure memory
as well as avoided syntax allocation.

#### First implementation (#289)

[#289](https://github.com/KanHarI/cubist-math/pull/289) (2026-10-19) adds
`RuntimeQuery` in `web/cubical-runtime.mjs`, described in its
[report](../../reports/shared-runtime-evaluation.md). It is an internal query
over a snapshot of a closed judgement: syntax thunks with linked environments,
one shared thunk per definition, admitted constructor/eliminator descriptors
including higher-order recursive positions, and a loop with a continuation
array. Observation is shallow, and unsupported demand reports `unsupported`
with no fallback. Higher constructors, paths, composition, Glue and transport
are unsupported, and observations are not kernel evidence. In one exploratory
sample the primes of `euclid(4)` and `euclid(5)` observe as 5 and 11 with no
native syntax allocation, at 469,195 and 28,187,972 work. `euclid(6)` stops
at a 2M work limit. Retained memory is substantial (about 667 MiB process RSS
after the 5 case). No checker, REPL or page uses the query. Still open: the
written readback correspondence (EVAL5/EVAL8), a responsive snapshot copy,
memory calibration and closed-environment pruning, cubical execution, and
the integration that would let a user's `evaluate euclid(4).1` use it.

### Rational full-normalization completion path

The [nondependent quotient-descent change](../../reports/nondependent-quotient-descent.md)
passes the unchanged generic quotient's fixed gate by generating its squash
clause with the constant motive already known. It also enables a completed
small-inverse reference on the #283 diagnostic branch under the normal work
ceiling. This is a library
computation change, not completion of the evaluator stages below: the new
quotient-free setness-transport fixture and the wide rational remain open.

Planned on 2026-10-19; none of the stages below is claimed complete by the
diagnostic experiments. This is part of the existing runtime track and NUM2
release work. The original generic quotient reproduction is now a retained
regression for the library fix. The [constant-transport reproduction](../../reports/nondependent-quotient-descent.md#the-evaluator-reproduction-remains)
isolates the remaining Glue/composition workload without a quotient,
arithmetic or a concrete setness proof. Its `moved_setness` and `moved_path`
functions are the evaluator gates. The wide rational additionally exposes
unary expansion in mixed closed/open BNat law proofs.

1. **EVAL3/EVAL4: shared execution.** Implement closures, environments,
   memoized thunks and an explicit evaluation stack together. Compile
   ordinary admitted constructor/eliminator metadata, including higher-order
   recursive positions. Keep annotations and certificates available as
   delayed computations. Preserve checked-input, assumption, cancellation,
   work and memory accounting contracts. Use the Euclid projection acceptance
   cases above to validate this stage; they do not close rational full
   normalization.
2. **EVAL4: depth-independent traversal and readback.** Follow the actual
   substitution, scope/dimension, restriction, comparison and syntax-readback
   paths that remain recursive, including JavaScript syntax decoding,
   printing, `expecting` matching and driver alpha comparison. Replace native/host stack dependence with
   explicit bounded work, preserving capture avoidance and shared graphs.
   Separate intermediate growth from the depth of the required output.
   Removing a depth guard is allowed only after its protected traversals have
   resource-safe replacements; increasing 512 alone is not the fix. Acceptance
   uses the [fixed 32/64/128-bit open-addition and bitwise-proof baseline](../../reports/open-bnat-normalization-baseline.md).
   The larger left-addition and proof cases hit the current 512 syntax-depth
   guard. A temporary diagnostic exposes compact completed addition outputs
   and the 64-bit proof. With the explicit normalization stack, the same
   diagnostic also completes the 128-bit proof at 5,604 nodes and depth 1,436;
   see the [normalization-stack report](../../reports/normalization-stack.md).
   Production guards remain unchanged. All nine
   complete-function cases must normalize within the report's stated work,
   deadline, memory and stack constraints, with no host overflow. Raising either
   guard or a memory/stack limit is not a fix; retain the fixed fixtures through
   the traversal changes. The kernel probe does not cover the separate
   JavaScript decoding, printing, matching and comparison requirements.
3. **Applicable EVAL8 work: cubical execution.** Extend the correspondence
   and implementation to term/level/dimension binders, paths and endpoints,
   face restriction, composition, transport, Glue and higher elimination.
   Represent shared delayed substitutions/restrictions without repeatedly
   rebuilding proof syntax. Use `moved_setness` and `moved_path` from the
   constant-transport fixture and their fixed-budget [completion gate](../../reports/rational-normalization.md#what-counts-as-fixing-it)
   at this stage. Unsupported execution must be explicit or cross
   a specified typed fallback boundary; it must not repeatedly restart the
   same work. This semantic work is expected to be needed for the rational failure even if
   EVAL5's user-facing observation interface has not shipped.
4. **EVAL5/EVAL8: complete typed normalization.** Force every surviving proof
   and annotation when a full normal form is requested (`!!!` since the
   [folded normal forms](../historical/folded-normal-forms.md); `!!` keeps a stuck
   definition folded), with explicit-stack
   readback and bounded memory. Validate normal forms, eta, instruction
   isolation, lifecycle and canonicity under the applicable EVAL8 gates.
   Measure complete readback of both retained transport functions, and keep
   the generic quotient regression passing. Measure the quotient with
   concrete `prop_type_is_set(U0)` evidence as well: the parameterized case
   is now cheap, but `related_to` still uses that concrete proof. Retain full
   rational certificate measurements, not just projections. If output itself is too large, report that separately
   from avoidable evaluator work. No proof irrelevance or transport
   regularity rule is introduced to make the workload pass.
5. **NUM proof algorithms and release.** Replace the demonstrated unary
   fallback in BNat arithmetic-law proofs with checked bitwise arguments
   where needed, measuring that source change separately. Retain the
   arithmetic-free quotient regression and the unchanged quotient-free
   transport reproduction throughout. A library improvement does not by
   itself satisfy the evaluator gates. Re-run full small and
   wide rational inverses, all NUM2 contracts and the default `Z`/`Q`
   migration checks. Since 2026-10-26 those full-normalization results are
   targets, not gates: the binary-rational release and the default migration
   check folded normal forms. Construction work can proceed independently, and
   an earlier general fix can meet the targets without all EVAL packages.

The implementation order can overlap the source-proof and cubical work as
dependencies allow. The ordinary-data evaluator alone is not predicted to
fix Glue normalization, and an explicit stack alone cannot make an enormous
required normal form small. Each implementation PR needs Claude Code Opus
5.5 xhigh review (at most eight rounds), comparing new findings with prior
reviews and preserving the existing computation rules. Reals and unrelated
language-feature work remain outside this track.

### EVAL5: demand only the result being observed

Both notes below are complete and archived in `historical/` (2026-10-26).
Their decisions remain this package's contract, and the open work is in this
section.

The [evaluation demand marks](../historical/evaluation-demand-marks.md) note of 2026-10-21,
decided the same day, is this package's observation contract: unmarked
positions are forced as far as the pattern or printer observes them, `!`
requests a weak head and `!!` a full normal form, naming the kernel's two
existing queries. [#304](https://github.com/KanHarI/cubist-math/pull/304)
implements it for expected-value patterns, and
[#305](https://github.com/KanHarI/cubist-math/pull/305) for printed values:
the REPL's `evaluate e` and `print(evaluate(e))` show the value form, with
a marker such as `<fun>` where a function, a path or a type stops it.
Its measurements show that the prime of `euclid(4)` itself exceeds the
syntax-depth guard (`K344`) under head queries, so the Euclid acceptance
below needs an evaluator change as well as an observation contract. The
[acceptance report](../historical/evaluation-demand-marks/report.md) measures both PRs
against main. `evaluate small_inverse;` shows its value in 28,085 ticks,
where main normalizes it in 71,027,452. `expecting !!_` reproduces main's
counters and normal form exactly. `euclid(4)` against `(5, _)` still stops
with `K344`.

The [folded normal forms](../historical/folded-normal-forms.md) note of 2026-10-23,
decision D1 of the rational normalization debugging plan, changes what `!!`
computes: a folded normal form, in which closed data computes in full and a
definition whose head is no data stays as written, so a stuck proof is
named, not unfolded. `!!!` names the full normal form, which stage 4 below
measures. `rationals.(2/3) expecting !!_` falls from 70,301,825 ticks and
1,116,794 nodes to 43,932 ticks and 936.

Provide typed readback for demanded data and a separately specified way to
inspect suspended fields. Keep function bodies as closures until application
or explicit full-normalization demand. Printing must respect its output
budget without first expanding a complete proof graph. Preserve readable
names, dimensions, dependent field types and the provenance of certificates.

Full normalization still requires a path that reads back annotations and
proofs correctly. Its cost is measured separately from lazy display.
Expected-value patterns (L2.9a) and the closed-truncation REPL command
`witness TERM;` (L2.9b) are implemented in
[#181](https://github.com/KanHarI/cubist-math/pull/181) and
[#182](https://github.com/KanHarI/cubist-math/pull/182), after this roadmap's
investigation. Until #304, patterns matched `result.normal`, after full
normalization, so a `_` hole saved no evaluation work, and
`evaluate euclid(4) expecting (5, _)` failed with the same counters as plain
`euclid(4)` in the baseline. Since #304 a pattern computes each part only as
far as it observes it: that pattern no longer forces the certificate, but it
still fails with `K344` at the prime, which is itself too deep, and its
`!!!(5, _)` twin (`!!(5, _)` before folded normal forms) keeps the full
normalization measured. The demand marks
note specifies the observation mode, its checking and its failure contract. Preserve exact expected-value checks,
the distinction from full normalization and witness readout's checked type.

**Acceptance:** users can inspect the number and certificates of a Euclid
result independently; forcing a retained field after a session operation is
safe or produces a documented expiry error; lazy observations are visibly
distinct from full normal forms. Report whether full `euclid(4)` succeeds;
do not close that failure based on its projection alone.

### EVAL6: packed binary arithmetic and specialization

After NUM0–NUM2 supply source-level binary arithmetic, investigate packing
BNat's bit structure into arbitrary-precision runtime integers, with
constructors, bit elimination and conversions agreeing with the admitted
signature. Preserve UNat's distinct induction behavior where it is used.
Specialize hot checked arithmetic definitions or compile
ordinary eliminators after the baseline identifies their cost. Key any
specialization to the checked definition/signature, never merely the source
name `BNat`, `UNat`, `Nat`, `add` or `mul`. General induction can still require
work proportional to its input; compact storage alone does not make it constant
time. Binary numerical foundations do not wait for this runtime optimization.

Keep exact arithmetic, a general fallback, and typed reconstruction or
checked evidence when a result enters the kernel. Document whether the
compiler or primitive evaluator becomes trusted before enabling it there.

**Acceptance:** constructor/recursor agreement, arithmetic differential
cases beyond machine-integer ranges, name-shadowing and distinct-signature
cases, and resource accounting that includes large-integer work and readback.

### EVAL7: reduce the algorithm's work

The archive's [divisibility test](../../../archive/first-library/primes.cubist)
searches quotient candidates up to the dividend, testing multiplication and
equality. Prime-divisor search nests these tests. Its bounded search also
unwinds and rebuilds witness wrappers after finding an early witness.

Develop a checked BNat remainder-based divisibility decision and a search
with tighter bounds and an explicit early-exit structure. Use NUM1's
numerical recursion for calls justified by a strict decrease.
EVAL7 owns the small `library/` modules for binary divisibility, primality
and least-prime-divisor search, and a separate checked binary Euclid pilot
using NUM1's factorial. Port the required definitions and certificate
proofs from the archive; these modules depend on the new numerical
foundations, never on archived `primes`.

**Migration and archive removal (decided 2026-10-26).** EVAL7 is where
primality and divisibility move to the library over binary `Nat`.
1. Every consumer of the archive's `euclid` moves to the library Euclid: the
   landing page, quick reference and reference examples; the site, inspector,
   program and instruction-driver tests; the evaluation baseline; #289's
   probe and tests; and the demand-marks report.
2. `euclid.cubist` is deleted, and `primes` loses its divisibility and
   primality definitions: `Divides`, its decision and lemmas, `Prime`,
   `prime_divisor_exists`, `factorial_positive` and
   `bounded_divisor_of_factorial`. In Cubist sources only `euclid` uses them.
3. EVAL7 is step NT2 of moving all of the archive's number theory to the
   library ([NT1–NT5](../archive-retirement.md#number-theory-in-the-library)).
   The other steps cover the rest of `primes`, which then goes entirely:
   - its unary order lemmas move to `unat`;
   - its least-witness search moves with `natural_minimum`;
   - its unary `factorial` gives way to `nat`'s, with the binary and radix
     numerals.

Until the switch, the archived modules stay intact as the fixed workload for
EVAL0–EVAL5 comparisons. After it, those comparisons and EVAL3–EVAL5's
Euclid acceptance read the library Euclid, with a new baseline version, and
the unary measurements keep their revisions.
Candidate-divisor bounds such as the square root require their mathematical
proof. Preserve the least-divisor behavior if replacing this construction,
or expose and name a different algorithm separately. Factorial remains
the source algorithm's growth factor; do not silently replace Euclid's
construction with an unrelated prime generator to improve its benchmark.

**Acceptance:** checked correctness and certificates, no new assumptions,
agreement on the small Euclid witnesses `2, 2, 3, 7, 5, 11` for inputs
`0` through `5`, and separate before/after source-algorithm measurements.
This is a computation pilot, not a resumption of the paused library backlog.

### EVAL8: integrate with the trusted computation rules

Before replacing any kernel reducer, extend the correspondence argument
and tests to term/level/dimension binders, paths and endpoints, composition,
transport, Glue, higher constructors and elimination, face restriction and
eta. Preserve the distinction between syntax equality and conversion search.
Review how lazy annotations and fallback behave under each operation.

Run the applicable C and JavaScript suites, sanitizer checks, canonicity
fixtures, browser/CLI evaluation, archive checking and definition
re-derivation. Include checkpoint/rollback, cancellation, malformed raw
queries, assumption rejection and query-before-instruction isolation.
Differential tests support the semantic review; they do not replace it.

Publish supported fragments, residual failures, memory/work measurements,
and the full-result versus projection outcomes. A release described as
fixing `evaluate euclid(4)` must execute that original full-result command
successfully under its documented contract. A data-only milestone can ship
earlier under its narrower contract without making that claim.

## Suggested implementation order

Start with EVAL0 and EVAL1, and start NUM0/NUM1 alongside them, including
numerical induction and recursion. NUM2's new binary-backed `Z` and `Q`
follow the natural semiring foundations. These packages are independent
of the closure evaluator for their mathematical construction. NUM2's
binary-rational release and its default migration check folded normal forms
(decided 2026-10-26); its full normalization contracts are targets. The
[completion path](#rational-full-normalization-completion-path) coordinates
the applicable EVAL work; it does not require finishing all EVAL packages.
EVAL2 can proceed independently once its cache contract is clear. Design
EVAL3/EVAL4 together, then specify EVAL5's observation interface and complete
the relevant EVAL8 review before a runtime becomes a default path.
Re-profile the binary-backed constructions before investing in EVAL6.
EVAL7 follows NUM1 and keeps its measurements separate from both the
new numerical library and the unchanged-source evaluator comparison.
Mathematical coverage, resource behavior and the output contract gate
promotion; a faster prime projection
alone does not.

The order from 2026-10-26 on is in the work plan's
[first actions](../work-plan.md#first-actions):
1. B8 of the [debugging plan](rational-normalization-debug-plan.md), done on
   2026-10-26;
2. the default `Z`/`Q`;
3. #289's runtime in the REPLs: ordinary data first, then the point
   constructors of set quotients so that `BInt` and `BQ` values evaluate;
4. typed readback (EVAL5).

EVAL7, with the archive's `euclid` deleted, proceeds alongside 3 and 4.
