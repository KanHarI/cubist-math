# Runtime evaluation and binary numerical foundations

Status: planned on 2026-10-07, following a local investigation at
`825c8b8896e02364e9d5cd53f5079014362738ab`. EVAL0 is implemented: its
[baseline](#measurements) was recorded on 2026-10-08. The early numerical
foundation is `UNat` and `BNat`, with binary naturals underlying `Z`, `Q`
and later numerical constructions. None of the NUM packages or the other
EVAL packages is implemented. A versioned scratch evaluator supplies
feasibility evidence only.
The [work plan](work-plan.md#runtime-evaluation-track) schedules this track;
the [computation notation roadmap](computation-notation-roadmap.md) owns
`do` and arrows, which are independent of these evaluator changes.

## Goal and current failure

Make small, closed mathematical constructions practical to execute while
preserving their checked types, assumptions and computational meaning.
The first workload is [Euclid's construction](../../archive/first-library/euclid.cubist):
`euclid(n)` returns a prime above `n`, together with its certificates, by
finding a prime divisor of `factorial(n) + 1`.

At the baseline, `euclid(3)` returns a pair beginning with `7`, but both
`euclid(4)` and `euclid(4).1` fail with:

```text
K344: Native prototype syntax depth exceeds 512.
```

This is the limit in [term_store.c](../../kernel/src/term_store.c), reached
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

EVAL0's [harness](../../tools/evaluation-baseline.mjs) repeats the
investigation's observations as a versioned baseline. Each sample is a new
Node process that checks the workload's imports and runs its entry as the
CLI REPL does, once cold and three times warm. Five samples per workload
were recorded on 2026-10-08 at `e81d352b` with Node 24.13.0 on
macOS/arm64, Apple M3 Pro, in the
[baseline record](../../tests/fixtures/evaluation-baseline.json). Its kernel
work and arena counters are deterministic; every workload's five cold
samples agree on them. Times are medians on that machine, not portable
targets. Repeat it after `make wasm`:

```sh
npm run baseline:evaluation
node tools/evaluation-baseline.mjs --only=euclid-3,euclid-3-print --samples=3
```

| Workload | Result | Normalizations | Comparisons | Instructions | Cold |
| --- | --- | --- | --- | --- | --- |
| `evaluate euclid(3);` | `(7, …)` | 2 | 2 | 258,730 | 407 ms |
| `print(evaluate(euclid(3)));` | `(7, …)` | 1 | none | 12 | 30 ms |
| `evaluate euclid(3).1;` | `7` | 2 | 2 | 42 | 7 ms |
| `evaluate euclid(4);` | K344 | 1, failed | none | 13 | 31 ms |
| `evaluate euclid(4) expecting (5, _);` | K344 | 1, failed | none | 13 | 30 ms |
| `evaluate euclid(4).1;` | K344 | 1, failed | none | 14 | 32 ms |
| `evaluate euclid(5).1;` | K344 | 1, failed | none | 15 | 43 ms |
| `evaluate 2 * 255;` | K344 | 2 | 2, one failed | 529 | 12 ms |
| `print(evaluate(2 * 255));` | `510` | 1 | none | 264 | 7 ms |
| `evaluate winding(integer_loop(negative(2)));` | `right(2)` | 2 | 2 | 59 | 36 ms |

The REPL's [evaluate method](../../web/repl-session.mjs) builds
`evaluate e expecting e`. The [translator](../../web/translator/translate.mjs)
then verifies and normalizes both sides, and asks for checked equality of
their types and normal forms. That comparison takes 375 of the 407 ms of
`evaluate euclid(3)` and 258,718 of its 258,730 instructions: the instruction
kernel derives the expanded certificate's equality with itself. Its two
normalizations take 15 ms. The print path checks and normalizes once,
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
  `euclid(4).1` takes under 1 ms warm, and `evaluate euclid(3)` 56 ms.

A separate JavaScript experiment, now
[versioned](../../tools/closure-evaluation-experiment.mjs), evaluates checked
syntax with environments and memoized thunks. It keeps lambda domains, pair
types, eliminator motives and unused fields suspended. It supports the
ordinary data operations used by this workload and refuses unsupported
operations; it does not implement general H1 elimination or cubical
computation. The baseline runs it as a separate series on the checked
definition `probe := euclid(n)`:

| Prime component requested | Scratch result | Evaluation time | Thunks forced | Deepest forcing | Peak memory |
| --- | --- | --- | --- | --- | --- |
| `euclid(3).1` | `7` | 5 ms | 13,210 | 120 | 157 MiB |
| `euclid(4).1` | `5` | 21 ms | 75,342 | 352 | 183 MiB |
| `euclid(5).1` | `11` | 1.2 s | 4,561,663 | 1,648 | 1,383 MiB |
| `euclid(6).1` | JavaScript call-stack overflow | 10 ms before failure | about 13,000 | about 3,500 | 157 MiB |

These runs ask the kernel nothing and allocate no kernel syntax. They do not
normalize or certify the returned proof fields. Peak memory is the sample
process's, about 145 MiB of which loading and checking the imports already
use. Where the stack overflows depends on how far the JIT has compiled the
evaluator, so the failed run's counts are observations, not counters.

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
verdict; preserve [instruction isolation](../../kernel/tests/test_isolation.c).

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
[integers](../../library/integers.cubist) and
[rationals](../../library/rationals.cubist) provide construction evidence;
comparison maps, isomorphisms and universe paths to those old types are
outside this track. The unary/binary natural equivalence remains an early
deliverable because both representations are useful. Here `BNat` names the
binary carrier explicitly; when it is exposed as the new default `Nat`,
this is the `UNat` ↔ `Nat` equivalence. Document the name and import
transition for existing unary clients before switching the public name.

Naturals form commutative **semirings**, not rings: they have no additive
inverses. The required `UNat`/`BNat` isomorphism therefore preserves zero,
one, addition and multiplication as a commutative-semiring isomorphism.
Establish nontriviality, additive cancellation, multiplicative cancellation
by a nonzero factor, and absence of zero divisors. Establish the new
binary-backed integers' ring and integral-domain properties and the new
rationals' field laws directly from these foundations.

Also construct equality of the natural carriers as members of `U0`, using
the library's [computational univalence](../../library/univalence.cubist).
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
[canonical binary data](../../archive/first-library/binary_naturals.cubist),
[bitwise arithmetic](../../archive/first-library/binary_arithmetic.cubist),
[round trips and equivalence](../../archive/first-library/binary_equivalence.cubist),
and [arithmetic correctness](../../archive/first-library/binary_arithmetic_correct.cubist).
Reuse their mathematics and checked examples while building the foundational
modules in `library/`; do not make the library depend on archived `primes`
or other archive-only prerequisites. Keep numeral types and basic arithmetic
below the algebraic model layer to avoid an import cycle through `algebra`.

## Milestones

EVAL0 is done; the other rows are planned. Sizes are relative scope, as in
the work plan.

| Package | Deliverable | Dependencies | Size |
| --- | --- | --- | --- |
| EVAL0 | Reproducible workload and phase measurements. **Done** on 2026-10-08 | Existing CLI, counters and build stamps | S |
| EVAL1 | One-pass REPL evaluation | EVAL0 | S |
| NUM0 | Explicit UNat and canonical BNat with direct binary arithmetic | Current inductive declarations; archive evidence | M |
| NUM1 | Natural semiring isomorphism, U0 path and transport laws; H1 binary Peano view and strong recursion with coherence proofs | NUM0; semiring and order laws; H1 dependent elimination; computational univalence | L |
| NUM2 | New binary-backed Z and Q, ring/domain/field laws and default APIs | NUM1; current quotients, rings and fractions | L |
| EVAL2 | Memoized full normalization | EVAL0; independent of EVAL1 | M |
| EVAL3 | Closure evaluator for a specified data fragment | EVAL0 and semantic contract | L |
| EVAL4 | Explicit evaluation stack and bounded runtime | EVAL3 design; implement alongside it | M |
| EVAL5 | Lazy observation and typed readback | EVAL3, EVAL4 | L |
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

Keep the archived Euclid algorithm fixed for evaluator comparisons. A
source algorithm change gets a separate series. Keep scratch evaluator
results separate from trusted normal forms and measure their different
output contracts explicitly.

**Acceptance:** reproduce the depth failure and REPL/print discrepancy,
and publish enough commands and artifacts to repeat both. Use deterministic
work/allocation regressions where practical; avoid hardware-specific CI
time thresholds.

**Implemented** on 2026-10-08. The
[harness](../../tools/evaluation-baseline.mjs) runs 22 kernel workloads:
full Euclid results, their prime projections under the REPL, print,
exact-value and pattern contracts, factorial, divisibility decisions, unary
arithmetic at the depth limit, closed transport and winding numbers.
Eight of them fail. It also runs the four scratch projections as a separate
series. Each sample is a new process; one more times the cold entry
unobserved, and another measures syntax depth. The phases are elaboration,
checking, normalization, normal-form decoding, the assumption inventory,
comparison, rendering and the rest. The kernel's normalizer returns
syntax, so readback has no phase of its own there; the scratch series
times execution and readback apart. Thunk forces, memo hits and the
deepest force nesting are the scratch evaluator's. For the kernel, whose
C stack is not observable, the harness reports the syntax depth that each
normalization, comparison and check allocates, with the deepest chain.
[Its test](../../tests/evaluation-baseline.test.mjs) keeps the recorded
outcomes and normalization and comparison counts exact, and lets the
deterministic counters fall but grow by at most a quarter. It asserts the
REPL/print discrepancy and the K344 failures directly and compares no times.
A change past those bounds records the baseline again with `--write`, and
its reason.

### EVAL1: remove redundant REPL work

Route plain REPL evaluation through one checked normalization and display,
sharing the existing print path where appropriate. Retain exact expected
value checks for source directives that actually supply an expected value.
Preserve notation selection, assumption diagnostics, scratch-entry lifetime,
failed-entry recovery and browser/CLI agreement.

**Acceptance:** one normalization for a successful plain evaluation;
the same displayed values and assumption refusals; the Euclid self-equality
instruction overhead disappears. In the baseline that comparison takes 375
of the 407 ms of `evaluate euclid(3)`, and plain `evaluate 2 * 255` fails
in it where printing shows `510`; both workloads measure the change. This
package does not claim to fix the syntax-depth failure.

### NUM0 and NUM1: representations, algebraic agreement and numerical induction

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
that use it; a bare equivalence of carrier types is not enough. Conversions
remain explicit computational functions. From this same equivalence,
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

This is the planned H1 construction, not an implemented recursor or an
import from the archive. H2 and archived `W` are not dependencies. The
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

Construct `Z` from pairs of `BNat`, using the existing same-difference
relation and quotient approach with binary addition and multiplication.
Construct `Q` as fractions over this `Z`, retaining its nonzero-denominator
evidence and existing quotient semantics. Reuse the generic field-of-fractions
construction in [rationals.cubist](../../library/rationals.cubist), instantiated
at the new integer ring with its checked decidable equality, nontriviality
and no-zero-divisor proofs. Separate its generic layer from the current
integer instance and adapt numeral handling to avoid retaining a unary
arithmetic dependency. Canonical fraction normalization is a separate
feature; changing the natural representation does not itself put every
rational in lowest terms.

NUM2 owns these new carriers, arithmetic, algebraic laws and default APIs.
The [reals roadmap's R1](reals-roadmap.md#milestones) consumes them: it owns
their decidable orders and ordered-ring/field laws, `PosRat`, the
Archimedean property and later canonical presentations. R1's order
work remains proposed under [first action 8](work-plan.md#first-actions);
NUM2 does not wait for it. R2 and the later real constructions target the
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
future number-system constructions use `BNat` by default. Implement
decimal/binary literal parsing, printing, numerical casts and numeral
interpretation directly over binary values. In particular, a large numeral
must not first become a unary `Nat` merely to enter a binary-backed ring.
Adapt the current numeral-rule and `CommRing.of_nat` paths with a binary
entry point and checked agreement; use repeated doubling/bit operations
where appropriate. Retain explicit `UNat` conversions for compatibility
and structural arguments. Specify the `Nat` name and notation migration
before switching aliases; the binary storage of `Z` and `Q`
does not depend on that spelling decision.

**Acceptance:** the default `Z` representatives contain `BNat` components,
and default `Q` fractions contain the resulting `Z`; the ring/domain/field
laws and numerical embeddings check without new assumptions. Arithmetic,
literals and rendering work on large binary magnitudes without allocation
proportional to their unary value. Update consumers and notation for the
new APIs; keep the archive checking under the documented imports and
unary-natural compatibility policy.
Record the new library's source-representation gains separately from
evaluator gains.

### EVAL2: preserve sharing during full normalization

[Weak heads](../../kernel/src/term_normalize.c) are already cached, but
`ck_normal` traverses every remaining child on each call. Cache completed
normal forms by exact immutable syntax identity, with scope/state included
where required. Never publish an in-progress or failed result. Account for
memory and invalidation across rollback and compaction, including normal
forms that create nodes before a later computation fails.

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

### EVAL5: demand only the result being observed

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
measurement baseline. Patterns currently match `result.normal`, after full
normalization: a `_` hole saves no evaluation work. Thus the existing form
`evaluate euclid(4) expecting (5, _)` still encounters the normalization
failure, with the same counters as plain `euclid(4)` in the baseline.
EVAL5 must specify any observation mode that lets this pattern
avoid forcing the certificate, including its checking and failure contract,
before changing evaluation behavior. Preserve exact expected-value checks,
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

The archive's [divisibility test](../../archive/first-library/primes.cubist)
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
foundations, never on archived `primes`. Keep the archived modules intact
as the fixed workload for EVAL0–EVAL5 comparisons.
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
of the closure evaluator.
EVAL2 can proceed independently once its cache contract is clear. Design
EVAL3/EVAL4 together, then specify EVAL5's observation interface and complete
the relevant EVAL8 review before a runtime becomes a default path.
Re-profile the binary-backed constructions before investing in EVAL6.
EVAL7 follows NUM1 and keeps its measurements separate from both the
new numerical library and the unchanged-source evaluator comparison.
Mathematical coverage, resource behavior and the output contract gate
promotion; a faster prime projection
alone does not.
