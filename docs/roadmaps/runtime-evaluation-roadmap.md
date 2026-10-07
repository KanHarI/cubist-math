# Runtime evaluation and binary numerical foundations

Status: planned on 2026-10-07, following a local investigation at
`825c8b8896e02364e9d5cd53f5079014362738ab`. The early numerical foundation
is `UNat` and `BNat`, with binary naturals underlying `Z`, `Q` and later
numerical constructions. None of the NUM or EVAL packages below is
implemented. A scratch evaluator supplies feasibility evidence only.
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

## Preliminary measurements

The investigation used Node 24.13.0 on macOS/arm64, Apple M3 Pro. Each
expression used a fresh program with its imports already checked. These
are individual observations, not benchmark medians or portable targets.

| Existing evaluation path | Observation |
| --- | --- |
| REPL `evaluate euclid(3)` | About 450 ms; two normalizations and 258,730 kernel instructions during the entry |
| `print(evaluate(euclid(3)))` | About 30 ms; one normalization and 12 kernel instructions during the entry |
| REPL `evaluate euclid(3).1` | About 6 ms; result `7` |
| REPL `evaluate euclid(4).1` | Normalization fails at syntax depth 512; about 136,000 new syntax nodes |

The REPL's [evaluate method](../../web/repl-session.mjs) builds
`evaluate e expecting e`. The [translator](../../web/translator/translate.mjs)
then verifies and normalizes both sides, and asks for checked equality of
their types and normal forms. Rechecking the expanded certificate accounts
for much more work than computing its first normal form. The print path
already checks and normalizes once, without the self-comparison.

A separate, uncommitted JavaScript experiment evaluated checked syntax
with environments and memoized thunks. It kept lambda domains, pair types,
eliminator motives and unused fields suspended. It supported the ordinary
data operations used by this workload and refused unsupported operations;
it did not implement general H1 elimination or cubical computation.

| Prime component requested | Scratch result | Evaluation time |
| --- | --- | --- |
| `euclid(3).1` | `7` | About 3 ms |
| `euclid(4).1` | `5` | About 17 ms |
| `euclid(5).1` | `11` | About 1 s |
| `euclid(6).1` | JavaScript call-stack overflow | No successful result |

The successful runs allocated runtime closures but no new kernel syntax
nodes. They did not normalize or certify the returned proof fields.
Preserve a versioned experiment and repeat the measurements in EVAL0
before treating these observations as a reproducible performance baseline.

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
  and an explicit compatibility path for the existing `Nat` APIs.
- `BNat` is the binary natural number type, with a canonical zero and
  nonzero bit representation. Its arithmetic operates on bits directly.
- `BNat` is the default foundation for numerical constructions. In
  particular, `Z` is built from pairs of `BNat`, and `Q` is the field of
  fractions of that binary-backed `Z`. They must not implement arithmetic
  by converting magnitudes through `UNat`.

The existing library's [integers](../../library/integers.cubist) use pairs
of unary `Nat`; its [rationals](../../library/rationals.cubist) use the
resulting integer ring. Migrating both is an early deliverable, not a
possible optimization deferred until runtime specialization. Retaining
unary indices for induction does not make them the representation of
integer magnitudes or rational numerators and denominators.

Naturals form commutative **semirings**, not rings: they have no additive
inverses. The required `UNat`/`BNat` isomorphism therefore preserves zero,
one, addition and multiplication as a commutative-semiring isomorphism.
Establish nontriviality, additive cancellation, multiplicative cancellation
by a nonzero factor, and absence of zero divisors. Extend the induced
isomorphism to the integer constructions as rings, preserving their
integral-domain properties, and to the rational constructions as fields.
This supplies the ring/domain comparison at the appropriate level.

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

All rows are planned. Sizes are relative scope, as in the work plan.

| Package | Deliverable | Dependencies | Size |
| --- | --- | --- | --- |
| EVAL0 | Reproducible workload and phase measurements | Existing CLI, counters and build stamps | S |
| EVAL1 | One-pass REPL evaluation | EVAL0 | S |
| NUM0 | Explicit UNat and canonical BNat with direct binary arithmetic | Current inductive declarations; archive evidence | M |
| NUM1 | Checked semiring isomorphism and natural-number properties | NUM0; semiring model interface | M |
| NUM2 | Binary-backed Z and Q, default numerical APIs and migration | NUM1; current quotients, rings and fractions | L |
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

### EVAL1: remove redundant REPL work

Route plain REPL evaluation through one checked normalization and display,
sharing the existing print path where appropriate. Retain exact expected
value checks for source directives that actually supply an expected value.
Preserve notation selection, assumption diagnostics, scratch-entry lifetime,
failed-entry recovery and browser/CLI agreement.

**Acceptance:** one normalization for a successful plain evaluation;
the same displayed values and assumption refusals; the Euclid self-equality
instruction overhead disappears. This package does not claim to fix the
syntax-depth failure.

### NUM0 and NUM1: representations and checked algebraic agreement

Expose the existing unary naturals as `UNat`, with a documented compatibility
policy for `Nat`, constructor names and imports. Define `BNat` with one
representation of zero and no redundant leading-zero forms. Implement
successor, addition, multiplication, equality and comparison directly over
bits, plus named conversions in both directions. Prove both round trips,
setness and preservation of zero, one, addition and multiplication.

Add the necessary commutative-semiring interface alongside the existing
algebraic hierarchy and construct its two models and their isomorphism.
Prove or transfer cancellation, nontriviality and no-zero-divisors through
the checked maps. Also prove comparison/order agreement for the algorithms
that use it; a bare equivalence of carrier types is not enough. Conversions
remain explicit computational functions. An isomorphism must not be treated
as definitional equality by the checker.

**Acceptance:** both representations and their operations are available
without the new evaluator; conversion and arithmetic laws check without
new assumptions; canonical binary boundary/carry cases compute; numerical
operations use bit recursion without a hidden unary round trip. Preserve
the existing unary induction API through the documented migration policy.
The archive remains a compatibility corpus, not a library dependency.

### NUM2: make Z and Q binary-backed by default

Construct `Z` from pairs of `BNat`, using the existing same-difference
relation and quotient approach with binary addition and multiplication.
Construct `Q` as fractions over this `Z`, retaining its nonzero-denominator
evidence and existing quotient semantics. Canonical fraction normalization
is a separate feature; changing the natural representation does not itself
put every rational in lowest terms.

Build the comparison maps to the former unary-backed integers and
rationals. Prove that they respect quotient relations, round-trip, preserve
ring/field operations and the integral-domain properties needed by the
fraction construction. Reuse or state the domain properties explicitly;
do not assume an `IntegralDomain` theory is already present in the library.
Use the equivalences to migrate statements and certificates without
pretending the old and new carriers are definitionally equal.

Make ordinary numerical APIs, integer magnitudes, rational components and
future number-system constructions use `BNat` by default. Implement
decimal/binary literal parsing, printing, numerical casts and numeral
interpretation directly over binary values. In particular, a large numeral
must not first become a unary `Nat` merely to enter a binary-backed ring.
Adapt the current numeral-rule and `CommRing.of_nat` paths with a binary
entry point and checked agreement; use repeated doubling/bit operations
where appropriate. Retain explicit `UNat` conversions for compatibility
and structural arguments. Specify the `Nat` name and notation migration
before switching aliases; the choice of binary storage for `Z` and `Q`
does not depend on that spelling decision.

**Acceptance:** the default `Z` representatives contain `BNat` components,
and default `Q` fractions contain the resulting `Z`; their public laws and
computability remain checked. Arithmetic, literals and rendering work on
large binary magnitudes without allocation proportional to their unary
value. Check existing library consumers, notation selection and archive
compatibility, with explicit conversions where representations differ.
Record this source-representation migration separately from evaluator gains.

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
Keep the `evaluate ... expecting ...` comparison contract explicit, including
any separately introduced expected-value patterns.

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
with tighter bounds and an explicit early-exit structure. Candidate-divisor
bounds such as the square root require their mathematical proof. Preserve
the least-divisor behavior if replacing this construction, or expose and
name a different algorithm separately. Factorial remains the source
algorithm's growth factor; do not silently replace Euclid's construction
with an unrelated prime generator to improve its benchmark.

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

Start with EVAL0 and EVAL1, and start NUM0/NUM1 alongside them. NUM2's
binary-backed `Z` and `Q` follow the checked semiring agreement; these are
early numerical foundations, independent of the closure evaluator.
EVAL2 can proceed independently once its cache contract is clear. Design
EVAL3/EVAL4 together, then specify EVAL5's observation interface and complete
the relevant EVAL8 review before a runtime becomes a default path.
Re-profile the binary-backed constructions before investing in EVAL6.
EVAL7 follows NUM1 and keeps its measurements separate from both the
representation migration and the unchanged-source evaluator comparison.
Mathematical coverage, resource behavior and the output contract gate
promotion; a faster prime projection
alone does not.
