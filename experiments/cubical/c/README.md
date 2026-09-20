# Experimental C kernel: dependent terms and interval paths

This is a new implementation, isolated from `src/kernel/` and its certificate
format. **The native checker now implements explicit cumulative universes,
Pi/Sigma, Nat, Unit, Void, sums, general dependent W induction, and interval
paths, and composition.** It independently checks inert input rather than
trusting JavaScript certificates. Composition checks every tube/base equation
and overlap, with native Nat/Unit/Pi/Sigma/Path computation matching the JS
reference.
Native Glue and universe composition now match the independently checked
reference rules. The full theorem that `idtoequiv` is an equivalence, the
strict Id bridge and higher inductive types remain incomplete.
This is not yet the website kernel or a full cubical/library migration.

## Reading the mathematics in the code

| File | Mathematical responsibility |
|---|---|
| `include/cubical.h` | Two distinct sorts, their representation and operation contracts |
| `src/formula.c` | Finite joins of finite meets; absorption and shared storage |
| `src/interval.c` | De Morgan reversal and dimension substitution |
| `src/faces.c` | Endpoint equations, face substitution and entailment |
| `include/cubical_kernel.h` | Opaque arena, raw handles and checked-result API |
| `src/term_store.c` | Inert syntax allocation and bounded handles |
| `src/term_substitution.c` | Capture-avoiding term and dimension substitution |
| `src/term_conversion.c` | Demand-driven conversion modulo bound names |
| `src/term_normalize.c` | Weak-head computation; separate optional normal forms |
| `src/check.c` | Checked telescopes, dispatch and result publication |
| `src/check_functions.c` | Pi/Sigma formation, introduction and elimination |
| `src/check_inductives.c` | Nat, Unit, Void, sums and general W rules |
| `src/check_paths.c` | Dependent paths and reconstructed endpoint annotations |
| `src/face_context.c` | Shared restriction of checked telescopes and face clauses |
| `src/equivalence_terms.c` | Derived contractible-fiber types and identity equivalence |
| `src/check_glue.c` | Checked gluing equivalences, boundaries and overlap coherence |
| `src/glue_compute.c` | Glue composition and derived universe composition |
| `src/check_composition.c` | Restricted contexts, partial boundaries and all overlaps |
| `src/composition_compute.c` | Derived filling and constructor-specific composition |
| `tests/lattice_cli.c` | Inert test input, separate from the trusted algebra |

A clause is a conjunction of generators, represented by two bitsets. A formula
is a disjunction of clauses. Removing a clause that contains another implements
absorption. `positive` and `negative` have different meanings in the two sorts:

- Interval: `i` and `1-i`; their conjunction is allowed.
- Face: `i=1` and `i=0`; their conjunction is impossible.

The empty list is bottom; the list containing an empty clause is top. Joining
formulas concatenates their clauses and applies absorption. Meeting them takes
every pairwise union of clauses and applies absorption. Comments beside each
operation state the corresponding mathematical rule.

Outputs are assembled in private candidates, then published on success. Inputs
may alias outputs. Allocation failure never establishes an equation. Formula
storage belongs to this trusted component; the C structs are not a certificate
format in which untrusted clients may inject arbitrary memory.

The first representation supports 64 distinct dimensions, including dimension
63. Dimension 64 is rejected, never masked to zero. This is a documented native
prototype restriction, not a restriction of cubical type theory. Dynamic
bitsets or a sparse dimension representation are required before removing it.
Universe levels are explicit unsigned integers, with checked successor and
maximum. There is no term-level Universe erasure; level schemas still need a
frontend instantiation mechanism. Cumulative upward inclusion is not downward resizing.

## Checks and measurements

```sh
make -C experiments/cubical/c test
node --test experiments/cubical/tests/native.test.mjs experiments/cubical/tests/native-kernel.test.mjs
make -C experiments/cubical/c BUILD=build-ubsan CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -Werror -fsanitize=undefined -fno-omit-frame-pointer' test
CUBICAL_NATIVE_BUILD=build-ubsan node --test experiments/cubical/tests/native.test.mjs experiments/cubical/tests/native-kernel.test.mjs
node experiments/cubical/benchmark.mjs
```

The native invariant tests and 2,100 deterministic cross-implementation requests
pass. The latter cover reversal, both endpoint equations, interval substitution,
face substitution and entailment. Invalid input and dimension overflow are
rejected. UndefinedBehaviorSanitizer checks also pass.

AddressSanitizer could not run on this macOS 26.5.1 / Xcode runtime. Both
sandboxed and unsandboxed binaries deadlocked before `main`; a process sample
showed `AsanInitInternal -> InitializeShadowMemory -> get_dyld_hdr -> malloc ->
AsanInitFromRtl -> StaticSpinMutex::LockSlow`. The hanging processes were stopped.
This is **not** reported as a successful ASan run. Re-run `make ... sanitize`
with a functioning sanitizer runtime, particularly on Linux CI.

[Recorded measurements](../../../docs/cubical/benchmark-results.json) are only
an algebra microbenchmark: 10,000 repeats of meet, reversal, and endpoint
conversion. The first run measured approximately 5.5 ms CPU / 1.4 MB peak RSS
for C, versus 176 ms / 62 MB for JavaScript. Runtime startup contributes to RSS;
this does not predict whole-proof performance. Univalence transport, circle,
group identity, F4 correspondence and quotient benchmarks remain explicitly
unavailable until the relevant translation and computation rules exist.

## Checked API and compact computation

`cc_kernel_term` only creates inert syntax. `cc_kernel_check` validates the
ordered assumption telescope, infers the term and checks an optional expected
type. Every path application's endpoint annotation is reconstructed internally;
a caller cannot forge an endpoint computation by supplying that annotation.
On failure the entire result is cleared. There is no old-kernel fallback.
Read-only node access supports an inspector with an external table of names.

Checking returns the checked expression and type without normalizing either.
`cc_kernel_normalize` is a separate explicit inspection operation; it does not
certify an arbitrary raw handle. The test CLI accepts a normalization option.
Conversion exposes only needed heads: beta reduction does not evaluate unused
arguments, and W induction constructs child induction hypotheses as functions
without traversing every subtree in advance.

The compactness regression checks a nested doubling expression denoting
4,194,304 at Nat. It allocates 1,329 arena nodes / 65,536 reserved arena bytes,
at the first native checkpoint (355 checking and 1,397 reduction steps there), and ignores it by beta reduction
without constructing the numeral. These bytes measure node/cache reservation,
not whole-process RSS or formula storage. This is not yet the requested
factorial theorem transported by computational univalence: Glue, the checked
Nat/binary equivalence and operation compatibility must be integrated first.

Native inputs and generated terms currently have a 512-node syntax-depth guard,
64 dimension names and a ten-million-step per-request budget. They fail
explicitly when exceeded. These prototype resource limits must be revised for
whole-library production use. The machine-readable constructor protocol is a
test adapter; the opaque C API is suitable for a subsequent WASM binding, which
has not yet been wired into the website.

At this milestone all 79 experimental tests pass. Ten native term tests
cross-check typing/normal forms against the independently implemented JavaScript
rules, include negative typing cases and actual dependent W/finite-sum motives.
The native invariant suite and native and derived-equivalence test files also pass UBSan (38 test
cases, including the 2,100 seeded dimension-algebra comparisons).

Thirteen native composition tests also compare inferred types and normal forms
with the JavaScript reference, and recheck the computed terms independently.
They include neutral path boundaries and transport through a varying function
domain, not just closed numerals. Constructor composition for W and sum types
is also implemented. A neutral composition is retained where no implemented
rule applies. Cubical canonicity for the full language is therefore not claimed.

The latest supporting native rules include universal face quantification and
Sigma eta. Identity equivalences are built from contractible fibers in ordinary
syntax and independently check in both implementations. Ten native Glue tests cross-check formation, projection, eta and actual
transport computation against JavaScript. They also recheck normal forms of
persistent-face and universe-composition examples. This is not yet a complete
univalence theorem or a migrated factorial proof.

Term substitution renames dimension binders when the inserted term contains
free dimensions. The dedicated regression inserts a closed path-producing
function under a dimension of the same name and then applies it to a varying
argument. Empty Glue faces are removed before conversion. Free-name analysis
and substitution consume the same checking budget, so a small shared syntax DAG
cannot cause an unbounded uncounted traversal.

### Checked definitions and demanded heads

`cc_kernel_define(kernel, symbol, value, expected_type)` checks a closed body
using only earlier checked definitions and publishes a folded `CC_DEFREF`
(tag 35). Failure publishes no definition. Definitions are transparent for
conversion, and a separate `cc_kernel_definition` query returns their checked
bodies and inferred types. Source opacity is an elaboration/display decision,
not a new assumption. No unchecked external theorem can enter this registry.

Conversion first compares folded syntax modulo binder renaming, including
matching definition references. It unfolds definitions only when that comparison
fails. `cc_kernel_whnf` exposes the demanded head without strongly normalizing
arguments, and is suitable for an elaborator's type-shape queries. Like the
normalization inspector, it accepts raw syntax but never certifies it; final
`cc_kernel_check` must validate all elaborated results.

The native API regression builds 22 checked applications of doubling and checks
a reflexive path at the compact natural 2^22: **252 arena nodes, 7 checking steps
and 28 reduction steps** for the final check, without expanding its unary value.
This is a compactness regression, not the requested factorial transport proof.
The tests also reject duplicate names, free variables, wrong declared types,
unknown references and equality between distinct numeric definitions.

### Sharing during substitution

Free-name analysis and capture-avoiding substitution memoize exact immutable
syntax keys. This prevents repeated traversal of a shared term as if it were
an exponentially larger tree. The bounded direct-mapped table has 8192 entries;
a hash collision only discards an optimization. It stores no typing judgements
and cannot bypass checking a context or a face restriction. Its allocation is
included in the reported arena memory. Substitution also returns the original
node immediately when the substituted variable/dimension does not occur.

A 24-level shared-DAG regression exercises weak-head inspection. With the source
frontend's independently supplied failing arithmetic fixtures, the default
10-million-step budget now checks binary factorial 7 in 59,153 reduction steps
and the radix fixture in 152,535. Their respective cumulative node counts are
14,681 and 83,238. These are source frontend checkpoints, not yet the final
computational-univalence factorial transfer acceptance test.

### Constructor composition for Sum and W

Both checkers now compute composition through matching sum/tree constructors.
For a W type, they first fill the label, then compose its children as a dependent
function over the varying arity. The native implementation lives in
`src/inductive_composition.c`; the reference implements the same mathematical
rule independently. Tests check empty/nonempty walls, varying label types and
varying arities, and independently recheck the resulting normal terms in both
implementations. A tube whose constructor cannot be exposed stays neutral.
This does not introduce a strict constant-family transport rule or an equality
between arbitrary trees.
