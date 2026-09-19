# THTH C

A C11 implementation of a type-theory proof checker. Independent engines can run concurrently.

The port includes all 67 inference opcodes, the composition and product
commutativity proofs, the dependent projection proof helper, and the builtin construction programs. The full builtin configuration exports 50 checked
judgements, including the same explicitly declared axioms as upstream.

## Build and test

```sh
make -j4
make test
make collision-test
make lint
build/thth proofs
```

Use a C11 compiler and Make. On Linux, `make CC=clang sanitize` runs AddressSanitizer
and UndefinedBehaviorSanitizer. Tests cover successful uses of all 75 opcodes (67 upstream and eight suspension/transport rules),
invalid handles and premises, context discharge, resource limits, rejected-node
rollback, and deterministic equivalence with inference caching enabled/disabled.
The collision test forces all interning hashes to zero and checks distinct keys,
deduplication, table growth, rollback, and inference validation.

Install [Cppcheck](https://cppcheck.sourceforge.io/) with `brew install cppcheck`
on macOS or `sudo apt-get install cppcheck` on Debian/Ubuntu. `make lint` checks
every C source file, including tests, included headers, and generated proof code.
Warnings, style, performance, and portability findings fail the target; CI runs
the same check. `CPPCHECK=/path/to/cppcheck make lint` selects another installation.

The type-checking kernel is isolated in [`src/kernel/`](src/kernel/). The
[mathematician’s reading guide](docs/kernel.md) explains the C notation through
inference rules, a complete proof example, and the context and binding conventions.
Its
[review guide](src/kernel/README.md) explains the validation path, rule notation,
context discharge, storage invariants, substitution, and compatibility limits.

## Interactive workbench and CLI

The proof workbench runs the C kernel as WebAssembly, with clickable expressions,
isolated previews, explicit acceptance, branching history, and save/replay.
The CLI uses the same interpreter and supports both named/numeric paths and
selection by adding parentheses around a displayed subexpression. Both start
with all 50 prelude library exports, including `LEM` and `AOC`. The browser proof
selector and CLI `proofs` / `open ID` expose every original proof construction
and the identity example as 28 checked, editable replay programs, including `open wnat_equiv` for
a verified WNat-to-Nat `isEquiv` proof.

```sh
make wasm       # Requires Emscripten; detects .tools/emsdk automatically
make cli        # Requires Node.js 24+
make serve      # Browser: http://127.0.0.1:8088
```

During development, select the relevant proofs or regression tests:

```sh
npm test -- complex_inverses
npm test -- --module ordered_squares
npm test -- web/proofs/complex_polynomials.proof
npm test -- --changed
npm test -- tests/workbench.test.mjs
npm test -- --test-name-pattern="complex inverses"
npm test -- --help
```

Module names and `.proof` paths check only those proofs and their transitive
imports, reporting kernel steps and axiom dependencies. `--changed` selects
added or modified proof sources, including staged and untracked files; it does
not select JavaScript, browser or C tests. Use a test file or name filter for
the relevant mutation and implementation regressions. Plain `npm test` runs
the complete regression suite for the final check; `npm run test:browser` runs
the browser checks separately.

MathScript offers separate `--reuse-normal-forms` and `--memoize-instructions`
flags for selected proof checks and `cli/repl.mjs`, with matching proof-viewer
toggles near the top. Both default on; add `no-` after `--` to disable an option
individually. Fresh-context indexing is always enabled. See
[compiler optimization experiments](docs/compiler_optimizations.md) for
measurements and comparison commands.

See the [workbench and CLI guide](web/README.md) for SDK setup, examples,
source syntax, resource bounds, and current limitations.

## Mathematical proof sources

The [high-level language](docs/mathscript.md) supports named definitions, dependent
functions, induction, pattern matching, and explicit proof blocks. Read and inspect
sources at `http://127.0.0.1:8088/proof.html?proof=euclid` or `?proof=circle` after
`make serve`. Sources live in [`web/proofs/`](web/proofs/); `.proof` files contain
mathematical programs, while `.construction.proof` files preserve kernel audit steps.

The [circle development](docs/circle_fundamental_group.md) constructs
`S1 = Suspension(Unit or Unit)` and checks its fundamental group is isomorphic to
integer addition. Its proof and supporting lemmas are high-level source; the C
extension implements general suspension rules only.

The [group structure identity development](docs/group_identity.md) proves
`(G = H) ≃ GroupIso(G, H)` for bundled small groups, with both canonical inverse
laws. Applying it to the winding isomorphism gives an actual equality of the
circle loop group and the integer group. It uses univalence and function
extensionality, without choice or excluded middle.

The [finite counting development](docs/finite_counting.md) constructs `Fin(n)`
from sums of Unit and proves the binomial, permutation (`k!`), and function
(`m^n`, including `k^k`) counts. Open `?proof=binomial_counting`,
`?proof=permutations`, or `?proof=function_counting` in the source explorer.
Each result lists its own axiom dependencies, with links to their declarations.

The [surjection development](docs/surjections.md) proves that every surjection
between sets has a right inverse, using the existing axiom of choice. Open
`?proof=surjections` to inspect the proof and its explicit axiom dependencies.

The [Cantor–Schröder–Bernstein proof](docs/schroeder_bernstein.md) constructs a
full equivalence from injections each way between sets, using excluded middle
and no choice. Open `?proof=schroeder_bernstein` in the source explorer.

The [real-number development](docs/reals.md) adds a constructive shared
ordered-field and Cauchy-completeness interface, with Dedekind completeness
separate. Dedekind cuts, classical Boolean conversion, and the ordinary Cauchy
quotient have checked preliminary lemmas; their complete field instances remain
under development. Open `?proof=complete_fields` in the source explorer.

The [puncture homotopy development](docs/puncture_homotopy.md) proves that every
loop in a finite puncture graph merely has a signed-word representation, and
that cancellative loop invariants are determined by generator values. A checked
nontrivial commutator has zero winding around both punctures. Open
`?proof=bouquet_generation` or `?proof=puncture_noncommutative`; the comparison
with continuous complex contours remains to be proved.

The [complex algebra development](docs/complex_analysis.md) constructs the
complex commutative ring over a supplied real ring, proves the conjugate and
inverse formulas, and checks polynomial difference and factor identities.
Open `?proof=complex_algebra` or `?proof=polynomial_difference`. Algebraic closure
and Great Picard are development targets, not established theorems.
Complex-analysis work is currently paused; the
[development handoff](docs/complex_analysis_handoff.md) records the checked
results, remaining obligations and how to resume.

The winding route now has checked [circle-degree obstructions](web/proofs/circle_degree.proof)
and [zero-avoiding linear deformations](web/proofs/complex_deformation.proof).
A positive-degree circle map cannot extend through a contractible homotopy
type; a dominating complex term remains nonzero as the smaller term is
introduced. Geometric comparison, continuity, and polynomial radius bounds
remain to be proved.

The [puncture period formula](web/proofs/puncture_periods.proof) now proves
that every additive invariant of a loop in the puncture homotopy type is the
sum of its winding numbers times its generator values. It is also
[specialized to complex addition](web/proofs/complex_periods.proof). This is
the homotopy part of the residue argument; general contour integration and the local
residue calculation remain to be constructed and proved.

[Limit and descent proofs](docs/analysis_limits.md) now construct additive
homotopy periods from Cauchy approximations on representatives, provided the
homotopy and concatenation errors tend to zero. Mere coverage suffices; no
representatives are chosen. [Finite contour sums](docs/contour_sums.md) now
have checked composition, linearity, telescoping, and refinement-error laws,
including their complex specialization. Scalar tag errors are bounded by
the uniform sampled error times the sum of edge-magnitude bounds; they tend
to zero when those bounds do. The complex coordinate version now proves
that changing tags preserves an existing limit when sampled errors tend
to zero and coordinate variation is bounded. [Geometric interval curves](docs/complex_curves.md)
now include uniformly continuous straight segments and their endpoints, with
zero avoidance under the squared-norm domination condition.
Their ordered interval samples have checked coordinate variation bounds
independent of the number of sample points.
The actual affine dyadic sums now have a checked Cauchy modulus when supplied
actual Archimedean bounds. Completeness constructs their unique limit, and
splitting at the constructed midpoint splits that limit into a sum. The
constructed integrals are complex-linear in the integrand, with continuity
witnesses built for sums and scalar multiples. These
results preserve constructive assumptions; comparison with arbitrary fine
partitions and homotopy invariance remain to be proved.
The parameter samples now map to the original contour sums; the affine
tag-independence proof supplies those variation bounds itself.
Uniform continuity along the curve now yields a positive mesh threshold
controlling all admissible tag changes, including the constructed left- and
right-endpoint sums.
Arbitrary finite subdivisions of a coarse affine interval now have a
width-scaled contour-error bound. Subdivisions across a whole partition can
be flattened to one sample list with a checked identity for its sum. The
global affine refinement bound is now checked: the total error is bounded by
the tolerance times outer width times coordinate length, independent of the
number of coarse edges or refined samples.
Recursive midpoint bisection now gives exact edge counts and mesh bounds;
Archimedeanness yields mere existence of admissible samples below every
positive mesh, without choice or excluded middle.
Widths remain small at every later level. Actual scalar convergence moduli
are checked when explicit Archimedean bound functions are provided.
Convergence for general contour sampling schemes, the required homotopy
estimates, and the comparison of geometric curves with homotopy paths remain
open.

The [Euclid argument](web/proofs/euclid.proof) imports its
[arithmetic and prime-number foundations](web/proofs/primes.proof), all checked
from mathematical source without axioms. [Basic examples](web/proofs/basics.proof)
introduce functions, pairs, and induction. In the CLI, use
`prove web/proofs/euclid.proof`, then the usual `use`, `select`, `children`,
`reduce`, and `check` commands. Override the local port with `make serve PORT=8090`.

## Performance design

* Immutable, hash-consed expression DAGs with 32-bit engine-local IDs. Structural
  equality is an ID comparison; hash collisions are resolved by full key checks.
* Cached subtree sizes, depths, and occurrence flags. Unaffected subtrees are
  reused during binding and substitution.
* Memoized AST transformations and reductions, plus a bounded cache of successful
  and unsuccessful inference requests.
* Canonical shared context sets and semantic judgement deduplication. The first
  checked derivation is retained instead of storing each redundant proof path.
* Rejected inference attempts roll back newly allocated AST nodes and invalidate
  affected transformation-cache generations.
* Small initial caches for short proofs, growing caches for long runs, and one
  independent engine per worker. No global mutable engine state or shared locks.



## C API

Link `build/libthth.a` and include [`thth.h`](include/thth.h):

```c
#include "thth.h"

int main(void) {
    tt_engine *engine = tt_new(NULL);
    if (!engine) return 1;
    tt_id proposition, proof;
    bool ok = tt_prove_composition(engine, &proposition, &proof);
    if (ok) tt_print_judgement(engine, proof, stdout);
    tt_free(engine);
    return ok ? 0 : 1;
}
```

```sh
cc -std=c11 -Iinclude example.c build/libthth.a -o example
```

`tt_apply` validates opcode arity, IDs, context discharge, and rule-specific
premises before publishing a judgement. It returns `TT_OK`, `TT_INVALID`,
`TT_LIMIT`, or `TT_OOM`; failed calls return result ID zero. `tt_opcode_metadata`
describes each opcode's arguments. `tt_judgement` and `tt_ast` expose expressions
and types for downstream tensorization. IDs are stable until `tt_free` and are
local to their engine; they are not upstream BLAKE3 hashes.
IDs are sequential array indexes, not truncated hashes. A separate 64-bit hash
accelerates lookup, with full-key comparisons resolving collisions. Capacity
exhaustion returns `TT_LIMIT` before an ID can wrap; allocation can fail earlier.

Configure expression size, traversal depth, context counters, judgement count,
and AST-node count through `tt_config`. There is no public unchecked judgement
constructor. Axioms are disabled by default. Loading the full upstream builtin
library requires `allow_axioms = true`; its construction temporarily lifts the
expression-size limit, which is restored for subsequent inference.

`tt_verify` checks that both stored judgements are closed, that the proposition
is a type, and that the proof's type equals the proposition. Trust comes from
constructing stored judgements through the kernel, as in upstream.

## Proof provenance and compatibility

The source revision and SHA-256 hashes of the ported proof files are recorded in
[`docs/proof_sources.json`](docs/proof_sources.json) and
[`docs/compatibility.md`](docs/compatibility.md). Generated proof programs call the
kernel for every step; they do not import prevalidated theorem conclusions.

Regenerate the proof programs and opcode metadata from an upstream checkout:

```sh
python3 tools/port_proofs.py /path/to/thth
make test
```

The Python generator is a development tool only. Its output is checked in, so
ordinary builds require only C and Make. The new engine preserves the binding
conventions needed by the upstream proofs. Documented computation-rule fixes
and differences in IDs, provenance deduplication, and checking behavior are listed
in [compatibility.md](docs/compatibility.md).

## Layout

| Path | Purpose |
|---|---|
| `include/` | Public C API and opcode numbers |
| `src/kernel/` | Checked rules, context discharge, binding, interning, and review guide |
| `src/proofs.c`, `src/proofs_generated.inc` | Original proof programs and builtins |
| `tests/` | Kernel, proof, regression, and determinism tests |

The axiom-free Euclid proof is available with `open primes`, followed by
`check InfinitelyManyPrimes infinitely_many_primes`. See
[the construction and definitions](docs/infinitely_many_primes.md).
