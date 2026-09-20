# Experimental C kernel: first native component

This is a new implementation, isolated from `src/kernel/` and its certificate
format. **Its present native component is the interval and face algebra, not a
complete type checker.** The independently implemented JavaScript reference
also checks Pi/Sigma, Nat induction, paths and composition. Those inference
rules have not yet been ported to C. Glue, universe composition, HITs and the
strict Id bridge remain incomplete in the experiment as a whole.

## Reading the mathematics in the code

| File | Mathematical responsibility |
|---|---|
| `include/cubical.h` | Two distinct sorts, their representation and operation contracts |
| `src/formula.c` | Finite joins of finite meets; absorption and shared storage |
| `src/interval.c` | De Morgan reversal and dimension substitution |
| `src/faces.c` | Endpoint equations, face substitution and entailment |
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
The future type layer should represent universe *levels* separately from terms,
with successor and maximum, retaining `Group(U0):U1` rather than erasing it to a
broad universe sort. Cumulative upward inclusion is not downward resizing.

## Checks and measurements

```sh
make -C experiments/cubical/c test
node --test experiments/cubical/tests/native.test.mjs
make -C experiments/cubical/c BUILD=build-ubsan CFLAGS='-O1 -g -std=c11 -Wall -Wextra -Wpedantic -Werror -fsanitize=undefined -fno-omit-frame-pointer' test
CUBICAL_NATIVE_BUILD=build-ubsan node --test experiments/cubical/tests/native.test.mjs
node experiments/cubical/benchmark.mjs
```

The native invariant tests and 1,800 deterministic cross-implementation requests
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
