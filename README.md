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
and UndefinedBehaviorSanitizer. Tests cover successful uses of all 67 opcodes,
invalid handles and premises, context discharge, resource limits, rejected-node
rollback, and deterministic equivalence with inference caching enabled/disabled.
The collision test forces all interning hashes to zero and checks distinct keys,
deduplication, table growth, rollback, and inference validation.

Install [Cppcheck](https://cppcheck.sourceforge.io/) with `brew install cppcheck`
on macOS or `sudo apt-get install cppcheck` on Debian/Ubuntu. `make lint` checks
every C source file, including tests, included headers, and generated proof code.
Warnings, style, performance, and portability findings fail the target; CI runs
the same check. `CPPCHECK=/path/to/cppcheck make lint` selects another installation.

The type-checking kernel is isolated in [`src/kernel/`](src/kernel/). Its
[review guide](src/kernel/README.md) explains the validation path, rule notation,
context discharge, storage invariants, substitution, and compatibility limits.

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
