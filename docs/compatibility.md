# Compatibility and proof provenance

Source: `KanHarI/thth`, commit
`79060d57eacdf42cd2b4762b2b4bfa3a530f0861` (2025-02-13).
File hashes are in [proof_sources.json](proof_sources.json).

## Ported material

`tools/port_proofs.py` translates 24 construction functions into C: 21 builtin
functions, the dependent `create_pr1_pr2` helper, and the composition and product
commutativity theorem tests. They call `tt_apply` for each original inference.
The builtin configuration includes the W-natural-number construction and
exports 50 judgements.

The port covers all 67 implemented inference opcodes and preserves their numeric
labels and premise/context metadata. `Nop` is a driver action rather than an
inference opcode. The C tests execute at least one successful instance of every
implemented opcode and check computation-rule results as well as theorem types.

The proof generator intentionally supports the small construction language used
by this source revision. It fails on unsupported statements; it is not a general
Rust-to-C compiler. The generated C is checked in and can be read independently.

## Checked compatibility

The Rust oracle in `bench/` replays traces emitted by the C kernel against the
original Rust inference implementation. It compares legality and normalized
64-bit fingerprints of expressions, types, and context-dependency sets. Reference
hashes are normalized to trace-local IDs before comparison. Fingerprints are
regression diagnostics, not trusted proof certificates or cryptographic IDs.

The original proof programs replay before the additional C opcode-coverage tests.
The frozen trace and its verification summary live under `tests/`. CI rebuilds
the C trace and checks it against that reference. Re-running the independent Rust
oracle requires access to the private source repository:

```sh
python3 bench/prepare_rust_baseline.py /path/to/thth /tmp/thth-reference
python3 bench/prepare_oracle.py /tmp/thth-reference
cargo build --release --manifest-path /tmp/thth-reference/Cargo.toml --bin oracle
TT_TRACE_FILE=/tmp/proof.trace build/test
/tmp/thth-reference/target/release/oracle /tmp/proof.trace
```

For Apple's system Python, the executable may additionally need
`DYLD_FRAMEWORK_PATH` set to the directory containing `Python3.framework`.

## Deliberate differences

* **Storage identity:** expressions use interned DAG IDs. Judgements are deduplicated
  by expression, type, assumptions, and highlight state; contexts by type,
  assumptions, and counter. The first checked derivation is retained. Upstream's
  hashes also encode proof history, so raw IDs and judgement counts do not match.
* **Failure handling:** malformed IDs, argument counts, illegal premises, resource
  exhaustion, and invalid highlights return statuses. They do not intentionally
  panic or dereference missing context handles.
* **Limits:** expression/depth/storage bounds are enforced by the C API. Large
  builtin construction temporarily lifts the final expression-size bound.
* **No Python bindings or model code:** this repository is the inference engine,
  proof library, C API, CLI, and benchmarks. AST/judgement inspection supports
  downstream consumers without importing the neural-network training stack.

## Computation-rule defects corrected during the port

The additional opcode tests revealed upstream rules whose implementation
does not construct the judgement described by its own inference-rule comment:

1. **`EqComp`:** Rust substitutes into the motive's `_type` (its universe), using
   the witness's `_type`, instead of substituting the witness expression into the
   motive expression. C constructs the result type from the motive and witness.
   For a constant `Unit` motive, the result has type `Unit`, not `U_0`.
2. **`WComp`:** Rust legality checks four premises (motive, branch, label, arity),
   but `apply_impl` treats the third premise as an already constructed `WSup`
   expression and can panic. C constructs `WSup(label, arity)` from premises three
   and four, then constructs the recursive argument to the branch. C's W beta
   reduction uses the corresponding recursive lambda rather than the upstream
   nonrecursive application.

The Rust oracle explicitly skips these corrected computation steps, W beta
reductions, and dependent
steps whose outputs have no pre-existing reference mapping. Those cases are
covered by direct C computation tests. They are not claimed to match the faulty
Rust output. None of the original ported proof programs needs either defect.

The WNat-to-Nat equivalence additionally exposed:

3. **Dependent Nat induction:** `NatElim`, `NatCompZ`, and `NatCompS` now require
   the successor branch to have type `C(succ(n))`, while its induction hypothesis
   has type `C(n)`. Upstream incorrectly checks both against `C(n)`. Positive and
   negative native tests exercise all three rules, including wrong IH types.
4. **Nat beta under binders:** a recursive call retains the Nat node's two
   virtual binder levels; its predecessor and zero branch leave those levels.
   Applying one negative shift to both predecessor and recursive hypothesis
   captured outer variables. Tests compare normalization before/after abstraction.
5. **W recursive argument:** the child variable is index 2 inside the newly
   constructed `IndW`, under the retained node-wide depth convention. Index 0
   failed to substitute the recursive lambda's argument. W beta also lowers
   constructor arguments when they leave the original eliminator. The native
   regression uses an arbitrary child function, not just constant children.

The four changed W computation/reduction fingerprints in the reference fixture
were already excluded from Rust parity; `tests/reference_verification.json`
records their line numbers. All other 3,648 trace records remain unchanged.
New Nat regressions run separately from that frozen compatibility trace.

The AST traversal retains upstream's node-wide binder-depth convention. These
fixes and regression tests do not constitute a foundational soundness proof.

## Concurrency and lifetime

One engine is owned by one thread at a time. Multiple engines are independent.
IDs and inspected values remain valid until that engine is freed. The library
does not perform hidden garbage collection or invalidate accepted IDs. Failed
inferences roll back only newly allocated temporary expression nodes.

