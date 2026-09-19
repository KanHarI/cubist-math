# Compiler optimization experiments

MathScript compiler optimizations are independently selectable. They change
which checked instructions the compiler emits; the kernel's inference rules
and axiom policy stay the same. Both options are enabled by default.

| Optimization | CLI flag | What it reuses |
| --- | --- | --- |
| Normal-form reuse | `--reuse-normal-forms` | Checked normalization results, including intermediate terms and the resulting normal form. Cache entries distinguish kernel judgments, recorded axiom dependencies, and beta-only versus definition-unfolding reduction. |
| Instruction memoization | `--memoize-instructions` | A previously checked instruction with the same operation, named premises, and context arguments. |

For a focused proof check, defaults enable both. Disable them
independently:

```sh
npm test -- sample_relations
npm test -- --no-memoize-instructions sample_relations
npm test -- --no-reuse-normal-forms sample_relations
npm test -- --no-reuse-normal-forms --no-memoize-instructions sample_relations
```

The proof viewer exposes the options separately near the top and rechecks
the proof when the selection changes. Your saved checkbox choices take
precedence over the defaults. Exported traces contain ordinary kernel
instructions and can be replayed without enabling compiler optimizations.
Recorded `construction` programs already specify their instructions; the
viewer disables these compiler options for them.

Fresh-context indexing is ordinary compiler behavior, with no flag or UI
toggle. It maintains an index of existing variable contexts and replaces
repeated scans of all bindings while selecting exactly the same fresh
variables. It remains active with either or both instruction caches disabled.

## Measure each optimization

The benchmark runs a separate process for each configuration, sequentially,
so an earlier run's WASM heap is not retained by the next run. It checks only
the requested proof sources and their imports, verifies the outputs, and
compares displayed statements and axiom dependencies. With no optimization
flags it measures baseline, each optimization individually, and their
combination:

```sh
node tools/benchmark-compiler.mjs sample_relations
node tools/benchmark-compiler.mjs --replay sample_relations
node tools/benchmark-compiler.mjs --reuse-normal-forms --memoize-instructions sample_relations
node tools/benchmark-compiler.mjs --json sample_relations
```

`--replay` additionally checks the entire emitted trace in a fresh kernel.
Instruction totals and per-operation differences are deterministic for a
fixed source and compiler configuration. Elapsed times are measurements of
individual runs and vary with machine load; fewer instructions do not imply
an equal percentage reduction in time or memory.

During the context-index experiment, `sample_tagged` and its imports measured:

| Configuration | Kernel instructions | Reduction from baseline | Compilation |
| --- | ---: | ---: | ---: |
| Old baseline, full context scans | 457,688 | — | 13.49 s |
| Normal-form reuse, full context scans | 419,678 | 8.3% | 12.84 s |
| Instruction memoization, full context scans | 282,139 | 38.4% | 9.20 s |
| Context index, caches disabled | 457,688 | 0% | 1.66 s |
| Context index and both caches | 244,439 | 46.6% | 1.40 s |

All five traces were replayed successfully, with identical displayed result
statements and axiom dependencies.
The benchmark now always uses the context index, including for its baseline;
the full-scan measurements above describe the earlier implementation.

The larger `curve_tag_stability` development checked and replayed with
1,211,134 instructions, compared with its previously checked baseline of
2,752,249 (56.0% fewer). Its dependencies remained `lib_Trunc` and
`lib_trunc_intro`. Before context indexing, compilation with both instruction
caches took 247.78 seconds and replay took
5.06 seconds. It still produced 767,529 distinct kernel judgments: the main
saving is in repeated instruction emission, not the mathematical content.

CPU profiling of `curve_contour_limits` with the two instruction caches
enabled identified repeated fresh-context lookup as roughly 93% of sampled
time. Enabling the context index reduced measured compilation from 338.69
seconds to 9.17 seconds (about 37 times faster). Both runs emitted 1,371,581
instructions and produced 868,820 kernel judgments, with identical statements
and axiom dependencies. The indexed trace also replayed in a fresh kernel in
4.61 seconds. The index changes context lookup, not proof size or the rules
used to check a proof.

The focused regression suite also replays small baseline and optimized
programs into the same kernel and verifies each proof against both versions
of its statement. It covers dependent types, opaque conversion, recursive
functions, axiom dependencies, and rejection of invalid proofs.

## Boxing and future experiments

Theorems already use boxed kernel definitions. Ordinary `def` declarations
are transparent; `opaque def` keeps a named definition folded and supports
checked unfolding when conversion needs it. These optimizations do
not change these language semantics.

Automatically boxing ordinary definitions requires a separate experiment:
smaller terms may help, but additional conversion witnesses and unfolding
can also increase the instruction count. Any such optimization should have
its own control and measurements before it is enabled for larger proofs.

A bounded prototype boxed every ordinary definition using the existing
kernel rules. With both reuse options enabled, `basics` still verified but
grew from 186 to 233 instructions. `sample_relations` stopped at a checked
dependent conversion: its compiler descriptors and the folded kernel domain
did not agree. Extending the conversion fallback exposed the same issue at
dependent function application. The prototype was reverted. A viable approach
needs application and conversion to coordinate selective unfolding, such as
reducing only enough to expose a function's outer type constructor.

Boxing individual concepts already works where existing conversion supports
them: changing only `InfinitelyManyPrimes` to `opaque def` still verified
Euclid's theorem. Its expression became a `DRef` instead of an expanded `Pi`,
but the trace grew from 22,589 to 22,614 instructions for the required
conversions. This experiment was not applied to the source library. A smaller
displayed expression alone does not establish a reduction in compilation
work or memory; the kernel already shares structurally identical subterms.

## Inspector readability

Checked declarations default to **Kernel notation (folded)**. For example,
`InfinitelyManyPrimes` is typeset with dependent products and sums as
`Π (n : Nat), Σ (p : Nat), Prime(p) × isLt(n, p)`. Native MathML supplies the
mathematical layout; no external rendering service is needed. Definition
names open their inspection, including the existing source-navigation link.
Kernel details are open by default. Long binder chains are laid out on separate
lines so dependent types remain readable.

The **Context** section lists the checked open assumptions and their types.
Click an assumption's name, including a reference to it in another type, to
inspect its own judgment and navigate to its source. These are the kernel's
actual context entries; variables bound inside a term by Π, Σ, or λ remain
internal binders. A closed judgment therefore has an empty context even when
its expression contains such binders.

Axiom leaves retain their checked identities and link to the corresponding
axiom inspection. The truncation notation toggle displays a fully applied
propositional truncation as `‖A‖`; disabling it exposes the named axiom
application, including its universe argument. This is display notation only:
it does not replace the checked term or alter workbench exports.

**Group independent binders** abbreviates consecutive Π binders, or consecutive
Σ binders, when their domains do not refer to earlier members of the group.
For example, `Π (zero, one : F; lt : F → F → 𝒰₀)` abbreviates three
successive Π binders. Equal domains are shared only when their kernel
structures match after accounting for binder depth. The earlier binder
declaring `F` stays separate.
Dependencies are read from kernel variable indices, not display names.
Ambiguous groups involving reused display names stay separate as well.
Grouping preserves binder order and never mixes Π with Σ; turn it off to see
each binder separately. This notation does not replace the term with a single
binder over a product type or change its checked derivation.

This view is an actual kernel term with checked definition references, not
MathScript text rewritten with mathematical symbols. The successful source
snapshot proposes a shape for the folded term. A separate kernel replays the
required premises, constructs the proposed term with ordinary formation and
application rules, and proves a `DefEq` judgment connecting it to the stored
term. Only the resulting kernel AST is rendered. The kernel's binder-index
convention applies to domains as well as codomains; product and arrow notation
is used only when the anonymous binder is absent from the codomain.

**Download folding certificate** exports the replayable instructions and the
names of both terms and their checked definitional-equality witness. Folding
does not change the original proof engine, instruction count, axiom list, or
proof export. Unsupported forms or failed comparisons fall back to the stored
kernel term. The source-derived folding proposal is never treated as evidence.

Each expression and type has an **Open in workbench** action. It opens a new
tab, replays the required checked instructions under the same axiom policy,
and selects the transferred term. A folded expression retains its certified
folded type by an explicit kernel type rewrite. Definitions can then be
unfolded, applications beta-reduced, and dependencies inspected with the usual
preview/accept workflow. The original mathematical proof is unaffected.
The transfer uses same-origin IndexedDB rather than putting large proof traces
in a URL or sessionStorage; it is removed after successful import.

Raw rendering also names the binder slots introduced by eliminators such as
`nat.elim [x1, x2]. ...`. These slots are part of the kernel's de Bruijn
indexing, including its depth convention for every constructor child. Omitting
them previously caused valid bound variables to appear as unexplained `#6`
or `#3` references. Expression-selection paths still refer to the original AST.

The separate **MathScript (folded)** option retains the successful source
snapshot. **Raw kernel term** and **Show full term** retain the stored
representation without display folding. Imported declarations use the same
checks, and failed proof checks preserve the previous successful snapshot.
