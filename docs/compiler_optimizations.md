# Compiler optimization experiments

MathScript compiler optimizations are independently selectable. They change
which checked instructions the compiler emits; the kernel's inference rules
and axiom policy stay the same. Both options start disabled.

| Optimization | CLI flag | What it reuses |
| --- | --- | --- |
| Normal-form reuse | `--reuse-normal-forms` | Checked normalization results, including intermediate terms and the resulting normal form. Cache entries distinguish kernel judgments, recorded axiom dependencies, and beta-only versus definition-unfolding reduction. |
| Instruction memoization | `--memoize-instructions` | A previously checked instruction with the same operation, named premises, and context arguments. |

For a focused proof check:

```sh
npm test -- --reuse-normal-forms sample_relations
npm test -- --memoize-instructions sample_relations
npm test -- --reuse-normal-forms --memoize-instructions sample_relations
```

The proof viewer exposes the two options separately and rechecks the proof
when the selection changes. Exported traces contain ordinary kernel
instructions and can be replayed without enabling compiler optimizations.
Recorded `construction` programs already specify their instructions; the
viewer disables these compiler options for them.

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

For `sample_tagged` and its imports, the measured instruction counts are:

| Configuration | Kernel instructions | Reduction from baseline |
| --- | ---: | ---: |
| Baseline | 457,688 | — |
| Normal-form reuse | 419,678 | 8.3% |
| Instruction memoization | 282,139 | 38.4% |
| Both | 244,439 | 46.6% |

All four traces were replayed successfully, with identical displayed result
statements and axiom dependencies. In this run, compilation took 15.46 seconds
for baseline and 8.87 seconds with both options.

The larger `curve_tag_stability` development checked and replayed with
1,211,134 instructions, compared with its previously checked baseline of
2,752,249 (56.0% fewer). Its dependencies remained `lib_Trunc` and
`lib_trunc_intro`. Optimized compilation took 247.78 seconds and replay took
5.06 seconds. It still produced 767,529 distinct kernel judgments: the main
saving is in repeated instruction emission, not the mathematical content.

The focused regression suite also replays small baseline and optimized
programs into the same kernel and verifies each proof against both versions
of its statement. It covers dependent types, opaque conversion, recursive
functions, axiom dependencies, and rejection of invalid proofs.

## Boxing and future experiments

Theorems already use boxed kernel definitions. Ordinary `def` declarations
are transparent; `opaque def` keeps a named definition folded and supports
checked unfolding when conversion needs it. The two reuse optimizations do
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
