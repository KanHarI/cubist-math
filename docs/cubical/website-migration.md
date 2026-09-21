# Native cubical website migration

## Current checkpoint

The website defaults to the independent cubical C kernel compiled to WebAssembly.
The full current corpus passes the one-second declaration benchmark: **2,484
concrete declarations checked, zero slow, blocked, or failed declarations**, and
16 universe templates checked at their concrete uses. There are 232 modules and
2,500 source declarations. See [the benchmark](benchmark.md), the latest
`web/benchmark-results.json`, or run `/benchmark.html` in the browser.

The explicit legacy backend remains available; it is never used as an automatic
fallback when native checking rejects a proof. Native interval proofs live under
`web/proofs/cubical/`. The source registry chooses those editions, and the editor
shows the actual source being checked. Original public theorem statements and
logical assumptions are preserved. Extra source declarations factor long proofs
into reusable lemmas.

## What changed

- Native path algebra, dependent pair paths, identity systems, structure/group
  identity, circle encode/decode, bouquet actions, field extensions, and the
  existing Galois development now check against computational cubical paths.
  Places that relied on judgmental constant transport in the old backend now
  supply explicit existing computation paths.
- Public result types on path inverse laws and identity maps retain compact
  contracts instead of exposing large inferred construction endpoints.
- Concrete universe-schema specializations are independently checked once and
  reused as named definitions. Templates themselves are not advertised as
  closed proof certificates.
- `with unfolding [names] { expression }` supplies genuinely scoped conversion
  hints. Each block is independently checked and retained as a closed helper,
  abstracting local variables and interval coordinates. Hinting a public
  definition also exposes its compiler-private helpers; other source definitions
  stay folded. Hints alter conversion strategy, never equality or assumptions.
- The native inspector and workbench replay source, preserve definition
  references, display explicit assumption contexts, and support source Back
  navigation. No legacy instruction stream is presented as a cubical proof.
- The loader pre-counts imports once and names the active declaration. Kernel
  steps, declaration progress, and current declaration each occupy their own line.
- The temporary benchmark runs in Node or a cancellable browser worker, with
  separate fast/slow/blocked/failed categories and descending time within each.
  A cooperative deadline and arena transactions prevent slow attempts or
  accumulated temporary syntax from poisoning later independent checks.

## Assumptions and remaining API work

Existing truncation, LEM, and choice signatures are explicit native contexts.
Closed definitions abstract over exactly their required assumptions. The existing
truncation signature lowers a U1 input to U0; that assumption is preserved and
shown, not silently replaced with computational truncation.

Function extensionality and the library's `ua`/`UnivalenceBeta` uses are derived
cubically. The full public half-adjoint `Univalence` witness is a remaining API
completion task; no declaration in the current corpus calls it. Completing the
current corpus does not finish the planned full Galois or complex-analysis
libraries. Their development roadmaps remain separate.

## Validation and resuming

Run `npm run benchmark:cubical` for the full source scan, or pass module names to
`node tools/benchmark-cubical.mjs` during development. Rebuild C changes with
`make cubical-wasm`. Use focused tests while iterating; reserve the full corpus
scan for a completed change or a requested measurement.

The checkpoint was exercised by the native C regression suite, UBSan compaction
regression, 56 focused frontend/runtime/formatter/reference tests, and the
browser proof/workbench/benchmark regression. See [finite conversion notes](finite-conversion-migration.md)
for the source factoring and [unfolding hints](unfolding-hints.md) for strategy.
