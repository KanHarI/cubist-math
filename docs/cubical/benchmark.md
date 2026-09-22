# Temporary declaration benchmark

Latest optimization pass (September 23): **3,573 checked within 100 ms, zero
slow, blocked, or failed declarations, plus 44 universe templates**, across
346 modules. The Node run took 10.14 s; its slowest declaration took 93.075 ms.
See [the performance notes](checking-optimizations.md) for the changes and
comparison with the previous corpus scan. The live browser worker independently
completed the same corpus with no slow, blocked, or failed entries. These are
machine-specific timings.

The subsequent F4/F2 loop-equality showcase adds 21 concrete declarations.
The updated saved scan checks all **3,594** within 100 ms, with zero slow,
blocked, or failed entries and 44 templates (10.74 s total; maximum 92.851 ms).

Open `/benchmark.html` and choose **Run benchmark in this browser**. A worker
loads the current source corpus, checks imports once, and gives each declaration
a 100 ms shared deadline for elaboration and the native closed check.
The page remains responsive, supports cancellation, filters the four categories,
links to source, and exports JSON. Browser results stay local.

`npm run benchmark:cubical` runs the same engine in Node and writes
`web/benchmark-results.json` and `build/cubical-benchmark.json`.
`node tools/benchmark-cubical.mjs MODULE...` checks selected import graphs and
only writes the build report; `--publish` also replaces the website snapshot.
Rebuild with `make cubical-wasm` after C changes.

Use `--limit-ms=1000` to measure a slower import graph without blocking its
later declarations. The browser provides 100 ms, 1 s, and 10 s deadlines.
Reports record the deadline and individual optimization settings; compare
counts only at matching settings. Times remain sorted descending per category.

The independent switches default on in both the proof viewer and benchmark:

- `--no-share-syntax`: disable exact native syntax interning.
- `--no-reuse-checks`: disable memoization of successful native judgements.
- `--no-compact-paths`: omit the checked endpoint signatures on `sym`, `trans`,
  and `cong`. The proof term is still built from ordinary cubical primitives.

For example: `node tools/benchmark-cubical.mjs polynomial_difference
--limit-ms=1000 --no-reuse-checks` (one command).
See [the optimization audit](checking-optimizations.md) for correctness details.

1. **Checked:** native checking completed within the selected deadline (100 ms by default).
2. **Needs optimization:** the wall deadline expired, or a completed check
   exceeded the target. A timeout does not refute the theorem.
3. **Blocked:** elaboration reached an unavailable dependency. The report
   records that dependency and follows its blocker chain to the root.
4. **Needs fixing:** checking failed for another reason. Investigate whether
   the fault is in migration, elaboration, the source proof, or resource use.

Universe templates are separate: only their concrete specializations
are closed, checked kernel definitions. Counting templates as standalone proof
certificates would be misleading. Counts refer to source declarations, not
generated specialization helpers or kernel instructions.

The deadline is cooperative, polled at source elaboration boundaries and every
1,024 kernel steps. Cleanup and operations between polls can overrun slightly.
All times over the target stay in category 2. Import parsing is excluded from
individual times. No full normalization or inspector rendering is requested.
Warm dependencies and machine load affect timings; this is an optimization
tracker, not a cross-machine performance score.

Rejected attempts roll back temporary arena nodes and definitions. Successful
attempts compact their new arena segment, retaining the checked definitions and
all reachable syntax while discarding temporary checking terms. Native
reduction caches, the previous result certificate, and JS handle caches are
invalidated together. The host translates newly retained definition handles after
compaction. Earlier checked definitions remain immutable and valid.
This prevents a slow attempt's temporary allocations from producing misleading
allocation failures in independent later declarations. The initial unisolated
scan was discarded as a baseline for precisely that reason.

The corrected September 21 baseline contains 2,479 source declarations in
232 modules: 2,322 checked, 20 slow, 119 blocked, 2 failed, 16 templates.
It took 38.08 seconds on an Apple M3 Pro in Node 24.13.0.

The completed migration scan checks all 2,484 concrete declarations within one
second each: zero slow, blocked, or failed declarations, plus 16 universe
templates, across 232 modules. The source total is now 2,500 because several
long proofs were factored into reusable checked lemmas. The saved report
retains the baseline counts; timings depend on the runtime and machine load.

The 100 ms optimization scan (September 21, 12:30 UTC) checks all 2,484
concrete declarations, with zero slow, blocked, or failed declarations and
16 templates. Total time is 4.81 s, down from 17.43 s in the completed migration
scan. The slowest declaration is `complex_coordinate_assoc_real` at 47.234 ms.
The browser worker independently completed the corpus at 100 ms with the same
category counts. These are observed results on this machine, not timing
promises for every device.
