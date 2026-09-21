# Temporary declaration benchmark

Open `/benchmark.html` and choose **Run benchmark in this browser**. A worker
loads the current source corpus, checks imports once, and gives each declaration
a one-second shared deadline for elaboration and the native closed check.
The page remains responsive, supports cancellation, filters the four categories,
links to source, and exports JSON. Browser results stay local.

`npm run benchmark:cubical` runs the same engine in Node and writes
`web/benchmark-results.json` and `build/cubical-benchmark.json`.
`node tools/benchmark-cubical.mjs MODULE...` checks selected import graphs and
only writes the build report; `--publish` also replaces the website snapshot.
Rebuild with `make cubical-wasm` after C changes.

1. **Checked:** native checking completed within 1,000 ms.
2. **Needs optimization:** the wall deadline expired, or a completed check
   exceeded the target. A timeout does not refute the theorem.
3. **Blocked:** elaboration reached an unavailable dependency. The report
   records that dependency and follows its blocker chain to the root.
4. **Needs fixing:** checking failed for another reason. Investigate whether
   the fault is in migration, elaboration, the source proof, or resource use.

The 16 universe templates are separate: only their concrete specializations
are closed, checked kernel definitions. Counting templates as standalone proof
certificates would be misleading. Counts refer to source declarations, not
generated specialization helpers or kernel instructions.

The deadline is cooperative, polled at source elaboration boundaries and every
1,024 kernel steps. Cleanup and operations between polls can overrun slightly.
All times over the target stay in category 2. Import parsing is excluded from
individual times. No full normalization or inspector rendering is requested.
Warm dependencies and machine load affect timings; this is an optimization
tracker, not a cross-machine performance score.

Rejected attempts roll back temporary arena nodes and definitions. Native
reduction caches, the previous result certificate, and JS handle caches are
invalidated together. Earlier checked definitions remain immutable and valid.
This prevents a slow attempt's temporary allocations from producing misleading
allocation failures in independent later declarations. The initial unisolated
scan was discarded as a baseline for precisely that reason.

The corrected September 21 baseline contains 2,479 source declarations in
232 modules: 2,322 checked, 20 slow, 119 blocked, 2 failed, 16 templates.
It took 38.08 seconds on an Apple M3 Pro in Node 24.13.0. The current saved
report records changes relative to that baseline; optimization is ongoing.
