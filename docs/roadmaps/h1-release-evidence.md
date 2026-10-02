# Release evidence for `581e03c`

- Revision: `581e03cc2eda551be9a40870830e9c5b3f0a0554`
- Recorded: 2026-10-02T15:50:22.753Z
- Local checks: in a fresh checkout of the revision
- Build stamp: kernel sources `e4f1284c0a85`, outputs `81b5abe99615`; translator copy sources `bba0a152e80a`, outputs `e7f577622661`

## Local checks

| Check | Command | Outcome | Seconds | Summary |
| --- | --- | --- | --- | --- |
| Kernel tests | make -C kernel test | passed | 9 | instruction isolation: ok |
| Lint | make lint | passed | 25 | 47/47 files checked 100% done |
| Sanitizers | make sanitize SANITIZERS=undefined | passed | 11 | instruction isolation: ok |
| WASM build | make wasm | passed | 4 | node tools/build-cubical-runtime.mjs |
| Build stamp | node tools/build-stamp.mjs check | passed | 0 |  |
| Instruction coverage | node tools/instruction-coverage.mjs | passed | 53 | Archive checked with the driver's guide in 39.7 s: 3,788 of 3,788 declarations in 368 modules, 0 gaps; kernel work 5,708,336 instructions, 199,674,864 steps.; 3,893 of 3,893 definitions derive in instruction mode (100.0%), in 12.8 s; kernel work 2,149,535 instructions (45,700 rejected), 295,757 queries, 135,077,685 steps; 837,330 branch points.; Coverage complete. |
| Instruction coverage with the oracle | node tools/instruction-coverage.mjs --oracle | passed | 45 | Archive checked with the conversion oracle in 34.5 s: 3,788 of 3,788 declarations in 368 modules, 0 gaps; kernel work 5,200,444 instructions, 275,403,557 steps.; 3,893 of 3,893 definitions derive in instruction mode (100.0%), in 10.2 s; kernel work 1,929,812 instructions (42,462 rejected), 285,959 queries, 204,545,464 steps; 627,369 branch points.; Coverage complete. |
| Node suite | npm test | passed | 99 | ℹ tests 714; ℹ pass 714; ℹ fail 0 |
| Workbench browser tests | npm run test:browser | passed | 15 | PASS cubical inspector: folding, navigation, simp trace/freeze, generic transfer, bounded raw syntax, workbench editing, and archive-isolated imports |
| Browser test cubical | node tests/cubical.browser.mjs | passed | 29 | PASS native proof/workbench flows and browser corpus benchmark with cancellation and live results |
| Browser test statement | node tests/statement.browser.mjs | passed | 20 | PASS source statements: conclusion, named hypotheses, binder navigation, mobile, S3, finite and general bases, dimension and tower law |
| Browser test proof-navigation | node tests/proof-navigation.browser.mjs | passed | 3 | PASS proof topic navigation (chromium); 370 proofs reachable |
| Browser test landing | node tests/landing.browser.mjs | passed | 20 | PASS proof landing: root, nine highlights, destinations, workbench transfer, mobile (chromium) |
| Site build | node tools/build-site.mjs | passed | 0 | Built build/site (d2acfb1b53c7). |
| Site browser test | node tests/site.browser.mjs | passed | 8 | PASS static landing, repository link, mobile layout, build version; PASS static worker, WASM, checking and folded inspection: euclid (cubical); PASS static worker, WASM, checking and folded inspection: cubical\_paths (cubical); PASS static worker, WASM, checking and folded inspection: f4\_galois\_correspondence (cubical); PASS reference examples: in-browser checking, linked names, embedded kernel inspector, evaluate results, instant macro tips; PASS reference excerpts: checked with their module, linked names, the module's workspace link; PASS examples open in the REPL bar with their definitions; PASS read-only REPL transcripts fork into the REPL bar; PASS library module in the workspace, with its console; PASS REPL page: let, typeof, evaluate, rejected entries; PASS REPL page: /modules, /clear and /restart; PASS elaboration panel and the kernel reference outline; PASS static kernel workbench (http://127.0.0.1:53243/) |

## CI runs dispatched on this revision

- [Run 37028834426](https://github.com/KanHarI/cubist-math/actions/runs/37028834426), 2026-10-02T15:42:12Z: success
  - [sanitizer](https://github.com/KanHarI/cubist-math/actions/runs/37028834426/job/110910271189): success
  - [test (ubuntu-latest, clang)](https://github.com/KanHarI/cubist-math/actions/runs/37028834426/job/110910271499): success
  - [lint](https://github.com/KanHarI/cubist-math/actions/runs/37028834426/job/110910271641): success
  - [test (macos-latest, gcc)](https://github.com/KanHarI/cubist-math/actions/runs/37028834426/job/110910271678): success
  - [workbench](https://github.com/KanHarI/cubist-math/actions/runs/37028834426/job/110910271711): success
  - [test (ubuntu-latest, gcc)](https://github.com/KanHarI/cubist-math/actions/runs/37028834426/job/110910271949): success
  - [test (macos-latest, clang)](https://github.com/KanHarI/cubist-math/actions/runs/37028834426/job/110910271953): success

## Verdict

Every check asked for passed.
