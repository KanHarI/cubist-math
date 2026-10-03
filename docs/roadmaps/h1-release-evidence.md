# Release evidence for `8229181`

- Revision: `8229181d3110928bcffeed212095b97cc906567a`
- Recorded: 2026-10-03T19:05:22.765Z
- Local checks: in a fresh checkout of the revision
- Build stamp: kernel sources `0d89137062f8`, outputs `d85575730948`

## Local checks

| Check | Command | Outcome | Seconds | Summary |
| --- | --- | --- | --- | --- |
| Kernel tests | make -C kernel test | passed | 8 | instruction isolation: ok |
| Lint | make lint | passed | 23 | 38/38 files checked 100% done |
| Sanitizers | make sanitize SANITIZERS=undefined | passed | 8 | instruction isolation: ok |
| WASM build | make wasm | passed | 3 |  |
| Build stamp | node tools/build-stamp.mjs check | passed | 0 |  |
| Instruction coverage | node tools/instruction-coverage.mjs | passed | 50 | Archive checked with the driver's guide in 37.3 s: 3,794 of 3,794 declarations in 370 modules, 0 gaps; kernel work 5,710,965 instructions, 199,658,737 steps.; 3,899 of 3,899 definitions derive in instruction mode (100.0%), in 12.4 s; kernel work 2,149,815 instructions (45,240 rejected), 295,925 queries, 135,103,226 steps; 837,591 branch points.; Coverage complete. |
| Node suite | npm test | passed | 86 | ℹ tests 657; ℹ pass 656; ℹ fail 0; ℹ todo 1 |
| Workbench browser tests | npm run test:browser | passed | 15 | PASS cubical inspector: folding, navigation, simp trace/freeze, generic transfer, bounded raw syntax, workbench editing, and archive-isolated imports |
| Browser test cubical | node tests/cubical.browser.mjs | passed | 26 | PASS native proof/workbench flows and browser corpus benchmark with cancellation and live results |
| Browser test statement | node tests/statement.browser.mjs | passed | 18 | PASS source statements: conclusion, named hypotheses, binder navigation, mobile, S3, finite and general bases, dimension and tower law |
| Browser test proof-navigation | node tests/proof-navigation.browser.mjs | passed | 3 | PASS proof topic navigation (chromium); 370 proofs reachable |
| Browser test landing | node tests/landing.browser.mjs | passed | 19 | PASS proof landing: root, nine highlights, destinations, workbench transfer, mobile (chromium) |
| Site build | node tools/build-site.mjs | passed | 0 | Built build/site (f27aed8b5e9d). |
| Site browser test | node tests/site.browser.mjs | passed | 8 | PASS static landing, repository link, mobile layout, build version; PASS static worker, WASM, checking and folded inspection: euclid (cubical); PASS static worker, WASM, checking and folded inspection: cubical\_paths (cubical); PASS static worker, WASM, checking and folded inspection: f4\_galois\_correspondence (cubical); PASS reference examples: in-browser checking, linked names, embedded kernel inspector, evaluate results, instant macro tips; PASS reference excerpts: checked with their module, linked names, the module's workspace link; PASS examples open in the REPL bar with their definitions; PASS read-only REPL transcripts fork into the REPL bar; PASS library module in the workspace, with its console; PASS REPL page: let, typeof, evaluate, rejected entries; PASS REPL page: /modules, /clear and /restart; PASS elaboration panel and the kernel reference outline; PASS static kernel workbench (http://127.0.0.1:63147/) |

## CI runs dispatched on this revision

- [Run 37146115004](https://github.com/KanHarI/cubist-math/actions/runs/37146115004), 2026-10-03T18:57:03Z: success
  - [workbench](https://github.com/KanHarI/cubist-math/actions/runs/37146115004/job/111270299849): success
  - [test (ubuntu-latest, gcc)](https://github.com/KanHarI/cubist-math/actions/runs/37146115004/job/111270299959): success
  - [test (macos-latest, clang)](https://github.com/KanHarI/cubist-math/actions/runs/37146115004/job/111270299995): success
  - [sanitizer](https://github.com/KanHarI/cubist-math/actions/runs/37146115004/job/111270300035): success
  - [test (macos-latest, gcc)](https://github.com/KanHarI/cubist-math/actions/runs/37146115004/job/111270300080): success
  - [test (ubuntu-latest, clang)](https://github.com/KanHarI/cubist-math/actions/runs/37146115004/job/111270300083): success
  - [lint](https://github.com/KanHarI/cubist-math/actions/runs/37146115004/job/111270300145): success

## Verdict

Every check asked for passed.
