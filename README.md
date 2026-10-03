# Cubist Math

Readable mathematical proofs, checked by a cubical type theory kernel written in C11.
Explore the library at **https://cubist.kanhar.art** or browse the
[repository](https://github.com/KanHarI/cubist-math).

The cubical kernel is the project's sole checker. Proof sources use the `.cubist`
extension. The browser and CLI elaborate the same source language and submit
terms to the native kernel compiled to WebAssembly. Definitions remain named;
conversion unfolds them on demand. Explicit assumptions are shown with each proof.

`Nat`, `zero`, and `succ` come from the ordinary source module
[`nat.cubist`](archive/first-library/nat.cubist), imported as the standard prelude.
They are ordinary names and can be shadowed. Binary and radix numbers are
ordinary inductive declarations too. The source module `w` keeps the inductive
`W(U,V,A,B)` and its structurally recursive `wrec`, though nothing imports it.
H1 was released on 2026-10-02, after review of its model, critical pairs and
canonicity, and is on by default. The kernel has no primitive Nat, W or
pushout formation, constructor, elimination, or computation rules; pushouts
are the source declaration in `pushout`.

## Build and use

```sh
make                 # Native C binaries and invariant tests
make test            # Run the native tests
npm ci               # Node.js 24+
make wasm            # Emscripten; detects .tools/emsdk if installed there
make serve           # http://127.0.0.1:8088/
node cli/repl.mjs check euclid
```

The website is static and checks proofs locally in a Web Worker. The kernel
workbench offers folded notation, checked contexts, beta/delta reduction, and
an assembly view of actual C opcodes. Open any checked expression from its
source inspector to retain its names and return navigation.

## Development checks

```sh
npm test -- euclid                       # Selected source and its imports
npm test -- archive/first-library/circle.cubist
npm test -- --changed                    # Modified .cubist sources
npm test -- tests/cubical-program.test.mjs
npm test                                # Final regression and corpus check
npm run test:browser
make CC=clang sanitize                  # Address/undefined sanitizers
make sanitize SANITIZERS=undefined     # macOS 26, where the address sanitizer hangs
make lint
```

`make wasm` stamps `web/dist` with a hash of the kernel's and the
translator's sources, the compiler and its flags, and the outputs
(`tools/build-stamp.mjs`). It runs under a lock, clears a stamp before
rewriting its outputs, and rebuilds whatever no longer matches, whatever the
file times say. Every command that loads `web/dist` refuses a stale build
rather than run code it does not contain: `npm test`, the browser tests, the
site build, the CLI, the coverage, audit, fingerprint, fuel-baseline,
migration-verifier and benchmark tools, and the driver trace
(`tests/driver-trace.mjs`), which checks another checkout it traces by that
tree's own stamp. So does a test file run on its own, with `node` or
`node --test`: each test file that loads `web/dist` imports
`tests/fresh-build.mjs` first, and `tests/fresh-build.test.mjs` keeps it so.

The independent optimization switches are `--[no-]share-syntax`,
`--[no-]reuse-checks`, and `--[no-]compact-paths`; all default on.
`npm run format:cubist` formats sources and flattens right-associated tuples
while checking that the expanded AST is unchanged. Add `-- --check` for a dry run.
`npm run lint:cubist` reports bindings that are never used and can be removed,
such as an `as` name no motive mentions; checking reports the same warnings.

## Code and documentation

- [`docs/README.md`](docs/README.md): documentation index and where to resume each development.
- [`kernel/`](kernel/README.md): the trusted C kernel. Its typing rules are the instructions in `src/instructions.c`, with one file per group of computation rules.
- [`docs/guides/cli.md`](docs/guides/cli.md): custom proofs, imports, commands, and CLI limitations.
- [`docs/guides/kernel.md`](docs/guides/kernel.md): a mathematician's guide to reading the kernel.
- [`web/translator/`](web/translator): the translator from source to kernel syntax, with elaboration and the proof tactics; the browser, the CLI and the tests load these same files. Every check is the kernel's. Their tests are in `tests/translator/`.
- [`archive/first-library/`](archive/first-library): the archived first `.cubist` library, still checked in CI. A rebuilt library replaces it area by area; see [`docs/library-results.md`](docs/library-results.md) and the [work plan](docs/roadmaps/work-plan.md).
- [`cubist-tests/`](cubist-tests/README.md): the Cubist sources the test suite checks, each a module the proof workspace opens as `proof.html?proof=NAME`, so that a case's derivation can be inspected there.
- [`web/language.html`](web/language.html): the source language reference, one page per chapter under `web/reference/`.
- [`docs/tactical/galois-handoff.md`](docs/tactical/galois-handoff.md) and [`docs/roadmaps/complex-analysis-roadmap.md`](docs/roadmaps/complex-analysis-roadmap.md): unfinished mathematical developments and resumption notes.

## Resuming development

Start with the [documentation index](docs/README.md), then read the relevant
[roadmap](docs/roadmaps/README.md) and [tactical checkpoint](docs/tactical/README.md)
before implementing a result. Galois theory, complex analysis, the real-number
constructions, and the RH-to-prime-counting implication each have a roadmap.
These record the intended scope, existing
results, remaining obligations, and assumptions; continue from that work rather
than rebuilding its foundations. A paused roadmap records possible future work,
not an instruction to resume it automatically.

Confirm the checkpoint against the current `.cubist` sources and run its focused
checks. Some notes describe earlier kernels: the current cubical checker and
verified declarations determine what is actually available. Preserve explicit
assumptions, prove missing steps instead of assuming them, and update the roadmap
and handoff with the results, verification commands, and next unfinished step.

`npm run build:site` assembles `build/site`; pushes to `main` publish it through
GitHub Pages at `cubist.kanhar.art`. The repository's `web/CNAME` declares the domain.
The former Id/J implementation and its separate instruction language have been
removed. Historical design notes are retained as history, not current API documentation.
