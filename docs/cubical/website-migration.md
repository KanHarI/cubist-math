# Cubical website migration checkpoint

The website now defaults to the independent cubical C checker, compiled to WASM.
The kernel selector exposes the original Id/J C checker explicitly. There is no
fallback that relabels an old certificate as cubical, and unsupported declarations
are shown as **Not checked**. The whole mathematical library is **not yet migrated**.

## Implemented

- `web/cubical-worker.mjs` checks source imports through `CubicalProgram`.
  Module-qualified native definitions prevent shadowing from retargeting earlier
  checked references. Imports are loaded on demand.
- Source references, local contexts, folded native definitions, and raw native
  syntax can be inspected. Interval coordinates remain explicit in open cubes.
- The native workbench replays exported source before inspecting a term. Exported
  ASTs are informational, never trusted certificates. Edited syntax is checked
  by C; normalization is an explicit action on a checked expression.
- Definitions, context variables, and proof return navigation survive transfer.
  The workbench provides Back, Back to source, and Un-highlight controls.
- The browser ABI supports all current constructors through HComp (41) and
  Trans (42), with their different binder scopes. Open-cube checking passes a
  validated 64-bit dimension mask. Decoding preserves ambient dimension names
  without capturing them under generated binders.
- Native source forms include `path`, `PathP`, `at`, `comp`, `face`, interval
  reversal/meet/join, pushout constructors and dependent induction. `Interval`
  is coordinate-binder syntax, not a postulated type.
- Suspension is derived from pushouts. The existing transport-style
  `suspension_induction` and `suspension_meridian_beta` elaborate through the
  proved equivalence between dependent paths and equality after transport.
  `apd` uses the same checked conversion.
- `web/proofs/cubical_paths.proof` has 15 checked declarations covering these
  source forms. It is available under Homotopy, with quick/full reference links.
- `make cubical-wasm` packages the same experimental elaborator sources into
  `web/dist/cubical-runtime`; generated browser copies are not another source
  implementation. `npm run build:site` builds both WASM kernels.

## Validation completed

Targeted native tests cover the Euclid source/import graph, manual factorial
sources, the actual four-direction factorial transfers through Glue, open cubes,
constructor/endpoint rejection, changing pushout maps and corrected transport,
module shadowing, native inspection, and export/replay.

The browser test checks native Euclid, cross-file Back, local contexts, workbench
replay, rejected edits, cubical paths, and interval contexts in the workbench.
The built static artifact was checked with native Euclid and cubical paths, plus
F4 on the explicitly selected **legacy** backend. This does not certify F4 in
cubical C. The full legacy mathematical regression is deferred until the final
migration checkpoint; only affected modules/tests are run during development.

Commands:

```sh
make cubical-wasm
npm test -- --cubical cubical_paths euclid
npm test -- tests/cubical-wasm.test.mjs tests/cubical-program.test.mjs tests/cubical-transfers.test.mjs
node tests/cubical.browser.mjs
npm run build:site
node tests/site.browser.mjs
```

## Next work

1. Port path foundations to direct cubical operations with explicit source proofs.
   `experiments/cubical/path-algebra.mjs` and its native/reference tests provide
   constant transport, units, inverse laws, and associativity. Existing
   `paths.proof` uses strict J computation in several branches. Do not silently
   treat those branches as valid or change `refl` into proof search. Also note:
   legacy `sym`/`trans`/`cong` are library macros importing paths, so replacing
   the bootstrap definitions with those macros creates a cycle in that backend.
2. Complete the remaining dependent transport, cancellation, decoder and `apd`
   coherence laws, then port the circle encode/decode proof.
3. Connect the public universe-polymorphic equivalence/univalence interfaces to
   native Glue. The public IsEquiv is half-adjoint data; native Glue uses
   contractible fibers. A checked bridge is required, not a reinterpretation.
4. Supply explicit support/policy for truncation, LEM and choice. Missing imports
   or unsupported axiom declarations currently remain unverified.
5. Improve generic-schema inspection: each concrete specialization is checked,
   but a universe schema is not a single closed native declaration.
6. Restore source-goal inspection for the native backend (currently declaration
   and local-reference inspection work; there is no legacy instruction stream).
7. Run the whole source migration audit and final full regressions only after
   the required foundations are in place. Update landing-page readiness and
   static tests as additional highlights acquire native certificates.

The generic path-over bridge is in `experiments/cubical/path-over.mjs`; its
inverse laws and actual nonconstant Glue-family tests are described in
`docs/cubical/path-over.md`. Computational pushout rules and boundaries are in
`docs/cubical/pushouts.md`.

## September 21 migration update

Native editions under `web/proofs/cubical/` now provide checked interval proofs
for the path foundations, dependent pair paths, identity systems, adjointification,
path actions, and circle encode/decode. `web/cubical-sources.mjs` selects them only
for the native backend; the editor and source link show the actual source checked.
The original sources continue to serve the explicit legacy backend. This is not
an invisible term substitution or fallback certificate.

The standard library's truncation, LEM, and set-choice signatures are now explicit
native contexts. Closed definitions abstract over exactly their needed assumptions.
The existing truncation signature returns a type in U0 even for a U1 input; this
universe-lowering assumption is preserved, not claimed as computational truncation.
Function extensionality and the public `ua`/`UnivalenceBeta` interface are derived
cubically. The full public `Univalence` witness still requires the separate
half-adjoint coherence bridge; no existing source module currently calls it.

Focused checks now pass for binary/radix equivalences and for the combined
`dyadic_sampling`, `subdivision_transport`, and `complex_norm_coordinates` import
graph (300 checked declarations). The circle graph has 188 checked declarations.
These are local results, not a claim that the whole library passes.

Remaining work includes structure/group conversion performance, downstream
Galois and bouquet proofs, and final complete-library/browser verification.
A captured `structure_path_roundtrip` conversion exhausted 10 million steps;
automatically growing that budget alone led to gigabytes of allocation. Selective
conversion strategies and explicit source hints are being tested against this
fixture. The loader now names the declaration currently being checked, rather
than the previously completed declaration.

## Benchmark checkpoint

See [the runnable benchmark](benchmark.md) and `/benchmark.html`. The current
corpus is now measurable with a one-second per-declaration wall deadline and
isolated rejected attempts. The page can run the corpus locally in a worker.

Selective `with unfolding [...] { expression }` source hints now preserve folding through the
structure and group identity conversion bottlenecks. These are conversion
strategies, not equality assumptions. Concrete Universe schema specializations
are checked once as named native functions and reused at later applications;
this removes repeated inlining in binary/radix equivalence proofs.

The corrected baseline is 2,322 checked, 20 slow, 119 blocked, 2 failed, plus
16 templates. The main remaining tasks are slower Galois/field conversions,
two circle-degree path-unit corrections, and downstream unblocking. Consult
the latest benchmark JSON instead of earlier audit counts in this document.
