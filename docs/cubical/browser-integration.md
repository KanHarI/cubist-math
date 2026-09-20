# Native cubical browser integration

The new C checker builds independently to `web/dist/cubical.mjs` and
`web/dist/cubical.wasm`:

```
make cubical-wasm
node --test tests/cubical-wasm.test.mjs
```

`wasm/cubical_bridge.c` exposes session tokens and integer syntax handles. It
does not accept production-kernel certificates or raw pointers from JavaScript.
`web/cubical-kernel.mjs` wraps checked judgements, named context variables,
formula inspection, and explicitly requested normalization. A failed check
clears the previous result; the session can then check a corrected term.
`web/cubical-syntax.mjs` transports named ASTs, preserving shared nodes and all
64 dimension bits. Cached input syntax is frozen to prevent stale handles after
mutation. None of these syntax operations certifies a proof.

Current independent WASM tests cover:

- dependent functions, checked telescopes, and path endpoints;
- rejection of invalid endpoints, malformed contexts and forged Glue witnesses;
- distinct interval and face lattices, including dimension 63;
- checking a compact expression denoting `2^22` without computing its unary value;
- all 13 declarations from the actual `binary_naturals.proof` source;
- computational transport along the Glue universe path for the identity
  equivalence of `Nat`, without a univalence axiom;
- every declaration of `binary_arithmetic`, `binary_induction`, `radix_naturals`,
  `radix_arithmetic`, and `radix_factorial`, through a native elaborator.

The source translator now handles W formation/introduction/induction, sums and
dependent matches, binary literals, and `intro`/`let`/`have`/`exact` blocks.
Native checking is an explicit final gate when requested; unsupported source
is reported as untranslated and never replaced by an assumed declaration.
`web/cubical-elaborator.mjs` now performs inference, conversion and head queries
through the native C API. Closed definitions are checked before registration;
later terms retain references to those definitions. Binary function
extensionality compiles to an interval path between functions, without an axiom.
The three manual factorial proofs pass: the binary development uses approximately
43,657 nodes / 2.3 MB, and the two generic-radix instances together use approximately
349,389 nodes / 17 MB. These are complete source checks, not imported certificates.

The website's regular proof inspector **still uses the production Id/J kernel**.
The new backend is not its default, and the general `idtoequiv isEquiv` theorem,
full library translation, and the cubical factorial transport acceptance test
are not complete. The existing compact factorial transfer proofs are documented
separately in [binary-radix.md](../binary-radix.md).
