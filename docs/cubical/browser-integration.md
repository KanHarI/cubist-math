# Native cubical browser integration

## Inspecting checked terms

The proof workspace puts source beside the inspector, with verification results
below the source. “Widen” gives the inspector more room for long types.
Source names, context assumptions, local definitions, axioms, and generated
cubical helpers are clickable. “Show body” expands a named proof or local
definition; “Show more of the term” increases the display budget without
normalizing the expression.

The default folded view preserves kernel definition references and uses source
labels for bound variables. Local `let`, `have`, and `obtain` names abbreviate
their elaborated expressions, including occurrences in context types. These
abbreviations are selected by exact syntax matching, modulo removal of typed
identity applications. Matching is restricted to the occurrence's lexical
environment and does not cross internal term or interval binders. Ambiguous
binder labels are distinguished with primes. No heuristic unfolding or proof
search is performed to obtain a nicer name.

`web/cubical-inspection.mjs` creates presentation annotations separately from the
checked AST. “Kernel notation (stored)” exposes the underlying constructors;
“Raw kernel term” also exposes internal names and annotations. Numeral,
nondependent arrow/product, and reflexivity notation are structural display
conventions. Truncation and equality notation have separate switches. Dependent
paths retain their varying family instead of being printed as ordinary equality.

Workbench transfers replay source and reconstruct the selected checked term.
They never submit display aliases as evidence. Source folding applies to context
types there too and can be switched off. Editing or normalization discards the
old folded projection; an invalid edit leaves the last checked display visible
with an explicit failure and disables normalization.

Focused checks:

```
node --test tests/cubical-inspection.test.mjs tests/cubical-program.test.mjs
node tests/cubical-inspector.browser.mjs
```

## Native interface

The new C checker builds independently to `web/dist/cubical.mjs` and
`web/dist/cubical.wasm`:

```
make cubical-wasm
node --test tests/cubical-wasm.test.mjs
node --test tests/cubical-transfers.test.mjs
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
  `radix_arithmetic`, and `radix_factorial`, through a native elaborator;
- `factorial_ten_from_binary`, about the existing `Nat` factorial, using the
  binary arithmetic compatibility proofs without materializing its unary value;
- the binary/Nat, radix/Nat and direct binary/radix inverse laws, converted to
  checked contractible-fiber equivalences and actual Glue universe paths;
- transport of the manual factorial proofs in all four requested directions,
  including radix bases 2 and 10, followed by the derived computation law and
  arithmetic compatibility to identify the original target factorial;
- seven concrete transferred factorial statements in
  `experiments/cubical/factorial-transfer.proof`, including the existing
  `Nat` statement `factorial(10) = nat_3628800`.

The source translator now handles W formation/introduction/induction, sums and
dependent matches, binary literals, dependent pair induction (`pair_induction`),
pair elimination (`unpack` and `obtain`),
sum `cases`, and `intro`/`let`/`have`/`exact` blocks.
Native checking is an explicit final gate when requested; unsupported source
is reported as untranslated and never replaced by an assumed declaration.
`web/cubical-elaborator.mjs` now performs inference, conversion and head queries
through the native C API. Closed definitions are checked before registration;
later terms retain references to those definitions. Binary function
extensionality compiles to an interval path between functions, without an axiom.
The three manual factorial proofs pass: the binary development uses approximately
43,657 nodes / 2.3 MB, and the two generic-radix instances together use approximately
349,389 nodes / 17 MB. These are complete source checks, not imported certificates.

The combined four-direction Glue transfer check uses approximately 1.35 million
arena nodes and 67 MB. Scanning its complete arena finds no closed successor
chain larger than **10**. JavaScript builds syntax; the C/WASM checker verifies
the inverse proofs, equivalences, universe paths and transported equalities.
No univalence, function extensionality, choice or LEM axiom is registered.
Dependency traversal verifies that each result contains actual Glue/composition,
and that a binary-to-radix transfer never uses the target's manual factorial
theorem. Conversely, radix-to-binary/Nat transfers do not use the binary manual
factorial theorem. Separate digit-conversion certificates identify the numerals.

The transport computation law is first registered as a checked function of an
arbitrary argument, then applied to each factorial endpoint. Keeping this shared
proof folded avoids repeated checking of a large substituted beta body. The
initial direct-body radix check exhausted the existing work budget; this
factoring solves it without increasing that budget or changing a kernel rule.

`experiments/cubical/number-transport.mjs` contains the checked-definition
assembly for this migration. The production half-adjoint `Equiv` declarations
remain explicitly untranslated: their source inverse laws build the cubical
contractible-fiber witnesses instead. The generic production `Equiv` API still
needs migration; these helpers do not silently substitute an unchecked witness.

The website's regular proof inspector **still uses the production Id/J kernel**.
The new backend is not its default. The general production `idtoequiv isEquiv`
API, strict identity elimination compatibility, higher inductive types and full
library translation remain unfinished. The compact factorial transfer acceptance
test now passes natively. The production transfer proofs are documented
separately in [binary-radix.md](../binary-radix.md).
