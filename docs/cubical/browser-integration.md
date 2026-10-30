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

Each workbench term (expression and type) has independent **β step**, **δ
unfold**, and **Normalize** controls. Clicking beta or delta enters selection mode
and highlights all applicable sites in the displayed term without changing it.
Click a highlight (or focus it and press Enter/Space) to reduce that occurrence.
Repeated uses of a shared subtree are separate selections. Escape or **Un-highlight**
cancels the mode. Large terms offer **Show more reduction sites** when the display
budget hides part of the expression.

Selection mode exposes type annotations and nested applications that ordinary
notation can hide, so their reduction sites remain selectable. Beta contracts a
function application, path application, or pair projection; it never unfolds
named definitions. Delta opens the selected reference using the closed body from
the kernel's definition registry, including explicit assumption parameters.
Normalize performs the kernel's full computation rules immediately.

The stepper proposes syntax with capture-avoiding substitution. Before showing a
change, C checks a constant path from the original term to its proposed reduct,
which requires definitional equality of their endpoints, and rechecks the whole
judgement. Same-type but unequal replacements are rejected. This introduces no
new trusted reduction rule. The changed side stays expanded so automatic folding
does not hide the step, while the other side and context retain their names.
**Back** restores the previous checked view, including reductions of the type.
An unvalidated edit disables all reduction controls.

Focused checks:

```
node --test tests/cubical-inspection.test.mjs tests/cubical-program.test.mjs tests/cubical-reduction.test.mjs
node tests/cubical-inspector.browser.mjs
```

## Native interface

### Kernel AST view

From a checked proof's inspector, **Open kernel AST** opens the cubical
workbench in its second view. The workbench's **View** selector switches between
mathematical notation, the **Kernel AST** and the **Kernel graph** of judgements;
**Back to Cubist** restores the source inspection.

The AST listing, below the term and type typeset, reads `cc_kernel_node` through the WASM bridge. It exposes
the actual `cc_term_kind` opcode number and C enum name, the unsigned payload,
and all four operand slots (`a` through `d`). `%n` identifies an arena term;
`@n` identifies an interval/face formula. Zero is an unused operand or list
terminator. Source names supplement the numeric data without replacing it.
These are native syntax constructors, not a trace of checking instructions or
CPU/WASM instructions. They retain the shared graph and do not normalize it.

The roots identify the checked expression, its selected checked type, and the
inferred type when the two use different handles. Context entries preserve their
order and show numeric symbols and type handles. Open interval dimensions and
formula clauses retain all 64 mask bits. A `CC_DEFREF` keeps its registry index;
**Show body and type** follows its separately registered, checked definition.
Operand links jump to their nodes, including nodes outside the current page.
**Show more nodes** extends the listing. **Download shown assembly** exports the
visible portion and labels incomplete listings explicitly.

Handles belong to the reconstructed native session and may differ on another
replay. The transfer still reconstructs and checks source; it does not trust a
supplied listing as a proof. The assembly view is read-only. Editing and checked
reductions remain available in the mathematical view.

```
node --test tests/cubical-assembly.test.mjs
node tests/cubical-inspector.browser.mjs
```

### WASM boundary

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
- the 27 declarations of the library's binary numbers, `bnat`;
- computational transport along the Glue universe path for the identity
  equivalence of `Nat`, without a univalence axiom;
- `radix_factorials`' 10! in binary, base 2 and base 10, through a native
  elaborator, and 10! carried from base 10 to binary along the univalence
  path `radix_path`, without a large expression.

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

Until 2026-10-30, `tests/cubical-transfers.test.mjs` also transported the
archive's manual factorial proofs between its unary, binary and radix
numerals in all four directions, along Glue universe paths that JavaScript
built from their inverse laws, within 2.5 million arena nodes and 128 MB,
and with no unary numeral above 24, the length of a binary literal that
its parser counted in unary.
NT5 of the
[archive retirement](../roadmaps/archive-retirement.md#number-theory-in-the-library)
retired it with those modules. The library states the same transports in
Cubist: `radix_conversion`'s `radix_path`, from a checked equivalence, and
`radix_factorials`, which carries 10! along it.

The website's regular proof inspector **still uses the production Id/J kernel**.
The new backend is not its default. The general production `idtoequiv isEquiv`
API, strict identity elimination compatibility, higher inductive types and full
library translation remain unfinished. The archive's transfer proofs are
documented in [binary-radix.md](../tactical/binary-radix.md), a dated
checkpoint.
