# Cubist website and workbench

Run `make serve`, then open http://127.0.0.1:8088/. The site uses the cubical C
kernel compiled to WebAssembly; there is no alternate checking backend.
The archived first library lives in `../archive/first-library/*.cubist`; the site serves it at `archive/first-library/`.

The source inspector retains definition names, context variables, and axiom
labels. **Open in workbench** replays the source in a fresh kernel session.
Checking and kernel operations run in a worker, with declaration progress while
loading, so expensive computations leave the browser responsive. Disabled
buttons use a normal cursor; the status text reports work in progress.
**Back to Cubist** restores the source selection. Folded notation is a display
option; raw syntax and native opcode assembly remain available. Beta and delta
buttons highlight applicable occurrences, and every selected reduction is
checked for definitional equality. **Un-highlight** clears visual selection.

Open `http://127.0.0.1:8088/workbench.html?view=ast` for a standalone kernel
example. In **Kernel AST**, select Expression or Judgement type, then follow
the named operands to select an occurrence. A preview and highlighted AST row
show the selection. For the default `identity(2)`, click **δ unfold identity**
beside its function operand, then **β reduce containing application**. At the
application itself the button is **β reduce application**. The native
instruction changes only that occurrence, even when its handle is shared.
The table's handle links inspect nodes independently of this selection.
Below the operation selector, **Native AST subtree** is collapsed by default.
Open it to see native constructors and operands without numeral shorthand.
Branches load one level at a time; **Select** focuses that occurrence for a
reduction, including normalization of only that subtree.

**Copy trace** copies a JSON diagnostic log to paste into an issue or chat.
It records operations from the current page load, including native paths,
rules, budgets, successful/refused results, Back branches, and bounded raw
AST excerpts before/after native steps. Costs include kernel work counters,
arena growth and elapsed time for the Step and its readback. The log includes
the page URL, identifies the checked source modules by SHA-256, and includes
a bounded copy of the main source. It does not record internal WHNF/Normalize steps or
expand definition bodies. Up to 100 recent events are retained with a size
limit; dropped events and omitted syntax are marked. Copy works during a
running operation and after a worker failure; denied clipboard access shows
selectable text. Reloading starts a new trace.

Buttons beside the selection offer **β**, **δ**, **ι**, **Path**, **Face**,
**Glue** and **Split** according to the native node shape, plus **WHNF** and
**Normalize** for the selected subtree. Relevant immediate-parent operations
say so in their labels. Suggestions do no reduction while navigating;
**Try** labels mean that the kernel must check further side conditions.
The operation menu retains all rules for manual exploration.
**WHNF** computes composition, transport and Glue heads, and can eta-contract;
**Normalize** also enters bodies. Both may perform many reductions. The **Glue**
operation is the targeted eta rule and may normalize its side conditions.
Filling elaborates to composition, whose tubes and partial elements are
navigable operands. Each request has an explicit work budget in kernel ticks,
without automatic budget increases. A refusal preserves the previous checked
view; **Back** restores its judgement. **Kernel graph** includes the actual
manual Step instructions, their premises and operand paths. These controls
use the existing kernel rules and do not change normalization behavior.

In `proof.html`, **Generated Cubist** beside Read and Edit shows a read-only
frontend expansion from the last check. Select the current file or an imported
module to see its generated theory, initial and free-model declarations in
Cubist syntax, with the same highlighting and line layout as Read. Click a
generated declaration or linked reference to open its checked term, type or
signature in the inspector; failed declarations show their diagnostic.
Original comments and unchanged declarations remain in source order. Replaced
theories and initial/free declarations appear commented out, with their
generated declarations immediately below them.
Each family is labeled checked, failed or blocked. Editing keeps
the previous expansion until **Check proof** runs again; a parse failure keeps
the previous snapshot. Modules without expansions say so explicitly.

The view retains the frontend's syntax before reference lowering, including
families that did not publish. Internal binders receive unambiguous display
aliases; public parameter labels stay intact. Identity markers such as
`c⟦1⟧`, explained above their declaration, identify captures or deferred
interpretations that ordinary source cannot express faithfully. Generated
dotted names and these annotations make this an inspection view, not a
standalone module or an alternative to **Export checked proof**.
A syntax form beyond the display's coverage or budget is identified
by declaration name instead of silently omitted. Rendering runs on demand in
the worker and does not recheck or regenerate the source.

`npm run build:site` creates a static artifact in `build/site`. GitHub Pages
publishes it at https://cubist.kanhar.art. `npm run test:site` exercises that
artifact, including workers, imports, WASM, source links, and the workbench.

The full language reference is `language.html`, an index of chapter pages in
`reference/`; a quick reference appears on the proof page. Every example in
them is checked by `tests/reference-examples.test.mjs`, and
`tests/reference-structure.test.mjs` checks their navigation and links. The test runner accepts module names, `.cubist` paths, and
individual JavaScript test files. See the root README for commands.

## Displaying terms

Source text and kernel notation show binders, variables, dimensions and the
names of definitions, types and constructors in one namespace, as the source
reads them. One rule holds for every display: in the text, every name means
what the term means by it. No binder captures a name it does not bind, and two
things the term tells apart never read alike where both are in scope. Its
implementation is `display-naming.mjs`; the printers choose no name.

Every source-text display (the elaborator's `displayText`, `displayTexts` and
`displayGoal`) names its terms by `forSource`, in four passes, in this order:

1. `explicitBinders` writes into the term every binder the printer would
   otherwise invent: a folded motive, a definition kept by name, as a function
   of the domain its checked type gives, `λ (z : D). M(z)`; a clause with fewer
   arguments, hypotheses or dimensions than its constructor takes; an
   eliminator written as a function, `λ (x : D). e(x)`. Each is an
   eta-expansion under a new name.
2. `apartFromDimensions` shows a definition named as a dimension of the term
   or of the context it is shown in (the display entry points take the
   context's dimensions) by its value: no source spelling tells the two apart,
   and a dimension the context names keeps its name.
3. `displayTerm` names every term and level binder apart from the labels and
   dimensions the term shows and the variables in its scope, never shadowing
   one around it.
4. `readableDimensions` names the dimensions decoding left unnamed apart from
   every name shown.

`sourceText` then prints the names it is given. A form the term does not spell
out, as an eta-reduced clause in a term not named so, prints in kernel
notation instead of under invented names.

Anything that adds to a term what can print a name runs before the third
pass. In #310's review, rounds 2 to 11, the printer added binders and domains
after the names were settled and renamed around them itself; each round found
the capture again for another pairing of binder, label and dimension (a match
clause, a lambda chain, a universe binder, a dimension, a context's
dimension). Writing them into the term before one naming pass replaced the
printer's renaming.

Kernel notation (`cubicalText`, `cubical-notation.mjs`) adds no binder: the
inspection's `expressionText`, the workbench and the proof page print a term
as it was checked, spelling kernel variables by their source names, and name
binders as they print, apart from the definitions, types and constructors
their bodies show (`labelsShown`); a definition named as a dimension of the
term or of the view's context (`dimensionNames`) shows by its kernel name,
`main__i`.

A display change is tested by reading its output back:
`tests/display-naming.test.mjs` prints the folded normal form of a corpus of
functions whose definitions are named as the display's own stems and
dimensions, reads each text back at its type in a fresh program, checks it is
the same function by conversion and computes alike, and does so again where
the context names each of those dimensions. Comparing printed text alone does
not catch a capture.
