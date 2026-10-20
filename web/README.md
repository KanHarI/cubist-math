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
