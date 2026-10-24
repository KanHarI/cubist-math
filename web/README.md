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

A term becomes source text in three passes, in this order, on every display
path (the elaborator's `displayText`, `displayTexts` and `displayGoal`):

1. `typedMotives` (`cubical-source-text.mjs`) writes each eliminator's folded
   motive, a definition kept by name, as a function of the domain its checked
   type gives, `λ (z : D). M(z)`; then `apartFromDimensions` shows a
   definition whose name is a dimension's, in the term or in the context it
   is shown in (the display entry points take the context's dimensions), by
   its value, since no source spelling tells the two apart and the dimension
   keeps its name.
2. `displayTerm` (`cubical-elaborator.mjs`) settles every binder's name, apart
   from every definition, type and constructor the term prints and every
   dimension it names, and `readableDimensions` names the dimensions decoding
   left unnamed apart from every printed name.
3. `sourceText` prints. It renames no binder the term has; the names it
   invents, a clause's arguments or an eliminator's argument, keep apart from
   what their scope prints.

Whatever a display adds to a term that can print a name, a domain, a binder or
a label, enters the term before the second pass. In #310's review, rounds 2
to 7, the printer added a folded motive's recovered domain after the names
were settled and renamed binders itself to make room for it; each round found
the capture again under another kind of binder (a match clause, a lambda
chain, a universe binder, a dimension). Moving the domain ahead of the naming
removed the printer's renaming and fixed them together.

The kernel-notation views, an inspection's `expressionText` and the
workbench's, print with `cubicalText` (`cubical-notation.mjs`), which names its
binders itself, apart from the definitions, types and constructors their
bodies show, and shows a definition named as a dimension of the term or of
the view's context by its kernel name (`main__i`); a folded normal form keeps
definitions under binders, which a full one never did.

A printer change is tested by reading its output back: print the value, check
the text at the value's type in a fresh program, and where two names could
trade meanings, evaluate the copy against the original
(`tests/folded-normal-forms.test.mjs`). Comparing printed text alone does not
catch a capture.
