# Cubist website and workbench

Run `make serve`, then open http://127.0.0.1:8088/. The site uses the cubical C
kernel compiled to WebAssembly; there is no alternate checking backend.
The archived first library lives in `../archive/first-library/*.cubist`; the site serves it at `archive/first-library/`.

The source inspector retains definition names, context variables, and axiom
labels. **Open in workbench** replays the source in a fresh kernel session.
**Back to Cubist** restores the source selection. Folded notation is a display
option; raw syntax and native opcode assembly remain available. Beta and delta
buttons highlight applicable occurrences, and every selected reduction is
checked for definitional equality. **Un-highlight** clears visual selection.

In `proof.html`, **Generated Cubist** beside Read and Edit shows a read-only
frontend expansion from the last check. Select the current file or an imported
module to see its generated theory, initial and free-model declarations in
Cubist syntax. Each family is labeled checked, failed or blocked. Editing keeps
the previous expansion until **Check proof** runs again; a parse failure keeps
the previous snapshot. Modules without expansions say so explicitly.

The view retains the frontend's syntax before reference lowering, including
families that did not publish. Captured references use display names and
internal pattern binders get readable names. Generated dotted declaration names
and capability metadata are not ordinary source declarations, so this is an
inspection view, not a standalone module or an alternative to **Export checked
proof**. A syntax form beyond the display's coverage or budget is identified
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
