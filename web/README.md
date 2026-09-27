# Cubist website and workbench

Run `make serve`, then open http://127.0.0.1:8088/. The site uses the cubical C
kernel compiled to WebAssembly; there is no alternate checking backend.
The archived first library lives in `../archive/first-library/*.cubist`; the site serves it at `archive/first-library/`.

The source inspector retains definition names, context variables, and axiom
labels. **Open in workbench** replays the source in a fresh kernel session.
**Back to Cubist** restores the source selection. Folded notation is a display
choice; raw syntax and native opcode assembly remain available. Beta and delta
buttons highlight applicable occurrences, and every selected reduction is
checked for definitional equality. **Un-highlight** clears visual selection.

`npm run build:site` creates a static artifact in `build/site`. GitHub Pages
publishes it at https://cubist.kanhar.art. `npm run test:site` exercises that
artifact, including workers, imports, WASM, source links, and the workbench.

The full language reference is `language.html`, an index of chapter pages in
`reference/`; a quick reference appears on the proof page. Every example in
them is checked by `tests/reference-examples.test.mjs`, and
`tests/reference-structure.test.mjs` checks their navigation and links. The test runner accepts module names, `.cubist` paths, and
individual JavaScript test files. See the root README for commands.
