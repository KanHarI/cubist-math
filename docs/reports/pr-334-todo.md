# PR #334: EVAL7 part two follow-up

Found while moving the archive's Euclid consumers to the library's
([report](binary-euclid.md#part-two)). It reproduces on main `27c0cc38`, is
outside EVAL7's scope, and is left unfixed here.

- [ ] **`tests/cubical.browser.mjs` stops at a strict-mode violation.**
  `workbench.locator("details summary").click()` resolves to two elements
  since the workbench gained its "Native AST subtree" section
  (`179c883b`, 2026-10-20). CI does not run this file
  (`npm run test:browser:cubical`); every step before that line passes,
  the Euclid steps among them. `#mathematical-view details > summary`, as
  `tests/cubical-inspector.browser.mjs` writes it, selects the one meant.
