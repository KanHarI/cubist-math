# PR #334: EVAL7 part two follow-up

Found while moving the archive's Euclid consumers to the library's
([report](binary-euclid.md#part-two)). Both reproduce on main `27c0cc38`,
are outside EVAL7's scope, and are left unfixed here.

- [ ] **The driver's alpha equality takes a free dimension for a bound one
  in a face.** `InstructionDriver.sameFormula` renames the right side's
  bound dimensions to the left side's, but leaves a free dimension's index
  as it is, so a face that names a bound dimension on one side and a free
  dimension of the same index on the other compares equal. Over raw
  syntax, with `plam(d, body)` a path abstraction binding `d` and
  `comp(k, d)` a composition binding `k` whose one tube has the face
  `d = 0`, the driver answers `alpha(plam(2, comp(3, 2)), plam(1, comp(3, 2)))`
  true: the left face names its bound dimension, the right face a free one.
  Terms compare names correctly (`sameName`, where a binding on either side
  decides); faces need the same rule. This change fixed a neighbouring case,
  a binding pruned before its face was compared (the probe is in the
  report).
- [ ] **`tests/cubical.browser.mjs` stops at a strict-mode violation.**
  `workbench.locator("details summary").click()` resolves to two elements
  since the workbench gained its "Native AST subtree" section
  (`179c883b`, 2026-10-20). CI does not run this file
  (`npm run test:browser:cubical`); every step before that line passes,
  the Euclid steps among them. `#mathematical-view details > summary`, as
  `tests/cubical-inspector.browser.mjs` writes it, selects the one meant.
