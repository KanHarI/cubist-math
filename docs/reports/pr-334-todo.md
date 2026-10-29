# PR #334: EVAL7 part two follow-up

Found while moving the archive's Euclid consumers to the library's
([report](binary-euclid.md#part-two)). Neither involves EVAL7's modules;
both are outside its scope and left unfixed here. The first reproduces on
main `27c0cc38`.

- [ ] **`tests/cubical.browser.mjs` stops at a strict-mode violation.**
  `workbench.locator("details summary").click()` resolves to two elements
  since the workbench gained its "Native AST subtree" section
  (`179c883b`, 2026-10-20). CI does not run this file
  (`npm run test:browser:cubical`); every step before that line passes,
  the Euclid steps among them. `#mathematical-view details > summary`, as
  `tests/cubical-inspector.browser.mjs` writes it, selects the one meant.
- [ ] **The Cubist tests' benchmark lists five checked declarations as
  failed.** Recorded again on a clean tree (`8b60b7e9`), the saved benchmark
  of `cubist-tests/` counts `notation_literals.rational_add`,
  `notation_pilots.five_sixths`, `ergonomics_generated_names.aliased`,
  `equivalence_from_inverse.path_cancel_right_at` and
  `truncation_resize.rejected` as "Needs fixing" (a notation not selected,
  a renamed bound variable, a context symbol named twice), while the test
  suite checks each module as stated. The benchmark checks every module in
  one session; none of the five involves EVAL7's modules. Under machine
  load a first recording also failed five more, on notation selection and
  parameter inference.
