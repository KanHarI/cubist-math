# The rebuilt library

This is the root of the rebuilt proof library (work-plan item I0.3). The
first library is kept, unchanged, in [`archive/first-library/`](../archive/first-library/).
Its results are catalogued in English in
[`docs/library-results.md`](../docs/library-results.md), which is what the
rebuild follows.

- Modules here take precedence over archive modules of the same name, in the
  command-line checker, the proof workspace and the language reference.
- Each module has one theme, and no helper is duplicated across modules.
- Every module is listed in `libraryModules` in
  [`web/mathscript/modules.mjs`](../web/mathscript/modules.mjs), and
  `tests/library.test.mjs` checks that each checks completely.

| Module | Contents |
| --- | --- |
| [`naturals`](naturals.cubist) | Addition, multiplication and order on `Nat`, with the basic laws of addition. `+`, `*`, `<` and `<=` need it. |
