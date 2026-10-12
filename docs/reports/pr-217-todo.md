# PR #217: defects shared with main

Found while reviewing PR #217 (frontend-generation cases) and reproduced on
main at `3c9090a9`. They are not fixed by that PR.

- [ ] The checked-comment comparison of the Cubist test modules
  (`tools/inline-errors.mjs`, `tests/cubist-tests-inlined-*.test.mjs`)
  treats a declaration with no output as checked: it compares what the
  checker reports with the comments, and such a declaration reports
  nothing. In `def N : Unit := tt; inductive N : U0 { c; } def u : U0 := N;`
  the inductive replaces the definition (inventory finding G1), the
  definition has no output, and both the reported and the stated items are
  empty. PR #217's frontend-generation cases require each declaration
  without a comment to have an output of its own
  (`tests/frontend-generation-cases.mjs`, `missing`); the Cubist test
  modules do not.
