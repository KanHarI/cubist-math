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
- [ ] Roadmaps still send readers to the replaced PRs. #188, #204–#211 and
  #212 were merged by mistake on 2026-10-10 and undone on main; #215–#224
  replace them. On main at `3c9090a9`, `docs/roadmaps/README.md` (branch
  work), `work-plan.md` (introduction, L2.6 row and branch-work table),
  `core-theories.md`, `inductive-language-features.md` and
  `proof-ergonomics-roadmap.md` link #188, #204–#211 or #212, some as an
  open PR. PR #217 updates the work plan's introduction and branch-work
  table; the other links remain.
