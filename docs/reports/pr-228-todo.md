# PR #228: defects shared with main

Found while reviewing PR #228 (separate induction hypotheses) and reproduced
on main at `7f9c4312`. They are not fixed by that PR.

- [ ] A clause that `web/translator/match.mjs` elaborates directly accepts
  the same name twice: `match t { leaf => 0; node(l, d, l) => d; }` checks,
  the later `l` shadowing the earlier. E570 (… is bound twice in this
  clause) is reported only for matches compiled by
  `web/translator/patterns.mjs`. Appended induction hypotheses,
  `node(l, d, r, l, j)`, and since PR #228 `node(l, d, r) with l, j`,
  shadow a field the same way.
- [ ] A directive's references are recorded with the declaration after it.
  `CubicalProgram` collects references in one pending list and records it
  when a declaration finishes (`web/cubical-program.mjs`, `onDeclaration`),
  so the bindings and links of an `evaluate` or `print` go to the next
  declaration, and those of a last directive are dropped. For this reason
  `tools/migrate-induction-hypotheses.mjs` migrates declarations only and
  reports the induction clauses of directives.
