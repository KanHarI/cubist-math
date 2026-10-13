# PR #218: defects shared with main

Found while reviewing PR #218 (FG1 declaration ownership) and reproduced on
main at `3c9090a9`. They are not fixed by that PR.

- [ ] A local declaration does not hide the members of an imported theory
  of the same name. With a module `fixture` that declares
  `import hlevels; theory T(U < UU0) { M : set U; c : M; }`, a file
  `import fixture;` with a local `T` that has no member `c`, then
  `def p := T.c;`, checks `p` against `fixture__T.c`. This holds for a
  local definition (`def T : Unit := tt;`) and for a local theory, whether
  it checks (`theory T(U < UU0) { M : set U; other : M; }`), fails to
  expand (`bad : Missing;`, E343) or fails to check
  (`x : M; bad_eq : x = tt;`, E606). PR #218 leaves these cases as they are
  on main; only a theory, initial or free model that it refuses as a
  duplicate (E872) refuses the imported `T.*` names.
- [ ] A notation rule that names a missing member of a name in scope
  reports the rule's internal key. With `def T : Unit := tt;` and
  `notation broken { x + y := T.c(x, y); }`, the client
  `def c := broken.(tt + tt);` reports E343
  `Untranslated name: \0notation broken T.c`, with a NUL byte for `\0`.
  The rule reads `T` under its key (`\0notation broken T`) and keeps `.c`
  after it; E343's message in `web/translator/translate.mjs` prints that
  key as it is, whereas E340's names a rule's name as the rule writes it.
  A name that is not in scope at all (`Nope(x, y)`) reports
  `Untranslated name: Nope`.
