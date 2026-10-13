# PR #218: defects shared with main

Found while reviewing PR #218 (FG1 declaration ownership) and reproduced on
main at `3c9090a9`. They are not fixed by that PR.

- [ ] A local theory does not hide the members of an imported theory of the
  same name. With a module `fixture` that declares
  `import hlevels; theory T(U < UU0) { M : set U; c : M; }`, a file
  `import fixture;` with a local `theory T` that has no field `c`, then
  `def p := T.c;`, checks `p` against `fixture__T.c`. This holds whether the
  local theory checks (`theory T(U < UU0) { M : set U; other : M; }`), fails
  to expand (`bad : Missing;`, E343) or fails to check
  (`x : M; bad_eq : x = tt;`, E606). PR #218 leaves these three cases as
  they are on main.
