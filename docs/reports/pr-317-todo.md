# PR #317: axiom definitions follow-up

Found while fixing the first review of #317. Both also occur on main, outside
the axiom change, and remain unfixed here.

- [ ] A module named `__proto__` crashes `CubicalProgram`, whether it is the
  main module or imported: `source.lastIndexOf is not a function`, from
  `leadingDocumentation`, since `this.sources` is a plain object.
  Reproduced on main `e7b67376` with `import __proto__;` and with a main
  module of that name. Key the sources by a `Map`, or refuse the module name.
- [ ] `simp_rule` naming a lemma applied to assumptions, an axiom among them,
  fails with "A source capture requires a closed core value." It fails
  closed, as it already does for lemmas that use assumptions. Rules over
  assumptions need a capture that carries the assumption, if wanted.

Found while fixing the second review of #317, also on main `e7b67376`:

- [ ] A truncation's universe argument displays as the binder's internal
  name, and is not instantiated in the display: after
  `def k(U < UU0, A : U, t : Trunc(U, A)) : Trunc(U, A) := t;`, `typeof k;`
  shows `forall U < UU0. forall A : U. Trunc(__U, A) -> Trunc(__U, A)` and
  `typeof k(U0);` still shows `Trunc(__U, A)`. Checking is unaffected
  (`LEM(U0)` checks against `ExcludedMiddle(U0)`); the axioms' types
  display so too, as `typeof LEM(U0, Unit);`.
- [ ] A checked file with print directives and no declaration fails
  `check` with only `<module> did not check.`: `complete` requires a
  declaration (`outputs.length > 0` in `web/cubical-program.mjs`), and no
  gap says why.
