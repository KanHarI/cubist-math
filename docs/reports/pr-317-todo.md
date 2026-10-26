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
