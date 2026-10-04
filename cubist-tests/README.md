# Cubist tests

The Cubist sources the test suite checks. Each is a module, so the proof
workspace opens it too, as `proof.html?proof=NAME`, where each case can be
checked and its derivation inspected in the Elaboration panel and the
workbench's Kernel graph.

- Every module is listed in `cubistTestModules` in
  [`web/cubist/modules.mjs`](../web/cubist/modules.mjs), and
  `tests/cubist-tests.test.mjs` checks that every file is.
- A module's JavaScript test checks it with `checkTestModule` from
  [`tests/check-program.mjs`](../tests/check-program.mjs), and looks its
  declarations up by name.
- A test module imports other test modules, then the library, then the
  archive (`web/module-resolution.mjs`). Nothing else imports a test module.
- A case meant to be refused is a declaration like any other; its test says
  which reason, and which code, it is refused with. A module may hold what
  the linter flags, so `npm run lint:cubist` lints the library only.

| Module | Cases |
| --- | --- |
| [`glue`](glue.cubist) | Glue types, `glue` and `unglue`, along the library's [`contractible_maps`](../library/contractible_maps.cubist) equivalences: a line of types glued along the identity, unglue of a glue term, a piece on a face of two clauses, and the refusals of a function that is no equivalence, a misplaced value, `glue` with no Glue type and `unglue` of a point. |
| [`face_restriction`](face_restriction.cubist) | Partial elements that use a variable whose type mentions their face, which the kernel types there with `Restrict`: Glue eta for a variable, a composition whose tube is such a variable, alone, inside an application or under `typed`, and two such tubes that overlap. |
| [`declared_match`](declared_match.cubist) | `match` on declared types, for `tests/declared-match.test.mjs`: clauses against the kernel's clause types, dependent motives, path and squash clauses, structural recursion, the match statement, recursion whose other arguments vary, and each refusal. |
