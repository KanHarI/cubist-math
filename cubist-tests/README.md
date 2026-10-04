# Cubist tests

The Cubist sources the test suite checks. Each is a module, so the proof
workspace opens it too, as `proof.html?proof=NAME`, where each case can be
checked and its derivation inspected in the Elaboration panel and the
workbench's Kernel graph.

- Every module is listed in `cubistTestModules` in
  [`web/cubist/modules.mjs`](../web/cubist/modules.mjs), and
  `tests/cubist-tests.test.mjs` checks that every file is.
- Every error and warning a module's check reports is a comment directly
  above the declaration or directive it belongs to, as
  `// Error: E606: Type mismatch: …` or `// Warning: W704: …`.
  `npm run inline-errors` writes them
  ([`tools/inline-errors.mjs`](../tools/inline-errors.mjs)), and
  `tests/cubist-tests.test.mjs` checks that they are exactly what the
  checker reports: a case that checks states nothing, and a refused case
  states its reason. A `// Refused: …` note above a case says why, in words;
  the tool keeps every comment but its own.
- A module's JavaScript test, where it has one, checks what a verdict does
  not show (an evaluation, the fuel spent, the goals shown), with
  `testModule` or `checkTestModule` from
  [`tests/check-program.mjs`](../tests/check-program.mjs), looking
  declarations up by name.
- A test module imports other test modules, then the library, then the
  archive (`web/module-resolution.mjs`). Nothing else imports a test module.
- A case meant to be refused is a declaration like any other. A module may
  hold what the linter flags, so `npm run lint:cubist` lints the library
  only.

| Module | Cases |
| --- | --- |
| [`glue`](glue.cubist) | Glue types, `glue` and `unglue`, along the library's [`contractible_maps`](../library/contractible_maps.cubist) equivalences: a line of types glued along the identity, unglue of a glue term, a piece on a face of two clauses, and the refusals of a function that is no equivalence, a misplaced value, `glue` with no Glue type and `unglue` of a point. |
| [`face_restriction`](face_restriction.cubist) | Partial elements that use a variable whose type mentions their face, which the kernel types there with `Restrict`: Glue eta for a variable, a composition whose tube is such a variable, alone, inside an application or under `typed`, and two such tubes that overlap. |
| [`declared_match`](declared_match.cubist) | `match` on declared types, for `tests/declared-match.test.mjs`: clauses against the kernel's clause types, dependent motives, path and squash clauses, structural recursion, the match statement, recursion whose other arguments vary, and each refusal. |
| [`induction`](induction.cubist) | `induction` on any declared type, for `tests/induction.test.mjs`: the expression and the statement, Nat's two forms, path constructors and function-typed recursive arguments, and the refusals and the warning. |
| [`automatic_clauses`](automatic_clauses.cubist) | For `tests/automatic-clauses.test.mjs`: a quotient's generated set squash (E4), explicit obligations, missing h-level evidence, automatic clauses in the match statement, trailing proofs, ambiguous whole-clause proofs and hlevel hints. |
| [`automatic_clauses_groupoid`](automatic_clauses_groupoid.cubist) | A groupoid's generated three-dimensional squash, with a dependent motive (E11). |
| [`automatic_clauses_without_hlevels`](automatic_clauses_without_hlevels.cubist) | A truncation's squash clause with no import of hlevels to generate it. |
| [`hlevel_lemmas`](hlevel_lemmas.cubist) | The library's h-levels at work, from the former `tests/hlevels.test.mjs`: each named level by conversion, the lemmas in a universe above U0, retracts, functions, pairs, products and subtypes, contractible types, Hedberg, and lemmas that prove no more than they state. |
| [`hlevel_tactic`](hlevel_tactic.cubist) | The hlevel tactic, for `tests/hlevel.test.mjs`: each kind of goal it proves, from evidence, hints and the type's shape, dependent path h-levels, and its refusals, each naming the first obligation nothing discharges. |
| [`hlevel_without_import`](hlevel_without_import.cubist) | hlevel with no import of hlevels, which it names. |
| [`h1_acceptance_levels`](h1_acceptance_levels.cubist) | H1 acceptance V2, V3, V5, V6, V12: a declared type's level counts stored data and relations, never a phantom parameter. |
| [`h1_acceptance_formers`](h1_acceptance_formers.cubist) | H1 acceptance V9, V10, V11: a former as a function, a signature at tier 1, and an instance at a successor level. |
| [`h1_acceptance_instances`](h1_acceptance_instances.cubist) | H1 acceptance V21, V22, V23, V29: maps between recorded instances, and universes written in the header. |
| [`h1_acceptance_paths`](h1_acceptance_paths.cubist) | H1 acceptance N5, N6, G1: path eta at a constructor, a boundary that does not hold, and no downward resizing. |
