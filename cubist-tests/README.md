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
- A value, a type or an elaborated term is a print directive, with what it
  shows in an `// Output: …` comment above it, which the tool writes and the
  test compares in the same way: `print(evaluate(e));` shows the normal form
  of a closed term, `print(typeof(e));` its type and `print(inspect(e));`
  the term the kernel checked, in kernel notation.
- A module's JavaScript test, where it has one, checks what neither a
  verdict nor a print shows (the fuel spent, the goals shown), with
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
| [`program_types`](program_types.cubist) | Nat and W as source declarations, for `tests/program-types.test.mjs`: imported Nat's constructors, literals and elimination, W's dependent eliminator computing, and a W declaration at a fixed higher universe. |
| [`program_types_nat_as_name`](program_types_nat_as_name.cubist) | Nat is an ordinary name, bound or shadowed. |
| [`program_types_constructor_shadowing`](program_types_constructor_shadowing.cubist) | A declared type's zero and succ shadow Nat's constructors, not its literals. |
| [`projections`](projections.cubist) | Projections p.1 and p.2 (L1.5, HoTT A8), for `tests/projections-let.test.mjs`: the kernel's projections with the family read from the pair's type, and misused projections. |
| [`projections_archive_helpers`](projections_archive_helpers.cubist) | Projections convert to the archive's projection helpers (HoTT A8). |
| [`let_statements`](let_statements.cubist) | let with a stated type and a proof block (HoTT B4): a restated goal, reasoning backwards, and the refusals. |
| [`path_operators`](path_operators.cubist) | Path and coordinate operators, for `tests/path-operators.test.mjs`: -p, p ++ q, -i, & and | elaborate as sym, trans, flip, meet and join do, and each says which operator failed on a non-path. |
| [`universe_generic`](universe_generic.cubist) | Universe binders and constants (L1.1, G0 §4.3), for `tests/universe-generic.test.mjs`: generic definitions at tier 0, both tiers' universes (B15), generic statements, proofs under binders, a generic assumption (D6) and inspection. |
| [`universe_generic_bounds`](universe_generic_bounds.cubist) | Universe is removed, and bounds, reserved names and universes are checked (B11–B14, B16, B17). |
| [`universe_generic_builtins`](universe_generic_builtins.cubist) | Instantiation, assumptions and builtins take universes below UU0 (S12, D4, Q10), and univalence is one generic definition. |
| [`universe_generic_rewriting`](universe_generic_rewriting.cubist) | Rewriting matches a generic rule's universe only where it is a bare variable. |
| [`inductive_values`](inductive_values.cubist) | For `tests/inductive-declarations.test.mjs` (as are the inductive_* modules below): constructors build values, computations hold by rfl, and no result carries a marker (T2). |
| [`inductive_universes`](inductive_universes.cubist) | Universe parameters: an erased one is read from its parameter, a recorded one carried (V7, V20, V26, V30). |
| [`inductive_levels`](inductive_levels.cubist) | The sort's level is the least containing its data and arities, or the one written (V27, V28). |
| [`inductive_data_first`](inductive_data_first.cubist) | Data are moved ahead of positions, and uses keep the source's order (A11). |
| [`inductive_higher`](inductive_higher.cubist) | Higher constructors: paths between constructors, used at coordinates. |
| [`inductive_rejections`](inductive_rejections.cubist) | Declarations are checked before they are admitted: each rejection names what is wrong (A4, A8, V31). |
| [`inductive_failed`](inductive_failed.cubist) | A failed declaration leaves its names untranslated and nothing admitted. |
| [`inductive_computable`](inductive_computable.cubist) | computable accepts a declared type, and refuses an assumption, naming it (T3, T4). |
| [`inductive_square`](inductive_square.cubist) | A two-dimensional constructor takes its instance from a square's type. |
| [`inductive_beta`](inductive_beta.cubist) | Constructor types are beta-reduced before they are classified and admitted. |
| [`inductive_binders`](inductive_binders.cubist) | Binders written in a constructor's result are its arguments. |
| [`inductive_former_values`](inductive_former_values.cubist) | A type former used as a value is a lambda over its universes and parameters. |
| [`inductive_instance_from_position`](inductive_instance_from_position.cubist) | Without an expected type, a constructor's instance is read from a position argument. |
| [`inductive_reduction`](inductive_reduction.cubist) | Types are checked before reduction, and level redexes reduce. |
| [`inductive_naturals`](inductive_naturals.cubist) | A declared type for other modules to import. |
| [`inductive_telescope`](inductive_telescope.cubist) | A declared type with a telescope of parameters, for another module to import. |
| [`inductive_imports`](inductive_imports.cubist) | Imported declared types are used by name, with no marker; each module numbers its own names. |
| [`inductive_shape_errors`](inductive_shape_errors.cubist) | Shape errors name the constructor and its argument, where they are. |
| [`inductive_no_marker`](inductive_no_marker.cubist) | Inspection shows no marker. |
| [`inductive_path_lambda`](inductive_path_lambda.cubist) | A path lambda at a point is contracted in constructor types. |
| [`inductive_projections`](inductive_projections.cubist) | Projections contract, and constructor-headed rules simplify, in constructor types. |
| [`inductive_trunc_minus_one`](inductive_trunc_minus_one.cubist) | trunc(-1) is prop (V31). |
| [`inductive_inspection`](inductive_inspection.cubist) | Inspection: a declared type's constructors and its eliminator's clause types. |
| [`inductive_inspection_names`](inductive_inspection_names.cubist) | Inspection: names are distinct, clause types whole, and repeated inspection keeps no state. |
| [`inductive_generated_names`](inductive_generated_names.cubist) | Inspection: generated names print as themselves after every round of suffixes. |
| [`inductive_printed_forms`](inductive_printed_forms.cubist) | Inspection: generated names avoid the printed form of every name. |
| [`inductive_assumptions`](inductive_assumptions.cubist) | Inspection: no declared type mentions an assumption, and each refusal names it. |
| [`inductive_one_parameter_name`](inductive_one_parameter_name.cubist) | Inspection: a parameter has one name in the whole view, and T.squash is distinct from squash. |
| [`computability`](computability.cubist) | For `tests/computability.test.mjs`: a computable declaration is refused when it depends on an assumption, naming the path, and its dependents with it. |
| [`computability_evaluation`](computability_evaluation.cubist) | evaluate checks the normal form of a closed, assumption-free term; each failed evaluation's error is stated above it. |
| [`computability_unfolding`](computability_unfolding.cubist) | Evaluation unfolds every definition and ignores unfolding hints. |
| [`induction_printed`](induction_printed.cubist) | How an eliminator prints, for `tests/induction.test.mjs`: as the induction that builds it, with `__U` for an erased universe, and the printed source written back. |
| [`ergonomics_rewrite_obligations`](ergonomics_rewrite_obligations.cubist) | `rw` at an occurrence, in reverse and on either side, and the refusals of a missing occurrence and a dependent position. |
| [`ergonomics_simp_rejections`](ergonomics_simp_rejections.cubist) | `simp` stops on a cycle, and does not prove a false equality or a loop equal to reflexivity. |
| [`ergonomics_simpa_reconstruction`](ergonomics_simpa_reconstruction.cubist) | `simpa` reconstructs the stated equality, and refuses a false supplied term. |
| [`ergonomics_type_transport_rejections`](ergonomics_type_transport_rejections.cubist) | `simpa` transports only along paths of types: no path, functions that are no type path, a nontrivial loop. |
| [`ergonomics_simp_child_order`](ergonomics_simp_child_order.cubist) | `simp` tries the rules at each child before rewriting its parent. |
| [`ergonomics_simp_incompatible_candidate`](ergonomics_simp_incompatible_candidate.cubist) | A quantified rule whose parameter type does not fit leaves the later rules available. |
| [`ergonomics_grouped_binder_shadowing`](ergonomics_grouped_binder_shadowing.cubist) | A grouped binder checks its shared domain before a binder shadows that name. |
| [`ergonomics_grouped_universes`](ergonomics_grouped_universes.cubist) | Grouped universe binders bind as separate ones do. |
| [`ergonomics_mixed_universes`](ergonomics_mixed_universes.cubist) | Consecutive mixed universe groups bind every parameter, for the binder link of `tests/proof-ergonomics.test.mjs`. |
| [`ergonomics_generic_calc`](ergonomics_generic_calc.cubist) | A generic `calc`, whose endpoint and step links `tests/proof-ergonomics.test.mjs` inspects and exports. |
| [`ergonomics_generic_proof_locals`](ergonomics_generic_proof_locals.cubist) | Generic proofs whose `ext` and simplified hypothesis binders `tests/proof-ergonomics.test.mjs` links. |
| [`ergonomics_generic_failure`](ergonomics_generic_failure.cubist) | A failed use of a generic definition leaves the definition and later uses intact. |
| [`ergonomics_repeated_match`](ergonomics_repeated_match.cubist) | A quantified simp rule matches a repeated parameter consistently. |
| [`ergonomics_invalid_registry`](ergonomics_invalid_registry.cubist) | Registrations of rules that are no equalities, and sets of them, are refused and enter no rule set. |
| [`ergonomics_local_simp`](ergonomics_local_simp.cubist) | `without` removes default rules and sets, `simp at h as h2` keeps the source hypothesis, and a global name is no hypothesis. |
| [`ergonomics_conditional_simp`](ergonomics_conditional_simp.cubist) | A conditional rule with a selected, missing, reflexive or wrong premise. |
| [`ergonomics_nested_premises`](ergonomics_nested_premises.cubist) | Premises simplified with nested witnesses, and the refusals without a base rule or with the rule alone. |
| [`ergonomics_rule_diagnostics`](ergonomics_rule_diagnostics.cubist) | Rewrite errors at the rule they name, and an unproved premise explained. |
| [`ergonomics_calc_step_links`](ergonomics_calc_step_links.cubist) | Each `calc` step, whose `by` link `tests/proof-ergonomics.test.mjs` checks. |
| [`ergonomics_binder_sites`](ergonomics_binder_sites.cubist) | `fun` and `forall`, bare and parenthesized, linked from their keywords. |
| [`ergonomics_generic_tactic_links`](ergonomics_generic_tactic_links.cubist) | Generic `calc`, `rw` and `simp`, linked to their checked witnesses. |
| [`ergonomics_freeze_premise_search`](ergonomics_freeze_premise_search.cubist) | A `simp` whose frozen form is withheld, as removing a rule changes its premise search. |
| [`ergonomics_freeze_set_collision`](ergonomics_freeze_set_collision.cubist) | A `simp` whose frozen form is withheld, as a named set shadows its rule. |
| [`ergonomics_freeze_witness`](ergonomics_freeze_witness.cubist) | Hypotheses simplified, whose frozen forms keep the witness a later proof compares. |
| [`ergonomics_search_time_scope`](ergonomics_search_time_scope.cubist) | Statements after `rw`, `simp` and a `calc` step, outside their search time. |
| [`ergonomics_simp_dependent_positions`](ergonomics_simp_dependent_positions.cubist) | `simp` skips matches in dependent positions instead of failing. |
| [`ergonomics_rewrite_eligible_rhs`](ergonomics_rewrite_eligible_rhs.cubist) | `rw` skips an unsupported left occurrence for an eligible right one. |
| [`ergonomics_generated_names`](ergonomics_generated_names.cubist) | Generated names stay distinct when a source name ends in a digit. |
| [`ergonomics_rule_scope_rules`](ergonomics_rule_scope_rules.cubist) | A generic definition simplified with its own module's set, for `ergonomics_rule_scope`. |
| [`ergonomics_rule_scope`](ergonomics_rule_scope.cubist) | A generic definition keeps its defining set where the set's name means another. |
| [`ergonomics_simp_freeze_path_identity`](ergonomics_simp_freeze_path_identity.cubist) | A `simp` offered no frozen form, as a later proof compares its path. |
| [`ergonomics_simpa_freeze_path_identity`](ergonomics_simpa_freeze_path_identity.cubist) | A `simpa` offered no frozen form, as a later proof compares its path. |
| [`ergonomics_simp_type_freeze_path_identity`](ergonomics_simp_type_freeze_path_identity.cubist) | `simp` along a type path: frozen only where no later proof compares it. |
| [`ergonomics_simpa_type_freeze_path_identity`](ergonomics_simpa_type_freeze_path_identity.cubist) | `simpa` along a type path: frozen only where no later proof compares it. |
| [`ergonomics_imported_failure_rules`](ergonomics_imported_failure_rules.cubist) | A generic definition that fails, for `ergonomics_imported_failure`. |
| [`ergonomics_imported_failure`](ergonomics_imported_failure.cubist) | A use of an imported definition that failed, reported in its own module. |
| [`ergonomics_simp_rules_a`](ergonomics_simp_rules_a.cubist) | Default and named registrations of a rule, for the `ergonomics_simp_client_*` modules. |
| [`ergonomics_simp_rules_b`](ergonomics_simp_rules_b.cubist) | The same registrations at priority 7. |
| [`ergonomics_simp_client_a`](ergonomics_simp_client_a.cubist) | Imported registrations simplify. |
| [`ergonomics_simp_client_isolated`](ergonomics_simp_client_isolated.cubist) | Without the import, no registration. |
| [`ergonomics_simp_client_conflict`](ergonomics_simp_client_conflict.cubist) | Two imports of one rule and two sets of one name: only a use of the name fails. |
| [`ergonomics_simp_client_reverse_order`](ergonomics_simp_client_reverse_order.cubist) | Imports in the other order keep the higher priority. |
| [`ergonomics_simp_client_shadowed_rule`](ergonomics_simp_client_shadowed_rule.cubist) | A local definition shadows an imported rule's name: no frozen form. |
| [`ergonomics_multi_binder_fun`](ergonomics_multi_binder_fun.cubist) | Multi-binder `fun`, whose link inspects the whole closed function. |
| [`ergonomics_tactic_sites`](ergonomics_tactic_sites.cubist) | Concrete `calc`, `rw` and `simp`, linked from their keyword sites. |
| [`ergonomics_tactic_sites_generic`](ergonomics_tactic_sites_generic.cubist) | The same, universe-generic. |
| [`fuel_tactics`](fuel_tactics.cubist) | Tactics that `tests/search-fuel.test.mjs` checks with the default fuel and with less, in fresh and reused sessions: a cycle and the rewrite budget among them. |
| [`fuel_residual_goals`](fuel_residual_goals.cubist) | Unfinished `rw`, `simp`, `simpa` and `calc`: each states the remaining goal, the side that changed and the rules that fired; the command-line checker reports the same. |
| [`fuel_search_spending`](fuel_search_spending.cubist) | Searches whose questions and rewrites `tests/search-fuel.test.mjs` counts. |
