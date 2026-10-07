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
| [`arguments`](arguments.cubist) | Holes `_` and named arguments `x := e` (L4.1a): holes solved from the arguments' types and the expected type, path endpoints, lambdas that wait for their type, nested holes, named arguments in any order and partial application, and the refusals: a hole nothing determines, a universe cumulativity leaves open, a solution that would mention a bound variable, universe holes, unknown or repeated names, builtins, constructors and local functions. |
| [`implicit_parameters`](implicit_parameters.cubist) | Implicit parameters `{…}` and universe holes (L4.1b): implicit arguments read off the others, named ones, the library's lists, recursion that passes them unchanged, universes inferred as the least the call needs, bounds on both sides, and the refusals: a type cumulativity leaves open, a universe the call's type depends on that nothing bounds, and an implicit parameter given by position. |
| [`patterns`](patterns.cubist) | Patterns (L2.2a): a match on several values, nested patterns, variables and `_` in a constructor's place, a constructor without arguments inside a pattern, recursion on the first value, the statement form on two values, `_` over a path constructor, an expected type that mentions the value, and the refusals: a missing case, a clause never reached, a clause with too few patterns, and a constructor matched against a value of no declared type. |
| [`sum_match`](sum_match.cubist) | The match statement on a sum, which replaced `cases`: clauses `left(a)` and `right(b)`, or `cases`' `left a`, each proving the goal at its side; a goal after `intro` kept as the motive; a hypothesis about the value taken at each side; and the refusals: another clause name, a side twice, two names, a missing side, and `induction` on a sum. |
| [`glue`](glue.cubist) | Glue types, `glue` and `unglue`, along the library's [`contractible_maps`](../library/contractible_maps.cubist) equivalences: a line of types glued along the identity, unglue of a glue term, a piece on a face of two clauses, and the refusals of a function that is no equivalence, a misplaced value, `glue` with no Glue type and `unglue` of a point. |
| [`face_restriction`](face_restriction.cubist) | Partial elements that use a variable whose type mentions their face, which the kernel types there with `Restrict`: Glue eta for a variable, a composition whose tube is such a variable, alone, inside an application or under `typed`, and two such tubes that overlap. |
| [`declared_match`](declared_match.cubist) | `match` on declared types, for `tests/declared-match.test.mjs`: clauses against the kernel's clause types, dependent motives, path and squash clauses, structural recursion, the match statement, recursion whose other arguments vary, and each refusal. |
| [`declared_induction`](declared_induction.cubist) | `induction` on any declared type, for `tests/induction.test.mjs`: the expression and the statement on the library's lists, Nat's two forms, path constructors and function-typed recursive arguments, and the refusals and the warning. |
| [`automatic_clauses`](automatic_clauses.cubist) | For `tests/automatic-clauses.test.mjs`: the generated set squash (E4) of the library's quotients, explicit obligations, missing h-level evidence, automatic clauses in the match statement, trailing proofs, ambiguous whole-clause proofs and hlevel hints. |
| [`automatic_clauses_groupoid`](automatic_clauses_groupoid.cubist) | A groupoid's generated three-dimensional squash, with a dependent motive (E11). |
| [`theories`](theories.cubist) | Theories (L2.4): sorts, operations with notation and laws; models built field by field and read by `m.f`, computing; parents' models; extension with a shared ancestor, labels and renaming; `open` and its notation; and the refusals: a field twice, a notation on a constant or out of order, one operator for two operations, two parents' fields of one name, an unknown parent or field, `open` of a non-model, a missing field, and a theory used as a term. |
| [`theory_morphisms`](theory_morphisms.cubist) | Homomorphisms and isomorphisms (L2.4): built field by field, their fields' types, identity, composition and a parent's homomorphism computing on closed models, isomorphisms' identity, composition and inverse, and a theory whose operation takes a non-sort, which has none. |
| [`theory_sections`](theory_sections.cubist) | Sections (L2.4): a model opened for each statement and proof, earlier definitions applied to the section's parameters, what they are outside, a section whose parameter is no model, and the refusals: a parameter of the section's name, and an implicit parameter of a definition's own. |
| [`theory_headers`](theory_headers.cubist) | A theory's header (L2.4c): carriers in two universes with homomorphisms across them, a parameter that every model shares and homomorphisms keep, a child taking its parent's parameter by name, and the refusals: a parent's universe or parameter missing, a binder bound twice or named as a field. |
| [`theory_variance`](theory_variance.cubist) | Homomorphisms by variance (L2.4c): inputs with no carrier kept, a parameter's elements kept, covariant inputs and results pushed forward, a contravariant input pulled back, identity and composition computing, and the refusals of an input mixed in a carrier and of a contravariant result. |
| [`theory_families`](theory_families.cubist) | Theory families (L2.4c): a monad on sets with the identity monad as a model, its homomorphisms and isomorphisms computing; a preorder whose homomorphisms are monotone; a graded family; a family of sets indexed by a carrier, with homomorphisms and no isomorphisms; and the refusals of a law over a family with no h-level and of an index given without its evidence. |
| [`theory_independent`](theory_independent.cubist) | Independent parents (L2.4c): two theories with one carrier and one operator, and a theory that is both without changing either; carriers merged, fields and operators of one name ambiguous where used and reached through labels, a renamed notation, homomorphisms named by label, and carriers of different kinds refused. |
| [`theory_use`](theory_use.cubist) | Selecting a model's notation (L2.4c): `use` in a block and at a file's top level, switched by a later one; `m.(e)`; qualified operators with their precedence and alone; a parent's operator through its label, inside a theory and on a model; and the refusals of an ambiguous operator, a qualifier that is no model, an operator its theory does not bind, and a `use` of no model. |
| [`notation_views`](notation_views.cubist) | Named notations (L2.10a): the library's `nat`, a notation of one's own, its rules read where declared, the operation alone, two models on one carrier, nested selections, and the refusals of an operator a selection does not bind. |
| [`notation_operators`](notation_operators.cubist) | Operators, operand views and derived operations (L2.10b): `-`, `/`, `^`, unary `-`, `>` and `>=`, their grouping, an exponent read in `nat`, a derived subtraction, the integers' negation and subtraction, qualified negation, and the refusals of an operator no selection binds, `-p` as reversal, and an operand with no view. |
| [`notation_literals`](notation_literals.cubist) | Literals in a selected notation (L2.10c): the rationals' literal rule reading `1/2`, `0.75` and `1_000/4` and refusing `1/0` at its denominator, the integers' numerals, a theory's numeral rule computing, and the refusals of a numeral where no rule reads it and of a literal `nat` cannot read. |
| [`notation_printing`](notation_printing.cubist) | Faithful printing (L2.10d): an operation printed with its operator where its notation is selected and qualified elsewhere, a literal printed as written, a numeral rule's application printed as the numeral where selected, and a printed text read back where it was printed. |
| [`notation_pilots`](notation_pilots.cubist) | The notation roadmap's pilots (L2.10e): its proposed examples on the integers, rationals and algebra, checked, with a rational equation proved by deciding it, and the refusal of `1/0`. |
| [`algebra_models`](algebra_models.cubist) | The library's `algebra` at work: powers of two a homomorphism from the natural numbers' additive monoid to their multiplicative one, evaluated, with its monoid homomorphism and a composite, and a group lemma's statement outside its section. |
| [`integer_examples`](integer_examples.cubist) | The library's integers at work: equality decided and arithmetic computed on closed integers, a commutative ring's lemma at the integers, and the natural numbers embedded as a homomorphism of additive monoids. |
| [`rational_examples`](rational_examples.cubist) | The library's rationals at work: sums, equal fractions and the inverse of a negative fraction, decided by computation, and a ring lemma at the rationals' ring. |
| [`theories_without_hlevels`](theories_without_hlevels.cubist) | A theory's sorts without `hlevels`, which its model type names. |
| [`quotient_effectiveness`](quotient_effectiveness.cubist) | Effective quotients: the natural numbers modulo parity, whose related elements are exactly those with equal classes, computed on closed classes; distinct classes; relatedness to an element as a proposition at each class; propositional extensionality, with transport along it; and the set of propositions. |
| [`automatic_clauses_without_hlevels`](automatic_clauses_without_hlevels.cubist) | A truncation's squash clause with no import of hlevels to generate it. |
| [`hlevel_lemmas`](hlevel_lemmas.cubist) | The library's h-levels at work, from the former `tests/hlevels.test.mjs`: each named level by conversion, the lemmas in a universe above U0, retracts, functions, pairs, products and subtypes, contractible types, Hedberg, and lemmas that prove no more than they state. |
| [`hlevel_tactic`](hlevel_tactic.cubist) | The hlevel tactic, for `tests/hlevel.test.mjs`: each kind of goal it proves, from evidence, hints and the type's shape, dependent path h-levels, and its refusals, each naming the first obligation nothing discharges. |
| [`hlevel_rules`](hlevel_rules.cubist) | `hlevel_rule`: registered lemmas whose statements match a carrier, with parameters read from the match and premises proved in turn; quantified evidence and hints as rules; lemmas that are no rule. |
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
| [`path_operators`](path_operators.cubist) | Path and coordinate operators, for `tests/path-operators.test.mjs`: ~p, p ++ q, ~i, & and | elaborate as sym, trans, flip, meet and join do, and each says which operator failed on a non-path. |
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
| [`evaluate_patterns`](evaluate_patterns.cubist) | `evaluate … expecting` a pattern: holes, pairs, injections and constructors matched part by part, other expressions by normal form, and the part a mismatch names. |
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
| [`program_generic_once`](program_generic_once.cubist) | A universe-generic definition, one kernel definition instantiated at each level. |
| [`program_shadow_first`](program_shadow_first.cubist) | A value that `program_shadow_second` defines again. |
| [`program_shadow_second`](program_shadow_second.cubist) | The second value. |
| [`program_shadowing`](program_shadowing.cubist) | A shadowed import cannot retarget a definition checked before it. |
| [`program_assumptions`](program_assumptions.cubist) | Assumptions explicit and minimal, for the inspection and replay of `tests/cubical-program.test.mjs`. |
| [`program_unfolding_hints`](program_unfolding_hints.cubist) | `with unfolding`: checked definitions only, its body checked apart, and no false path. |
| [`program_unfolding_scopes`](program_unfolding_scopes.cubist) | Unfolding scopes close local variables and interval coordinates. |
| [`program_optimizations`](program_optimizations.cubist) | Path proofs and refusals that every combination of the kernel's optimization switches checks alike. |
| [`program_generic_identity`](program_generic_identity.cubist) | A generic definition, for `program_generic_caller`. |
| [`program_generic_caller`](program_generic_caller.cubist) | Calls of an imported generic definition, linked to it. |
| [`program_unused_generic`](program_unused_generic.cubist) | Unused generic definitions, whose locals inspect and replay under the universe binder. |
| [`program_untyped_generic`](program_untyped_generic.cubist) | Untyped lambdas, refused in generic definitions and ordinary ones, without stopping later declarations. |
| [`wasm_binary_literal`](wasm_binary_literal.cubist) | The binary naturals checked in WASM, and a false binary literal equation refused. |
| [`wasm_bad_factorial`](wasm_bad_factorial.cubist) | A false factorial value, refused. |
| [`wasm_invalid_paths`](wasm_invalid_paths.cubist) | Paths, compositions and pushout eliminations with wrong boundaries, refused. |
| [`wasm_moving_maps`](wasm_moving_maps.cubist) | A path constructor of the declared pushout transported along changing maps, with its boundary corrected. |
| [`wasm_suspension_use`](wasm_suspension_use.cubist) | Suspension induction through a proved PathP bridge. |
| [`driver_first_proof`](driver_first_proof.cubist) | The first proof, whose derivations `tests/instruction-driver.test.mjs` walks in instruction mode, and whose `lt_succ` the workbench lists as a judgement graph. |
| [`driver_sums`](driver_sums.cubist) | Constructors at a type that reduces, derived as their source. |
| [`dimension_regression`](dimension_regression.cubist) | Finite dimensions, zero included, unique for arbitrary bases, without choice. |
| [`dimension_degree_regression`](dimension_degree_regression.cubist) | Extension degree: positive, one for the identity, invariant under extension equality. |
| [`dimension_tower_regression`](dimension_tower_regression.cubist) | The product basis and the numerical tower law, for arbitrary fields and a commuting triangle. |
| [`dimension_invalid`](dimension_invalid.cubist) | Dimension chooses no basis, keeps linearity and a tower's embedding: four refusals. |
| [`algebraic_extensions_invalid_embedding_claims`](algebraic_extensions_invalid_embedding_claims.cubist) | Embedding claims the archive does not make, refused: into a target that is not algebraically closed, and one embedding for every separable extension. |
| [`algebraic_extensions_invalid_f4_root`](algebraic_extensions_invalid_f4_root.cubist) | Zero is no root of the formal F2 polynomial whose F4 roots are 2 and 3. |
| [`finite_spanning_finite_tower_regression`](finite_spanning_finite_tower_regression.cubist) | Arbitrary finite subspaces have bases and finiteness descends both ways in a tower. |
| [`finite_spanning_invalid_spanning`](finite_spanning_invalid_spanning.cubist) | Finite extraction does not choose a basis or equate finiteness with independence. |
| [`finite_spanning_spanning_regression`](finite_spanning_spanning_regression.cubist) | Finite spanning families contain an indexed subfamily basis without choice. |
| [`linear_algebra_basis_regression`](linear_algebra_basis_regression.cubist) | Finite bases give unique coordinates and cubical carrier transport without choice. |
| [`linear_algebra_chain_regression`](linear_algebra_chain_regression.cubist) | Spans are least subspaces and independent chains have bounds, including empty and U1-indexed chains. |
| [`linear_algebra_general_basis_regression`](linear_algebra_general_basis_regression.cubist) | The general basis theorem derives maximality from choice, with its exact assumptions visible. |
| [`linear_algebra_invalid_basis_selection`](linear_algebra_invalid_basis_selection.cubist) | Basis existence cannot silently select a basis or justify adjoining the zero vector. |
| [`linear_algebra_invalid_linear`](linear_algebra_invalid_linear.cubist) | Nonlinear constant maps and a silently changed basis length are rejected. |
| [`linear_algebra_s3_regression`](linear_algebra_s3_regression.cubist) | S3 has six elements and a genuinely non-normal point stabilizer, without axioms. |
| [`polynomial_algebra_adjoined_root_regression`](polynomial_algebra_adjoined_root_regression.cubist) | Adjoined roots and embeddings into a root field are constructed, not assumed. |
| [`polynomial_algebra_invalid_polynomial_claims`](polynomial_algebra_invalid_polynomial_claims.cubist) | Zero polynomial is excluded from root bounds and division by zero. |
| [`polynomial_algebra_polynomial_regression`](polynomial_algebra_polynomial_regression.cubist) | Formal division, uniqueness, root bounds and Bezout are checked without extra axioms. |
| [`quotient_groups_invalid_quotient`](quotient_groups_invalid_quotient.cubist) | Quotient construction rejects omitted normality and silent universe lowering. |
| [`quotient_groups_quotient_regression`](quotient_groups_quotient_regression.cubist) | Quotient groups and the first isomorphism theorem check constructively across universes. |
| [`quotient_universal_hom_universe_regression`](quotient_universal_hom_universe_regression.cubist) | The homomorphism universe schemas at U0 to U3, each computable, and agreeing with small homomorphisms. |
| [`quotient_universal_regression`](quotient_universal_regression.cubist) | The quotient universal property for a genuinely U1 target, without representative choice. |
| [`quotient_universal_bad_factorization`](quotient_universal_bad_factorization.cubist) | A factorization without the subgroup-killing hypothesis, refused. |
| [`h1_cauchy_quotient`](h1_cauchy_quotient.cubist) | The H1 migration of the archive's `cauchy_quotient` (see [`docs/roadmaps/h1-truncation-migration.md`](../docs/roadmaps/h1-truncation-migration.md)): Cauchy sequences with moduli and their equivalence relation over the declared truncation, still on the archive's fields and predicate quotient. |
| [`h1_zorn_step`](h1_zorn_step.cubist) | The H1 migration of a step of the archive's `zorn_chain_complete`: maximal elements, strict successors and double negation at U1 over the declared truncation, still on the archive's Bourbaki–Witt development. |
| [`truncation_small_mere`](truncation_small_mere.cubist) | G2: `small_mere_eliminate` into U1 through the declared eliminator, computable. |
| [`truncation_cauchy_same`](truncation_cauchy_same.cubist) | G5: the rebuilt `CauchySame` and `EventualClose` in U0, computable. |
| [`truncation_resize`](truncation_resize.cubist) | G6: resizing a proposition with LEM alone, and a `StrictlyAbove` witness refused set evidence. |
| [`truncation_strict_successor`](truncation_strict_successor.cubist) | G7: `no_maximal_strict_successor`, double negation at U1, LEM retained. |
| [`truncation_rebuilt_classical`](truncation_rebuilt_classical.cubist) | Rebuilt classical assumptions beside the legacy signatures, and a false truncation former refused. |
| [`printer_lint`](printer_lint.cubist) | The printer's values and types of matches, inductions, binders and declared types, which `tests/printer-lint.test.mjs` lints: eliminators print as the match or induction that builds them. |
| [`translation_failed_proofs`](translation_failed_proofs.cubist) | A failed proof becomes no axiom: a use of it fails, and the rest checks. |
| [`translation_path_induction`](translation_path_induction.cubist) | Weak J from composition and singleton contraction. |
| [`translation_weak_j`](translation_weak_j.cubist) | Weak J has no strict reflexivity beta rule. |
| [`mismatch_source_syntax`](mismatch_source_syntax.cubist) | Mismatches in source syntax, without module prefixes, generated suffixes or redexes. |
| [`mismatch_calc_naming`](mismatch_calc_naming.cubist) | `calc` names the two terms it shows together, apart from a captured label. |
| [`source_text_messages`](source_text_messages.cubist) | Messages, evaluations and prints in source syntax. |
| [`inspection_declared_types`](inspection_declared_types.cubist) | Declared types linked to their imported and local declarations. |
| [`inspection_shadowed_nat`](inspection_shadowed_nat.cubist) | Names that shadow the natural numbers' type, linked to their own declarations. |
| [`inspection_axiom_labels`](inspection_axiom_labels.cubist) | An assumption's label and a derived helper, inspected. |
| [`inspection_let_alias`](inspection_let_alias.cubist) | A let alias keeps the original local's name. |
| [`assembly_fixture`](assembly_fixture.cubist) | Declarations whose kernel assembly `tests/cubical-assembly.test.mjs` lists. |
| [`assembly_generic_assumptions`](assembly_generic_assumptions.cubist) | A generic assumption, one kernel entry used at two levels. |
| [`glue_printed`](glue_printed.cubist) | A Glue line as the printer shows it, written back: it checks, and equals the line. |
| [`admission_two`](admission_two.cubist) | Definitions whose admission and derivation `tests/instruction-admission.test.mjs` watches. |
| [`reduction_demo`](reduction_demo.cubist) | Declarations that `tests/cubical-reduction.test.mjs` reduces by delta and beta steps. |
| [`f4_extension_loops`](f4_extension_loops.cubist) | The F4 extension's loop type equals C2: each lemma of the archive that says so is computable. |
| [`f4_extension_loops_false`](f4_extension_loops_false.cubist) | The two-loop equality certifies no one-element loop type. |
| [`fingerprint_fixture`](fingerprint_fixture.cubist) | Declarations whose elaboration fingerprints `tests/elaboration-fingerprint.test.mjs` takes and compares after edits. |
| [`documentation_helper`](documentation_helper.cubist) | An imported definition documented by its comment. |
| [`documentation_use`](documentation_use.cubist) | Documentation from local and imported source: the comment directly above a declaration. |
| [`declared_match_operator_call`](declared_match_operator_call.cubist) | A recursion whose other arguments vary, with `+` given to it by a notation of the module's own; a function named `add` gives `+` no meaning. |
| [`declarations_definitions`](declarations_definitions.cubist) | Constructions and proofs checked with their bodies exposed, and a false claim refused. |
