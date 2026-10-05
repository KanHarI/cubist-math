# The rebuilt library

This is the root of the rebuilt proof library (work-plan item I0.3). The
first library is kept in [`archive/first-library/`](../archive/first-library/)
as a reference, not relied on: where this library implements a part of it,
that part is removed from the archive and its dependents import the library
instead. Its results are catalogued in English in
[`docs/library-results.md`](../docs/library-results.md), which the rebuild
follows.

- Modules here take precedence over archive modules of the same name, in the
  command-line checker, the proof workspace and the language reference.
- Each module has one theme, and no helper is duplicated across modules.
- Every module is listed in `libraryModules` in
  [`web/cubist/modules.mjs`](../web/cubist/modules.mjs), and
  `tests/library.test.mjs` checks that each checks completely and uses exactly
  the assumptions listed for it there.
- The library is self-contained: a module here imports only modules here
  (`web/module-resolution.mjs`). An archive module may import a library
  module, as many import `nat`.
- Nothing is imported automatically: a module that uses the natural numbers,
  numerals included, imports `nat`.

| Module | Contents | Assumptions |
| --- | --- | --- |
| [`nat`](nat.cubist) | The natural numbers, `Nat` with `zero` and `succ`, with addition, multiplication and order, and the laws of addition. Numerals and `+`, `*`, `<` and `<=` need it. | None |
| [`classical_axioms`](classical_axioms.cubist) | The statements of the classical assumptions as types, `ExcludedMiddle(U)` and `AxiomOfChoice(U)`, with checks that `LEM(U)` and `Choice(U)` have them. | `LEM`, `Choice`, `Truncate` |
| [`hlevels`](hlevels.cubist) | Contractible types, propositions and sets in every universe below `UU0`, with `HasLevel(U, n, A)` defined by recursion on `n`, so that `IsSet` is level 1 by conversion. Propositions are sets, levels are cumulative, having a level is a proposition, and a retract, such as a type equivalent to another by an inverse, a function type, a type of pairs, a product or a subtype keeps the level of the types it is made from. Contractible types are closed under the same constructions except subtypes, since a subtype can be empty, and being contractible is a proposition. Negations are propositions (`not_is_prop`), and so is the decision of a proposition (`Decidable`, `decision_is_prop`). A type with decidable equality, such as `Nat`, is a set (Hedberg). | None |
| [`h1_truncation`](h1_truncation.cubist) | The propositional truncation `Trunc(U, A)` as a declared type that computes: `merely`, that it is a proposition, maps between truncations, and elimination into a proposition of any universe below `UU0`. | None |
| [`h1_classical`](h1_classical.cubist) | Excluded middle and choice stated over `Trunc`, as `LEM(Trunc, U)` and `Choice(Trunc, U)` give them; double-negation elimination for propositions, deciding a proposition, and resizing a proposition in `U1` to one in `U0`. | `LEM[h1_truncation.Trunc]`, `Choice[h1_truncation.Trunc]` |
| [`universe_automorphisms`](universe_automorphisms.cubist) | Excluded middle for `U0` holds exactly when there merely is an automorphism of `U0` sending `Unit` to `Void`, for the equivalences of [`contractible_maps`](contractible_maps.cubist), with equal types from [`univalence`](univalence.cubist)'s `glue_path`. Both directions without the truncations use no assumption. | Truncation; `LEM` only in the final corollary |
| [`contractible_maps`](contractible_maps.cubist) | Equivalences as contractible maps, the form the kernel checks a Glue type's equivalences in: the fiber of a function, a function whose fibers are contractible (`IsContrMap`), the type of such equivalences (`ContrEquiv`), the identity, and the equality of two equivalences with one forward map, since being contractible is a proposition. An equivalence has an inverse with both inverse laws (`equiv_inverse`), and every function with an inverse and both inverse laws is one (`inverse_equiv`, after Cubical Agda's `isoToIsEquiv`). | None |
| [`univalence`](univalence.cubist) | Univalence by Glue, for the equivalences of [`contractible_maps`](contractible_maps.cubist). An equivalence glues a path of types (`glue_path`), and a path of types transports the identity to an equivalence (`idtoequiv`). The two are inverse (`glue_path_idtoequiv`, `idtoequiv_glue_path`), so `idtoequiv` is an equivalence (`univalence`). Along every line of Glue types, unglue is an equivalence (`glue_line_equiv`), and the type of types equivalent to a type is contractible (`equivalent_types_contractible`). The `ua` builtin takes the `Equiv` of `import paths;` instead. | None |
| [`lists`](lists.cubist) | Lists of elements of a type in any universe below `UU0`, with their length and concatenation (`append`), whose universe and element type are implicit parameters, read off the lists: `nil` is a unit on both sides, concatenation is associative, and the length of a concatenation is the sum of the lengths. | None |
| [`quotients`](quotients.cubist) | Set quotients as a declared type: the quotient of a type by a relation, with a class for each element and a path between related classes. It is a set; it has induction into families of sets; and a map into a set that respects the relation descends to it, uniquely. No representative is chosen. Effectiveness, that related elements are exactly those with equal classes, is still to come. | None |
