# The rebuilt library

This is the root of the rebuilt proof library (work-plan item I0.3). The
first library is kept, unchanged, in [`archive/first-library/`](../archive/first-library/).
Its results are catalogued in English in
[`docs/library-results.md`](../docs/library-results.md), which is what the
rebuild follows.

- Modules here take precedence over archive modules of the same name, in the
  command-line checker, the proof workspace and the language reference.
- Each module has one theme, and no helper is duplicated across modules.
- Every module is listed in `libraryModules` in
  [`web/cubist/modules.mjs`](../web/cubist/modules.mjs), and
  `tests/library.test.mjs` checks that each checks completely and uses exactly
  the assumptions listed for it there.
- Until the foundations are rebuilt, a module may import archive modules, such
  as `paths` for `Equiv` and `ua`.

| Module | Contents | Assumptions |
| --- | --- | --- |
| [`naturals`](naturals.cubist) | Addition, multiplication and order on `Nat`, with the basic laws of addition. `+`, `*`, `<` and `<=` need it. | None |
| [`classical_axioms`](classical_axioms.cubist) | The statements of the classical assumptions as types, `ExcludedMiddle(U)` and `AxiomOfChoice(U)`, with checks that `LEM(U)` and `Choice(U)` have them. | `LEM`, `Choice`, `Truncate` |
| [`hlevels`](hlevels.cubist) | Contractible types, propositions and sets in every universe below `UU0`, with `HasLevel(U, n, A)` defined by recursion on `n`, so that `IsSet` is level 1 by conversion. Propositions are sets, levels are cumulative, having a level is a proposition, and a retract, such as a type equivalent to another by an inverse, a function type, a type of pairs, a product or a subtype keeps the level of the types it is made from. Contractible types are closed under the same constructions except subtypes, since a subtype can be empty, and being contractible is a proposition. A type with decidable equality, such as `Nat`, is a set (Hedberg). | None |
| [`universe_automorphisms`](universe_automorphisms.cubist) | Excluded middle for `U0` holds exactly when there merely is an automorphism of `U0` sending `Unit` to `Void`. Both directions without the truncations use no assumption. | Truncation; `LEM` only in the final corollary |
| [`contractible_maps`](contractible_maps.cubist) | Equivalences as contractible maps, the form the kernel checks a Glue type's equivalences in: the fiber of a function, a function whose fibers are contractible (`IsContrMap`), the type of such equivalences (`ContrEquiv`), the identity, and the equality of two equivalences with one forward map, since being contractible is a proposition. | None |
| [`univalence`](univalence.cubist) | Univalence by Glue, for the equivalences of [`contractible_maps`](contractible_maps.cubist): an equivalence glues a path of types (`glue_path`), a path of types transports the identity to an equivalence (`idtoequiv`), and gluing along `idtoequiv(p)` gives back `p`. The `ua` builtin takes the `Equiv` of `import paths;` instead. | None |
