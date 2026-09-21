# Native source edition of path actions

`web/proofs/cubical/path_actions.proof` keeps the public helper names and types
from `web/proofs/path_actions.proof`. The legacy source remains unchanged.
The native edition uses explicit checked cubical operations rather than strict
identity-eliminator computation.

- `append_path` is canonical `trans`; its agreement with `concatenate` is
  reflexivity.
- Appending a path and its reverse uses the proved cancellation laws.
- The original right-inverse proof is retained as
  `append_path_right_inverse_raw`. The public right inverse uses the existing
  adjointification counit, and `append_path_triangle` uses the corresponding
  adjointification triangle. Their public types are unchanged and agree with
  the tuple assembled by `append_path_equivalence`.
- `map_concat` contains the explicit image-of-filling comparison cube.
  Application preserves reversal, and double reversal computes, so those two
  helpers use reflexivity.
- `transport_predicate` uses Pi composition and then the explicit
  constant-transport path in U0. It does not assume universe transport is
  judgmentally trivial.
- `reopen_closed_path` cancels the right connector and then the left connector
  using existing path-algebra proofs.

Validation used the current native WASM `CubicalProgram` on main, with an
absolute temporary loader overriding only `path_actions` to this worktree's
native edition. Its import graph checked 74 declarations with zero failures
and zero gaps. The eight explicit public-contract proofs in
`experiments/cubical/fixtures/path-actions-contracts.proof` then checked too:
82 declarations, zero failures, zero gaps. No legacy checker was used.

A broader caller check (circle_degree, puncture_graph, loop_words, and
bouquet_generation) checked 332 declarations and identified 39 failures in
still-unmigrated circle/bouquet proofs and their dependents. No failure was in
path_actions. Those remaining source migrations are not claimed complete by
this checkpoint.

The root agent owns the source registry. Integration requires mapping
`path_actions` to `cubical/path_actions.proof` in `web/cubical-sources.mjs`.
This worktree does not change that registry or the frontend translator.
