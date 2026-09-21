# Cumulative result types

The native and reference checkers distinguish definitional equality from directed
cumulative typing. `U0` and `U1` are different terms. Nevertheless a term of type
`U0` may be checked at `U1`, and the same lifting is available in the result of a
function or dependent pair over a definitionally equal domain:

```text
Γ, x : A ⊢ B ≤ C
─────────────────────────────────
Γ ⊢ (Π x : A. B) ≤ (Π x : A. C)

Γ, x : A ⊢ B ≤ C
─────────────────────────────────
Γ ⊢ (Σ x : A. B) ≤ (Σ x : A. C)
```

Here `≤` includes definitional equality and `Ui ≤ Uj` when `i ≤ j`. Both compared
types are already checked. Their bound variables are renamed to one common fresh
variable before comparing the codomains. Domains must remain definitionally
equal: this implementation does not add function-domain variance, universe
resizing, or an equality between universes.

This closure is necessary for substitution. A generic definition can check a
family `fun x : A => B` at `A -> U1` while `B : U1`. After instantiating `B` with
`Nat`, the family's most precise inferred type becomes `A -> U0`; its checked
uses at `A -> U1` must remain valid. Only allowing cumulativity when both whole
types are universes caused inferred types to fail their own subsequent checks.

The concrete reported failure was `interval_midpoint_right_order`, a second
projection of `interval_midpoint_within`. Its value inferred successfully, but
its exported type contained a lower-universe constant family passed to
`field_first`, which expects a family into `U1`. Rechecking the exported type,
including after closing the truncation parameter, failed. The complete reported
fixture now checks: 536,770 arena nodes, 972 checking steps, and 30,016 reduction
steps, with the existing operation budget.

`lib/cubical/tests/cumulativity.test.mjs` tests substitution followed by
rechecking the inferred type, nested result lifting, dependent pairs, and
rejection of downward lifting, changed domains, and equality between universes.
The same cases are checked by the independent JS and C implementations. This
change adds no axiom, and does not change the conversion relation or evaluator.
