# PR #325: NT1 follow-up

Found while moving the unary order lemmas into `unat`. Outside NT1's scope
and left unfixed here.

- [x] An expression `match` does not always narrow a hypothesis parameter's
  type in its clauses, while a proof-block `match` does. Over
  `import unat; use unat;`:

  ```
  // E606: found n <= 0, expected Void
  computable def le_zero_absurd(n : UNat, h : n <= 0) : n = 0 := match n {
      zero => refl(0);
      succ(k) => absurd(h);
    };
  // Checks: the same clause with typed(Void, h)
  computable def le_zero_typed(n : UNat, h : n <= 0) : n = 0 := match n {
      zero => refl(0);
      succ(k) => absurd(typed(Void, h));
    };
  ```

  - **Three columns, recursive:** `match a, b, c` for transitivity fails the
    same way on `ab`.
  - **Two columns:** `unat_le_step`'s `match a, b` is narrowed.
  - **Consequence:** `unat_le_zero` and `unat_le_trans` are written as proof
    blocks for this reason.
  - **Next step:** find where the expression form computes its clause
    contexts, and why `typed(Void, h)` succeeds where `h` alone does not.
  - **Fixed by #330** (option B, decided on 2026-10-28): a `match`
    expression takes each hypothesis about its variable at each constructor,
    as the statement does. `le_zero_absurd` and the three-column
    transitivity are in `cubist-tests/match_hypotheses.cubist`. An
    `induction` expression keeps its rule.
