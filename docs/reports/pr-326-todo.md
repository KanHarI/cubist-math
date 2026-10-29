# PR #326: EVAL7 part one follow-up

Found while building the library's binary divisibility, primes and Euclid.
Each was worked around in the library. All are outside EVAL7's scope and left
unfixed here; the first overlaps #325's [TODO](pr-325-todo.md).

- [x] **Unrefined hypotheses in a definition-level match.** A match fails with
  E606 when a dependent hypothesis is used only in a later clause, e.g.
  `absurd(h)` after clauses that return `tt`. It checks if an earlier clause
  uses the hypothesis, or if the hypothesis is curried into the result type.
  Three-scrutinee matches with dependent hypotheses fail the same way.
- [x] **Passing such a hypothesis to a helper.** `f(p, below)` fails, while
  eta-expanding `below`, or currying it, checks.
  - **Both fixed by #330** (option B, decided on 2026-10-28): a `match`
    expression takes each hypothesis about its variable at each constructor,
    as the statement does; `cubist-tests/match_hypotheses.cubist` holds both
    cases. An `induction` expression keeps its rule.
- [ ] **The runtime cannot run NUM1's strong recursion.** It contains
  compositions, so every library Euclid value form falls back to the kernel's
  queries after about 65K runtime steps (see
  [binary-euclid](binary-euclid.md)). This is a runtime-roadmap item, not a
  library defect.
- [ ] **Depth.** `euclid(7)` and `euclid(8)` stop at the kernel's depth guard
  (K344). A bare NUM1 strong recursion that only steps to the predecessor
  stops at the same depths, so the limit belongs to NUM1's recursion or the
  evaluator, not to the search.
