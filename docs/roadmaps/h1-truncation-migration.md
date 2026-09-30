# H1 truncation migration evidence

Status: experimental implementation and review draft, 2026-09-30. The
[ledger](h1-truncation-ledger.json) pins 17 checked public changes against
`cc6b50f`. Its acceptance permits the listed changes; it does not certify
that the old and new proofs are identical or that all 47 declarations of
specification section 8.4 have been rebuilt.

`library/h1_truncation.cubist` admits the universe-preserving proposition
truncation and proves its proposition evidence, mapping and elimination
into an independent finite universe. Its definitions are computable and
have no logical assumptions. The legacy archive stays isolated and unchanged.

| Acceptance case | Checked implementation | Dependencies |
| --- | --- | --- |
| G2 | `small_mere_eliminate`, from a small truncation directly into a proposition in U1 | H1; no assumption |
| G4 | Exact old/new public-type hashes and renderings, hypotheses, assumption lists and H1 markers; the same change unlisted, or a changed pin, fails | Both versions must first check |
| G5 | Rebuilt `EventualClose` truncates its small witness at U0; `CauchySame` remains a relation into U0 | H1; neither predicate has assumptions |
| G6 | `resize_prop` decides a proposition using LEM at U1, returning Unit or Void with proposition evidence and maps both ways | LEM only; set evidence for `StrictlyAbove` is rejected |
| G7 | Rebuilt `no_maximal_strict_successor` uses double-negation elimination at U1 on its large truncated conclusion | LEM retained; the four legacy truncation dependencies removed |

The rebuilt Cauchy module has 16 declarations: five verify as identical and
eleven have exact ledger changes. Its representative-selection wrappers
still call the archived predicate quotient and retain its legacy truncation
dependencies. Those wrappers are recorded explicitly; this slice rebuilds
the small equivalence relation and its laws, not the quotient foundation.

The Zorn comparison selects `no_maximal_strict_successor` only. It does not
claim to rebuild `zorn_chain_complete`, the tower or all of the other remedy
groups. `tower_induction_large` and `tower_relative_induction` are explicitly
deferred to H2, and group 5 is refused by the implemented ledger validator.

## Classical signatures

`LEM(Trunc, U, ...)` and `Choice(Trunc, U, ...)` explicitly restate the two
assumptions over the admitted proposition truncation. The former must have
one erased universe parameter, one carrier parameter, an `A -> Trunc(A)`
point and the generated proposition squash. An arbitrary proposition former
is refused. They report LEM and Choice separately from H1 and retain their
non-computing status. The old `LEM(U, ...)` and `Choice(U, ...)` keep their
archived signatures and can coexist in the same session.

`h1_classical.cubist` proves generic double-negation elimination, decidability
of propositions and proposition resizing. Resizing takes explicit
`IsProp(U1, P)` evidence; it cannot extract or resize a witness type merely
from its being a set. For propositions, maps in both directions give an
equivalence because both composites are identified with identities by their
proposition evidence.

## Reproduce the scoped comparisons

All four commands enable H1 explicitly. Each accepted change is checked
against the ledger; removing `--ledger` rejects it. A selected declaration
scope is printed in the report and does not imply whole-module migration.

```sh
node tools/verify-proof-migration.mjs --base cc6b50f --experimental h1 --no-dependents --edited-root library --ledger docs/roadmaps/h1-truncation-ledger.json cauchy_quotient
node tools/verify-proof-migration.mjs --base cc6b50f --experimental h1 --no-dependents --edited-file docs/examples/h1/migrations/field_logic.cubist --declarations small_mere_eliminate --ledger docs/roadmaps/h1-truncation-ledger.json field_logic
node tools/verify-proof-migration.mjs --base cc6b50f --experimental h1 --no-dependents --edited-file library/h1_zorn_step.cubist --declarations no_maximal_strict_successor --ledger docs/roadmaps/h1-truncation-ledger.json zorn_chain_complete
node tools/verify-proof-migration.mjs --base cc6b50f --experimental h1 --no-dependents --edited-file library/h1_classical.cubist --declarations ExcludedMiddle,AxiomOfChoice,excluded_middle_assumed,axiom_of_choice_assumed --ledger docs/roadmaps/h1-truncation-ledger.json classical_axioms
```

`tests/truncation-migration.test.mjs` checks G2 and G5–G7, the ledger file,
coexistence with the legacy signatures and rejection of a false truncation
former, and the CLI's pinned baseline for a module stored in `library/`.
Compared modules require a baseline at the requested Git revision in
`library/` or `archive/first-library/`; an untracked new module cannot supply
its own baseline. `tests/proof-migration.test.mjs` checks listed/unlisted G4 changes,
changed pins, forbidden removals, duplicate entries, failed declarations,
and refusal to use a ledger to bypass proof-identity checking.
