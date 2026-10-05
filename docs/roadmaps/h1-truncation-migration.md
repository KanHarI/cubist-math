# H1 truncation migration evidence

Status: experimental implementation and review draft, 2026-09-30. The
[ledger](h1-truncation-ledger.json) pins 17 checked public changes against
`f4d1961`, rebased from `cc6b50f` on 2026-10-05. Its acceptance permits the listed changes; it does not certify
that the old and new proofs are identical or that all 47 declarations of
specification section 8.4 have been rebuilt.

`library/h1_truncation.cubist` admits the universe-preserving proposition
truncation and proves its proposition evidence, mapping and elimination
into an independent finite universe. Its definitions are computable and
have no logical assumptions. The legacy archive stays isolated and unchanged.

| Acceptance case | Checked implementation | Dependencies |
| --- | --- | --- |
| G2 | `small_mere_eliminate`, from a small truncation directly into a proposition in U1 | H1; no assumption |
| G4 | Version 2: exact old/new public-type and value hashes and renderings, hypotheses, assumption lists, explicit LEM/Choice replacements and H1 markers; the same change unlisted, or a changed pin, fails | Both versions must first check; local public/value dependencies must be identical or ledgered within the comparison scope |
| G5 | Rebuilt `EventualClose` truncates its small witness at U0; `CauchySame` remains a relation into U0 | H1; neither predicate has assumptions |
| G6 | `resize_prop` decides a proposition using rebuilt LEM at U1, returning Unit or Void with proposition evidence and maps both ways | `LEM[h1_truncation.Trunc]` only; set evidence for `StrictlyAbove` is rejected |
| G7 | Rebuilt `no_maximal_strict_successor` uses double-negation elimination at U1 on its large truncated conclusion | Legacy LEM explicitly replaced by `LEM[h1_truncation.Trunc]`; the four legacy truncation dependencies removed |

`cubist-tests/h1_cauchy_quotient.cubist` has 16 declarations: five verify as identical and
eleven have exact ledger changes. Its representative-selection wrappers
still call the archived predicate quotient and retain its legacy truncation
dependencies. Those wrappers are recorded explicitly; this slice rebuilds
the small equivalence relation and its laws, not the quotient foundation.

The Zorn comparison selects `no_maximal_strict_successor` and its five
unchanged local dependencies. The field-logic comparison includes the
unchanged `FieldProp` predicate alongside `small_mere_eliminate`. Neither
claims to rebuild `zorn_chain_complete`, the tower or all of the other remedy
groups. `tower_induction_large` and `tower_relative_induction` are explicitly
deferred to H2, and group 5 is refused by the implemented ledger validator.

The two slices that build on archive developments, `h1_cauchy_quotient` and
`h1_zorn_step`, live in `cubist-tests/`, since a library module imports only
library modules. The prelude `nat` has since moved from the archive into the
library; the verifier reads its baseline from the old path and places it in
the library, as today's checks do.

## Classical signatures

`LEM(Trunc, U, ...)` and `Choice(Trunc, U, ...)` explicitly restate the two
assumptions over the admitted proposition truncation. The former must have
one erased universe parameter, one carrier parameter, an `A -> Trunc(A)`
point and the generated proposition squash. An arbitrary proposition former
is refused. They report `LEM[h1_truncation.Trunc]` and
`Choice[h1_truncation.Trunc]` separately from H1 and retain their
non-computing status. The old `LEM(U, ...)` and `Choice(U, ...)` keep their
archived signatures and can coexist in the same session.
Aliases of one checked truncation share an assumption; different admitted
truncations have different labels. The ledger records a replacement explicitly
and does not describe these new signatures as retained legacy assumptions.

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
All ledger entries for a compared module must be inside that run's scope.
`hypothesesAdded` lists newly spelled parameter names for review; the pinned
public type, rather than that informational list, records their actual types.
The CLI defaults to the ledger's pinned baseline and rejects an explicit
`--base` that names a different revision. Archive imports resolve only within
the archive; a compared root prefers its archived predecessor, then library.
Each type and value pin also hashes the checked meanings of referenced
definitions and admitted signatures, so a folded name cannot hide a changed
dependency even when its public type stays the same.

```sh
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file cubist-tests/h1_cauchy_quotient.cubist --ledger docs/roadmaps/h1-truncation-ledger.json cauchy_quotient
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file docs/examples/h1/migrations/field_logic.cubist --declarations FieldProp,small_mere_eliminate --ledger docs/roadmaps/h1-truncation-ledger.json field_logic
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file cubist-tests/h1_zorn_step.cubist --declarations OrderMaximal,StrictlyAbove,strict_above_point,strict_above_laws,strict_above_is_set,no_maximal_strict_successor --ledger docs/roadmaps/h1-truncation-ledger.json zorn_chain_complete
node tools/verify-proof-migration.mjs --base f4d1961 --no-dependents --edited-file library/h1_classical.cubist --declarations ExcludedMiddle,AxiomOfChoice,excluded_middle_assumed,axiom_of_choice_assumed --ledger docs/roadmaps/h1-truncation-ledger.json classical_axioms
```

The pins were refreshed at H1's release on 2026-10-02. Results no longer
carry the `kernel extension: H1` marker, so every change's
`extensionsAdded` and `extensionsRetained` are empty. The signature
fingerprint no longer includes the retired `experimental` flag, so 52 type
and value hashes changed. Every assumption list, type text and value text
is unchanged, which the refresh checked before writing the new hashes.

The pins were refreshed again on 2026-10-05, with the base moved to
`f4d1961`, where `nat` and `naturals` became one module and the archive's
`primes` gave up its copies of their arithmetic. Against `cc6b50f`, whose
`primes` still had its own `add` and order, `cauchy_quotient`'s
declarations that use them differed by which definitions they named,
though no source changed. At the new base both versions use `nat`'s:
`close_tails_compose` is identical again, and four value hashes changed,
the old and new values of `sequence_same_transitive` and
`cauchy_same_equivalence`. Every assumption list, type text and value text
is unchanged, which the refresh checked before writing them.

`tests/truncation-migration.test.mjs` checks G2 and G5–G7, the ledger file,
coexistence with the legacy signatures and rejection of a false truncation
former, and the CLI's pinned baseline for a module stored in `library/`.
Compared modules require a baseline at the requested Git revision in
`library/` or `archive/first-library/`; an untracked new module cannot supply
its own baseline. `tests/proof-migration.test.mjs` checks listed/unlisted G4 changes,
changed pins, forbidden removals, duplicate entries, failed declarations,
scope escapes, body substitution, explicit assumption replacements,
archive/library collisions and refusal to bypass proof-identity checking.
The rebuilt module's `h1_` prefix preserves the legacy `cauchy_quotient` CLI,
REPL and page lookup when H1 is disabled.
