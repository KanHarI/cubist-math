# CB2: retained interfaces in production

Archived on 2026-10-17: this implementation sequence is complete. Continuing
contracts are indexed under [frontend](../frontend/README.md); the
[work plan](../work-plan.md) owns any subsequent work.

Status: complete and merged in #234, followed by the separate CB0–CB2 cleanup
in #235. Reconciled on 2026-10-17 against main `e729c2d5`; CB3–CB7 and
the final cleanup are also merged. Validation below records the CB2 checkpoint.

CB2 resolves complete theory headers, field and helper telescopes, family
domains and inheritance at their ordered source boundary. The default theory
and initial/free-model paths consume those interfaces. Internal references
carry compilation-owned identities through cloning, substitution and artifact
publication; display labels cannot retarget them.

Inheritance shares fields only under the required origin and binding
correspondence, comparing local binders by alpha-equivalence. Helpers retain a
complete checking expression alongside their normalized analysis view. Both
support strategies use exact dependencies and explicit conditional pattern
alternatives; unknown consumed openings and inferred holes remain obligations.
A token introducing a pattern or selection is not itself a dependency.

File selections activate before each source declaration's parameters. Initial
requests resolve the theory head in that enclosing context while their
arguments and generators resolve under the request telescope. Named notation
receipts retain source identities and lazy operand recipes; missing recipe
receivers fail on consumption without becoming destination names. A translator
constructed on an existing checker reuses that compilation's identity registry.

The production regression suite requires the intended results for all capture
witnesses and the bounded preservation configurations, with their independently
written incorrect clients still rejected. It covers imported renaming, earlier
headers versus later helpers, bare recursive references, family helper domains,
diamond sharing and conflicts, initial/free folds, optional publication groups,
source links and diagnostic labels. `retained-production.test.mjs` additionally
checks that ordinary imported interfaces actually carry the identities consumed
by generation. The mutation runner now targets the production identity lowering
and file-activation boundaries as well as reservation and publication rollback.

Validation: `npm test`: 1,193 tests, 1,177 passed, 16 documented later-phase TODOs, zero failures; all 3,857 canonical checks passed. All four production mutation checks were killed. The 207-module corpus is included in the full suite.

## Completed handoffs

- [CB3](capture-bindings-cb3.md) completed deferred scopes and lazy selection
  receivers; its migration refusals are retired.
- [CB4](capture-bindings-cb4.md) removed the Hom/Iso text templates and completed
  generated universe inference using retained artifacts.
- [CB5](capture-bindings-cb5.md) completed lint, binding-faithful generated views
  and contextual diagnostics.
- [CB6](capture-bindings-cb6.md) delivered the arbitrary-context REPL beyond
  CB1's isolated replay pilots.
- [CB7](capture-bindings-cb7.md) retired remaining transitional paths and
  recorded release evidence. #241 removed completed-defect staging.

All eight authorized external CB2 review rounds were used. Later integration
checks are implementation validation, not a ninth external review or a claim of
an externally approved final head. The cross-round design analysis is recorded
in [review obligations](../../reports/capture-bindings-review-roots.md).

The separate CB0–CB2 cleanup merged in #235. It removed superseded producers
and receiver interpreters, mode switches, capture keys, obsolete snapshots,
forwarding APIs and duplicate validation. Historical source rewriting remains
isolated in `legacy-syntax.mjs`; CB3/CB4 completed the remaining handoffs above.
