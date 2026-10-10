# FG0 contract audit

Scope: all 22 executable cases in PR #205, following review of `1c079714`.
The [frontend generation roadmap](../roadmaps/frontend-generation.md) supplies
the behavioral requirements. The [inventory](frontend-generation-gaps.md)
describes defects; the [manifest](../../tests/fixtures/frontend-generation.md)
maps cases to evidence. This audit checks those mappings and acceptance
boundaries without declaring the compiler defects fixed.

The procedure is the [regression contract checklist](../guides/regression-contracts.md).
Each case now has a known-defect control, a different-cause control with unchanged
diagnostic codes (changed navigation for G9), and an acceptance control in
[frontend-generation-audit.test.mjs](../../tests/frontend-generation-audit.test.mjs).
Existing harness regressions retain prerequisite, fixture, strict-mode and
independent-activation checks. W705 and W706 safe-advice controls remain active.

## Requirements and controls

“Source” below means real independently checked clients on a supported variant.
“Observer” means an explicitly injected diagnostic/publication result layered
over real checked outputs. Observer controls exercise the predicate's boundary;
they do not establish a compiler fix. Supported variants avoid the original bug
and likewise do not establish that its original source is fixed.

| Cases | Authority | Acceptance control and allowed variation | Distinguishing failure |
| --- | --- | --- | --- |
| G1, G1-initial, G1-reverse, G1-same-kind | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: independently check the original declaration and clients without the duplicate, then inject its refusal. Both declaration orders and the original constructor are covered. Duplicate wording/code may vary within the documented refusal contract. | Lost original client; changed type mismatch or registration cause with the same code. |
| G2 | [FG3](../roadmaps/frontend-generation.md#fg3-infer-universes-from-the-generated-telescope) | Source: supported `op(x : M) : M`, retaining all Hom/Iso/computation clients at U0/U1. | Different found/expected types with E606 and the same cascade. |
| G3 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Observer: retain checked base clients, withhold Hom/Iso, and supply an E817 identifying op, p and l. Two focused refusal wordings are accepted. | A leaked family, or a different underlying Hom mismatch with E606. |
| G4, G4-flat | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: supported Unit motives, with checked nested/flat projections and computations. | Same E546 with a different primary cause. Evidence records both the generated obligation and its required h-level. |
| G5, G5-single | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Real original clients plus injected suppression of unsafe advice; existing controls preserve ordinary safe W705/W706. Only identified advice at the source target authorizes the associated rewrite. | Same-code changed advice, declaration or location; partial grouped advice; changed refusal cause after the original rewrite. |
| G6 | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: child E340 names P, with or without an attached root cause. Parent E343 still reports Undefined and independent clients check. | A different parent or primary cause; re-expansion still has the wrong child code. |
| G8 | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Observer: E606 with the specified found/expected endpoints; token or wider body span accepted. | Swapped endpoints, empty/off-token/out-of-body spans, or a different generation cause. |
| G9 | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Source: rename the colliding law binder, preserving independently stated meaning and all navigation sites. Identical repeated links are equivalent. | A different definition target; existing harness checks missing sites. |
| G10 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: the binder, helper call, or enclosing conflicting clause supplies a nonempty origin. | Unrelated origin, or a different E871 cause. |
| G11, G11-grouped-dependent, G11-inherited, G11-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename the derived parameter through its telescope/body, preserving all independent intended/captured equations in each context. | Different same-code mismatch; intended and captured equations must retain opposite verdicts. |
| G12, G12-inherited, G12-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: nonrecursive iter, retaining twice and its computation clients in all three contexts. | Different same-code primary refusal; missing/refused clients remain explicit. |
| G12-range | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: range over iter, iter(n), or a wider span within the written law. | Empty/off-reference/out-of-law span, or a different E845 cause. |

## Findings and dispositions

- G6 rejected root-cause retention that FG1 permits. Removed that prohibition;
  retained the parent-cause prerequisite and the child's E340/parent checks.
- G5 inferred an edit from a warning code. Recorded code/declaration/message and
  required matching advice within the edit target before applying the replacement.
  Unknown advice fails for investigation; it is never silently treated as the
  same edit. This mapping can be retired with temporary defect tracking.
- G12-range overconstrained the span to a whole call. The required reference is
  now `iter`; controls accept both narrow and wider valid origins.
- The same-code audit confirmed that G2's previous name/code observation could
  hide an unrelated mismatch. All cases now retain primary cause payloads.
  E340 cascade membership and dependency targets are also checked; repeated
  attached cause wording is not a cause fingerprint. Location and navigation requirements keep
  their own source checks rather than depending on diagnostic formatting.
- The range audit found G8 could accept reversed found/expected endpoints because
  it searched for both strings anywhere. It now compares their respective roles.
- The coverage check compared IDs alone. It now also verifies finding ownership;
  a G12-range row incorrectly assigned to G11 fails. The fixture comment now
  correctly describes downstream provenance/browser consumers.

## Validation and lifecycle

Run the contracts, harness and audit together:

```sh
npm test -- tests/frontend-generation.test.mjs tests/frontend-generation-harness.test.mjs tests/frontend-generation-audit.test.mjs
```

The audit's case-list check requires an acceptance control for every executable
case, and its different-cause loop runs every case. These checks establish
coverage of the stated controls; the contents still require semantic review.
Use the contributor checklist on new cases and audit siblings after findings.

Validation: the full suite has 848 tests (826 pass, 22 documented TODOs, no
failures); the three focused files have 89 (67 pass, 22 TODOs). All 22 expanded
defect records also match the historical compiler at `00d4ecce`. Seven controlled
reversions are rejected: G6 cause retention, G12 reference width, G8 endpoint
roles, G5 advice observation, G2 primary-cause and dependency-target observation,
and coverage ownership. The G12 span control states `iter` independently of
fixture metadata so restoring the erroneous whole-call requirement fails it.

An isolated integration over downstream compiler `f527e81f`, activating every
original case and preserving its extra controls, passes 36 contract/control/
provenance tests and all 13 required compiler mutation checks. This is an
integration overlay, not a claim that the downstream branch contains this update.

Keep the roadmap as the behavioral authority when integrating downstream fixes.
Activate each fixed original case and preserve downstream search-eligibility,
explicit-path, provenance, named-constructor and recursive-predecessor controls.
Once all original cases pass, retire known-defect records and tests specific to
that lifecycle. Retain the acceptance boundaries and distinguishing controls
that still protect active behavior. Integration and full-suite results belong
in the PR's validation record at the tested revision.
