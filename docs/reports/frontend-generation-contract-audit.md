# FG0 contract audit

Scope: the executable cases from PR #205, restored in PR #217, including the
diagnostic acceptance review of `89c97e99`.
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
The different-cause loop checks historical debt recognition. Separate controls
start from accepted results and change only diagnostic meaning; they require
rejection with `knownDefect` removed and in strict mode. These controls establish
the acceptance boundary that remains after activation.

## Requirements and controls

“Source” below means real independently checked clients on a supported variant.
“Observer” means an explicitly injected diagnostic/publication result layered
over real checked outputs. Observer controls exercise the predicate's boundary;
they do not establish a compiler fix. Supported variants avoid the original bug
and likewise do not establish that its original source is fixed.

| Cases | Authority | Acceptance control and allowed variation | Distinguishing failure |
| --- | --- | --- | --- |
| G1, G1-initial, G1-reverse, G1-same-kind | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: independently check the original declaration and clients without the duplicate, then inject its refusal. Both declaration orders and the original constructor are covered. Duplicate wording/code may vary within the documented refusal contract. | Lost original client; a real constructor client becomes accepted, or a real model/fold output leaks alongside the preserved original binding. |
| G2 | [FG3](../roadmaps/frontend-generation.md#fg3-infer-universes-from-the-generated-telescope) | Source: supported `op(x : M) : M`, retaining all Hom/Iso/computation clients at U0/U1. | Different found/expected types with E606 and the same cascade. |
| G3 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Observer: retain checked base clients, withhold Hom/Iso, and supply an E817 identifying op, p and l. Two focused refusal wordings are accepted. | A leaked family, or a different underlying Hom mismatch with E606. |
| G4, G4-flat | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: supported Nat motives, with distinct branch results and independently stated accepted/refused equations. | Constant match result; wrong clause result; same E546 with a different primary cause. |
| G5, G5-single | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Real original clients plus injected suppression of unsafe advice; existing controls preserve ordinary safe W705/W706. Only identified advice at the source target authorizes the associated rewrite. | Same-code changed advice, declaration or location; partial grouped advice; changed refusal cause after the original rewrite. |
| G6 | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: child E340 has dependency target P, with or without an attached root cause. Parent E343 has untranslated subject Undefined and independent clients check. | Dependency Q even when its attached cause mentions P; an untranslated-name message masquerading as a dependency; a different parent cause. |
| G8 | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Observer: E606 with the specified found/expected endpoints; token or wider body span accepted. | Swapped endpoints, empty/off-token/out-of-body spans, or a different generation cause. |
| G9 | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Source: rename the colliding law binder, preserving independently stated meaning and all navigation sites. Identical repeated links are equivalent. | A different definition target; existing harness checks missing sites. |
| G10 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: E871 identifies helper k and captured field c; the binder, helper call, or enclosing conflicting clause supplies a nonempty origin. | Unrelated origin; a different helper, field or unrecognized cause with an otherwise valid range, including after activation. |
| G11, G11-grouped-dependent, G11-inherited, G11-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename the derived parameter through its telescope/body, preserving all independent intended/captured equations in each context. | Different same-code mismatch; intended and captured equations must retain opposite verdicts. |
| G12, G12-inherited, G12-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: two-step nonrecursive unrolling, retaining zero/one/two-step and wrong-result clients in all three contexts. This establishes the finite witnesses only. | Constant iter makes the wrong equation check; ignoring the recursive result preserves the first step but fails the second with E606. Unrelated same-code failures remain rejected. |
| G12-shadowed | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename only the local iter parameter; intended/local and captured/field equations retain opposite verdicts. A separate field-type control checks today. | Replacing the local call by the earlier field result makes the captured equation check. |
| G12-range | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: E845 identifies recursive iter in a field type; range over iter, iter(n), or a wider span within the written law. | Empty/off-reference/out-of-law span; a different operation, context or unrecognized cause with an otherwise valid range, including after activation. |

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
  attached cause wording is not a cause fingerprint. Location and navigation
  requirements keep their own source checks rather than depending on diagnostic
  formatting.
- The range audit found G8 could accept reversed found/expected endpoints because
  it searched for both strings anywhere. It now compares their respective roles.
- The coverage check compared IDs alone. It now also verifies finding ownership;
  a G12-range row incorrectly assigned to G11 fails. The fixture comment now
  correctly describes downstream provenance/browser consumers.
- The constructor audit used an impossible output shape. Output absence is now
  named explicitly (`absentOutputs`/`absentOutputFamilies`); constructor availability
  is observed through real clients that must receive E343. Positive programs prove
  each constructor is usable while absent from outputs. Observer leak controls
  replay those real client verdicts and actual model/fold outputs alongside a
  synthetic duplicate refusal. They establish predicate sensitivity, not a
  compiler-generated partial-publication bug. Downstream original cases establish
  the actual refusal and preservation behavior.
- Collision diagnostics previously allowed exactly one gap. Refused clients now
  carry individual codes, and their expected diagnostics compose with the
  declaration refusal. A control combines E343 and E606 clients with the duplicate
  diagnostic, and rejects swapped codes, missing clients and extra diagnostics.
- G12's first successor could not distinguish using the recursive result from
  substituting `c`. Every context now requires `computation2`. Executable constant
  and step-ignoring counterexamples independently specify the client verdicts and
  E606 failures that must reject them. Removing a second-step witness fails the
  minimum-obligation check.
- Historical cause matching was stronger than active acceptance. A shared
  diagnostic decoder now serves both historical observations and desired
  expectations, with independently stated expected causes. Declaration and
  refused-client diagnostics compose through the same complete-multiset matcher.
  G1/G1-initial pin each missing constructor name; G6 pins the dependency target;
  G10 and G12-range pin causes alongside ranges; G8 uses the same matcher for its
  ordered endpoints. Removing mandatory cause metadata fails before checking.
- Acceptance controls now change causes in otherwise valid observations, keeping
  every other requirement satisfied. They reject the reported same-code probes
  after activation, as well as changed helper/field/recursive subjects, malformed
  dependency messages, and wrong missing constructor names. Attached dependency
  causes and permitted source spans remain accepted.
- Removed the harness's duplicate G12 nonrecursive controls. The audit retains
  all three supported contexts and their constant/ignored-recursion mutants.

## Validation and lifecycle

Run the contracts, harness and audit together:

```sh
npm test -- tests/frontend-generation.test.mjs tests/frontend-generation-harness.test.mjs tests/frontend-generation-audit.test.mjs
```

The audit's case-list check requires an acceptance control for every executable
case, and its different-cause loop runs every case. These checks establish
coverage of the stated controls; the contents still require semantic review.
Use the contributor checklist on new cases and audit siblings after findings.

Controlled reversions cover cause retention, reference width, endpoint roles,
advice observation, primary causes, dependency targets and coverage ownership.
The reference-span control states `iter` independently of fixture metadata.
The follow-up adds constructor-availability, output-absence, source-anchor
ambiguity and missing-obligation controls, plus semantic mutants for constant
computations, ignored recursive results and capture of a shadowing parameter.
An incorrect implementation that still checks clients is a separate audit
boundary from an unrelated diagnostic.

The [independent requirement map](../../tests/fixtures/frontend-generation-requirements.mjs)
records obligations and their witnesses. Removing both a fixture and its
manifest row cannot erase an obligation. This check establishes mapping
completeness; semantic sensitivity comes from the real equation pairs and
explicit counterexamples, not from metadata agreement.

Keep the roadmap as the behavioral authority when integrating downstream fixes.
Activate each fixed original case and preserve downstream search-eligibility,
explicit-path, provenance, named-constructor and recursive-predecessor controls.
Once all original cases pass, retire known-defect records and tests specific to
that lifecycle. Retain the acceptance boundaries and distinguishing controls
that still protect active behavior. Integration and full-suite results belong
in the PR's validation record at the tested revision.
