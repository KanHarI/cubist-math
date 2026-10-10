# Frontend generation contract acceptance audit

The contracts from [#205](https://github.com/KanHarI/cubist-math/pull/205)
are integrated and active on this branch. The
[roadmap](../roadmaps/frontend-generation.md) defines desired behavior; the
[independent requirement map](../../tests/fixtures/frontend-generation-requirements.mjs)
assigns executable witnesses. The [manifest](../../tests/fixtures/frontend-generation.md)
records each case and the surviving downstream controls.

The old compiler's defect records and classification-only tests have been
retired. The following acceptance boundaries remain in
[frontend-generation-audit.test.mjs](../../tests/frontend-generation-audit.test.mjs).
Real original cases run separately against the fixed compiler. Source controls
and injected observations exercise the predicates without substituting for
those integration checks. See the [contributor checklist](../guides/regression-contracts.md).

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
| G6 | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: child E340 names P, with or without an attached root cause. Parent E343 still reports Undefined and independent clients check. | A different parent or primary cause; re-expansion still has the wrong child code. |
| G8 | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Observer: E606 with the specified found/expected endpoints; token or wider body span accepted. | Swapped endpoints, empty/off-token/out-of-body spans, or a different generation cause. |
| G9 | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Source: rename the colliding law binder, preserving independently stated meaning and all navigation sites. Identical repeated links are equivalent. | A different definition target; existing harness checks missing sites. |
| G10 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: the binder, helper call, or enclosing conflicting clause supplies a nonempty origin. | Unrelated origin, or a different E871 cause. |
| G11, G11-grouped-dependent, G11-inherited, G11-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename the derived parameter through its telescope/body, preserving all independent intended/captured equations in each context. | Different same-code mismatch; intended and captured equations must retain opposite verdicts. |
| G12, G12-inherited, G12-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: two-step nonrecursive unrolling, retaining zero/one/two-step and wrong-result clients in all three contexts. This establishes the finite witnesses only. | Constant iter makes the wrong equation check; ignoring the recursive result preserves the first step but fails the second with E606. Unrelated same-code failures remain rejected. |
| G12-shadowed | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename only the local iter parameter; intended/local and captured/field equations retain opposite verdicts. A separate field-type control checks today. | Replacing the local call by the earlier field result makes the captured equation check. |
| G12-range | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: range over iter, iter(n), or a wider span within the written law. | Empty/off-reference/out-of-law span, or a different E845 cause. |

## Distinguishing controls

- Output-absence checks (`absentOutputs`/`absentOutputFamilies`) describe reported
  declarations. Real positive programs prove constructors can be usable without
  appearing in that list. Constructor leaks are observed through E343 clients;
  observer controls replay real client verdicts and actual model/fold outputs
  alongside a synthetic duplicate refusal, preserving the original binding.
- Refused clients carry individual codes, composed with declaration diagnostics
  into one complete set. A control combines E343 and E606 clients with the
  duplicate refusal and rejects swapped codes, extra gaps and missing clients.
- Semantic controls use distinct branches, zero/one/two recursive steps, and
  independent intended/incorrect equations. Executable constant and step-ignoring
  sources state their separating client verdicts and E606 failures. The supported
  two-step unrolling establishes those finite witnesses, not general recursion.
  Capturing a local recursive parameter makes the incorrect equation check.
- Source scopes, conflicts and rewrites resolve before checking; duplicate
  anchors fail without invoking the compiler. Inner-token occurrences are
  explicit, including the conflicting binder rather than a letter in `succ`.
- Removing both a case and its manifest row still fails the independent
  requirement map. Removing constructor, output, wrong-equation or second-step
  expectations also fails. Metadata coverage does not itself prove semantic sensitivity.
- Diagnostic controls retain permitted alternatives: attached parent causes,
  narrow or wider valid spans, and correctly ordered found/expected endpoints.
- Lint observer controls inject a proposed unsafe edit because the fixed linter
  now suppresses it. Changed/partial advice cannot silently authorize the edit;
  real safe W705/W706 controls and downstream generated clients remain active.

Run the commands in the manifest and the normal full suite. Preserve all
required compiler mutation checks, including recursive lexical shadowing.
The preexisting reservation/failed-publication mutations complement the
observer leak controls; neither replaces the other. Keep commit-specific
suite and integration results on the PR, alongside the exact tested revision.
