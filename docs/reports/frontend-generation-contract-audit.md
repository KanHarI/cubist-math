# FG0 contract audit

Scope: the executable cases from PR #205, restored in PR #217, including the
diagnostic acceptance review of `89c97e99` and the requirement review of
`687f554c`. The [frontend generation roadmap](../roadmaps/frontend-generation.md)
supplies the behavioral requirements. The [inventory](frontend-generation-gaps.md)
describes defects; the [manifest](../../tests/fixtures/frontend-generation.md)
maps cases to evidence. This audit checks those mappings and acceptance
boundaries without declaring the compiler defects fixed.

The procedure is the
[regression contract checklist](../guides/regression-contracts.md).
[frontend-generation-audit.test.mjs](../../tests/frontend-generation-audit.test.mjs)
gives every case three controls:

- Debt: the recorded defect is recognized, and changing any one primary cause or
  dependency target (navigation for G9) makes it an unrecognized observation.
- Acceptance: an accepted observation of the case passes in strict mode and is
  an unexpected pass while its defect record remains.
- Counterexamples: every counterexample of every applicable requirement is
  applied to that accepted observation. Each must violate its requirement and
  be refused with `knownDefect` removed and in strict mode.

Requirements and their counterexamples are defined together in
[frontend-generation-contracts.mjs](../../tests/frontend-generation-contracts.mjs),
so the third control covers each case without per-case audit code and remains
after activation. A requirement without a counterexample fails the audit, and
the [requirement map](../../tests/fixtures/frontend-generation-requirements.mjs)
names the requirements each witness must keep. Harness regressions retain
prerequisite, fixture, strict-mode and independent-activation checks. W705 and
W706 safe-advice controls remain active.

## Requirements and controls

“Source” below means real independently checked clients on a supported variant.
“Observer” means an explicitly injected diagnostic/publication result layered
over real checked outputs. Observer controls exercise the predicate's boundary;
they do not establish a compiler fix. Supported variants avoid the original bug
and likewise do not establish that its original source is fixed. Every row also
rejects refused, missing or assumption-dependent clients, accepted refusals, and
missing, duplicated, recoded or unrelated diagnostics.

| Cases | Authority | Accepted observation and allowed variation | Counterexamples that must be refused |
| --- | --- | --- | --- |
| G1, G1-initial, G1-reverse, G1-same-kind | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: check the original declaration and clients without the duplicate, then inject its refusal. Duplicate wording/code may vary within the documented refusal contract. | Another type for the original binding; a duplicate accepted or refused for another reason; a real constructor client that checks or names another missing name; a real model/fold output. |
| G2 | [FG3](../roadmaps/frontend-generation.md#fg3-infer-universes-from-the-generated-telescope) | Source: the domain moves into the model's universe (`op(A : U, x : A)`). Hom/Iso, computation, `map_op` preservation and level clients check at U0/U1; that variant's U1 level pin is U2. Stating a U0 model's Hom in U0 is refused with `found U1, expected U0`. | A missing preservation field or level client; an accepted lowering or one with other endpoints; a different same-code Hom mismatch. |
| G3 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Observer: retain checked base clients, withhold Hom/Iso, and supply the fixing compiler's E817 naming op, p and l. Two other focused wordings are accepted. | A leaked family root or member; a refusal without op, p, l or its dependency, including the real E817 for arrow-typed operations; another code. |
| G4, G4-flat | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: Nat motives, with distinct branch results and independently stated accepted/refused equations. | Constant match result; wrong clause result; same E546 with a different primary cause. |
| G5, G5-single | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Real original clients with unsafe advice suppressed; existing controls preserve ordinary safe W705/W706. Only identified advice at the source target authorizes the associated rewrite. | Advice with another message or declaration, outside its target, empty, partial or extended; a changed refusal cause after the original rewrite. |
| G6 | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: child E340 has dependency target P, with or without an attached root cause. Parent E343 has untranslated subject Undefined and independent clients check. | Another dependency, including Q whose attached cause mentions P; an untranslated-name message with E340; another parent subject. |
| G8 | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Observer: E606 with the specified found/expected endpoints; token or wider body span accepted. | Swapped or changed endpoints; empty, off-token, out-of-body or unlocated spans; a different generation cause. |
| G9 | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Source: rename the colliding law binder, preserving independently stated meaning and all navigation sites. Identical repeated links are equivalent. | At any written site: a freshened label, another or missing definition target, or no link. |
| G10 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: E871 identifies helper k and captured field c; the binder, helper call, or enclosing conflicting clause supplies a nonempty origin. | Empty, unrelated, unlocated or out-of-clause spans; a different helper, field or unrecognized cause. |
| G11, G11-grouped-dependent, G11-inherited, G11-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename the derived parameter through its telescope/body, preserving all independent intended/captured equations in each context. | Different same-code mismatch; intended and captured equations must retain opposite verdicts. |
| G12, G12-inherited, G12-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: two-step nonrecursive unrolling, retaining zero/one/two-step and wrong-result clients in all three contexts. This establishes the finite witnesses only. | Constant iter makes the wrong equation check; ignoring the recursive result preserves the first step but fails the second with E606. |
| G12-shadowed | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename only the local iter parameter; intended/local and captured/field equations retain opposite verdicts. A separate field-type control checks today. | Replacing the local call by the earlier field result makes the captured equation check. |
| G12-range | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: E845 identifies recursive iter in a field type; range over iter, iter(n), or a wider span within the written law. | Empty, off-reference, out-of-law or unlocated spans; a different operation, context or unrecognized cause. |

## Findings and dispositions

- G6 rejected root-cause retention that FG1 permits. Removed that prohibition;
  the parent's cause and the child's E340 target remain required.
- G5 inferred an edit from a warning code. Recorded code/declaration/message and
  required matching advice within the edit target before applying the
  replacement. Unknown advice fails for investigation; it is never silently
  treated as the same edit. This mapping can be retired with temporary defect
  tracking.
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
  named explicitly (`absentOutputs`/`absentOutputFamilies`); constructor
  availability is observed through real clients that must receive E343.
  Positive programs prove each constructor is usable while absent from outputs.
  Observer leak controls replay those real client verdicts and actual model/fold
  outputs alongside a synthetic duplicate refusal. They establish predicate
  sensitivity, not a compiler-generated partial-publication bug. Downstream
  original cases establish the actual refusal and preservation behavior.
- Collision diagnostics previously allowed exactly one gap. Refused clients now
  carry individual codes, and their expected diagnostics compose with the
  declaration refusal. A control combines E343 and E606 clients with the
  duplicate diagnostic, and rejects swapped codes, missing clients and extra
  diagnostics.
- G12's first successor could not distinguish using the recursive result from
  substituting `c`. Every context now requires `computation2`. Executable
  constant and step-ignoring counterexamples independently specify the client
  verdicts and E606 failures that must reject them. Removing a second-step
  witness fails the minimum-obligation check.
- Historical cause matching was stronger than active acceptance. A shared
  diagnostic decoder now serves both historical observations and desired
  expectations, with independently stated expected causes. Declaration and
  refused-client diagnostics compose through the same complete matcher.
  G1/G1-initial pin each missing constructor name; G6 pins the dependency
  target; G10 and G12-range pin causes alongside ranges; G8 uses the same
  matcher for its ordered endpoints. Removing mandatory cause metadata fails
  before checking.
- Negative acceptance controls were written by hand for each case, and after
  `89c97e99` only diagnostic causes had them. G9's labels, targets and sites,
  G3's refusal meaning, the duplicate refusal's reason, G10's clause bound and
  assumption-freedom could each be deleted without a failing test; some were
  guarded only by the historical record. Each requirement now carries its
  counterexamples and the audit applies them to every case. The requirement map's
  `checks` keep each witness's requirements applicable.
- Observation was entangled with compiler calls, and the harness copied results
  without rebinding `get`. Compiler and lint results are now collected once;
  facts and requirements are pure functions of that evidence. Assertions that
  duplicated requirements (invariant clients, the parent's cause, the presence of
  an expected refusal) became observations, so they cannot preempt a recorded
  defect or a counterexample.
- G2 accepted a Hom without the fixed-domain operation's preservation field and
  never fixed its universe, contrary to FG3's exit. Clients now use `map_op` at
  U0 and U1, pin the U1 level, and require a refused U0 lowering.
- The debt control changed only the first primary gap, so G6's child was never
  compared with its record. Every primary gap and dependency target now changes
  in turn, and only an unrecognized observation is accepted.
- The harness's flat activation control replaced only the first `= S.c`, leaving
  `wrong` ill-typed rather than wrong. It duplicated the audit's supported source
  and was removed; every supported-source edit now asserts that it applied.
- Diagnostic matching was first-fit, so a code-only expectation could take the
  diagnostic a cause-bearing one needed. It now finds a complete matching
  independently of expectation order. The E845 decoder retains its context, and
  the passing E845 control uses the shared matcher.
- Removed the harness's duplicate G12 nonrecursive controls. The audit retains
  all three supported contexts and their constant/ignored-recursion mutants.

## Validation and lifecycle

Run the contracts, harness and audit together:

```sh
npm test -- tests/frontend-generation.test.mjs tests/frontend-generation-harness.test.mjs tests/frontend-generation-audit.test.mjs
```

The audit requires an accepted observation for every executable case and a
counterexample for every applicable requirement. These checks establish
coverage of the stated controls; the contents of counterexamples and supported
sources still require semantic review. Use the contributor checklist on new
cases, and add a counterexample with each new requirement.

An incorrect implementation that still checks clients is a separate audit
boundary from an unrelated diagnostic: semantic mutants cover constant
computations, ignored recursive results and capture of a shadowing parameter.
The [independent requirement map](../../tests/fixtures/frontend-generation-requirements.mjs)
records obligations, their witnesses and the requirements those witnesses keep.
Removing a fixture and its manifest row, or a requirement's applicability,
cannot erase an obligation.

Keep the roadmap as the behavioral authority when integrating downstream fixes.
Activate each fixed original case and preserve downstream search-eligibility,
explicit-path, provenance, named-constructor and recursive-predecessor controls.
Once all original cases pass, retire known-defect records and tests specific to
that lifecycle. Retain the requirements, their counterexamples and the
distinguishing controls that still protect active behavior. Integration,
mutation and full-suite results belong in the PR's validation record at the
tested revision.
