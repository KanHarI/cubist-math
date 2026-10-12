# FG0 contract audit

Scope: the executable cases from PR #205, restored in PR #217, including the
diagnostic acceptance review of `89c97e99`, the requirement review of
`687f554c`, the activation review of `2e27565b`, the condition review of
`f48bc1f7`, the guard review of `2a246504` and the design review of
`637734ab`, the diagnostic-cause review of `f3b68c5f`, the optional-code
review of `fbe53b4e`, the witness review of `1628df46` and the anchor review
of `e9e85e18`. The
[frontend generation roadmap](../roadmaps/frontend-generation.md) supplies the
behavioral requirements. The [inventory](frontend-generation-gaps.md)
describes defects; the [manifest](../../tests/fixtures/frontend-generation.md)
maps cases to evidence. This audit checks those mappings and acceptance
boundaries without declaring the compiler defects fixed.

The procedure is the
[regression contract checklist](../guides/regression-contracts.md).
[frontend-generation-audit.test.mjs](../../tests/frontend-generation-audit.test.mjs)
judges every case by its requirements alone. Each requirement in
[frontend-generation-contracts.mjs](../../tests/frontend-generation-contracts.mjs)
is a table of named conditions over facts that only project evidence. Each
condition carries its counterexamples, and each requirement lists its permitted
variations. The audit's controls:

- Acceptance: an accepted observation of the case, and each permitted
  variation of it, meets every requirement.
- Counterexamples: every counterexample of every applicable condition is
  applied to that accepted observation, and each must violate its condition.
- Isolation: some counterexample violates each condition alone, so a check
  that combines two conditions cannot leave either unguarded.
- Mutation: changing any comparison in the facts that conditions read, in the
  conditions or in the diagnostic field matchers must change some verdict of
  the controls above.

The audit never reads defect records or classifies cases, so activating a case
or retiring every record leaves it unchanged. These controls cover each case
without per-case audit code. The
[requirement map](../../tests/fixtures/frontend-generation-requirements.mjs)
names the requirements each witness must keep, the expectations its case must
keep and, independently of the tables, the conditions each requirement judges.

The expected-failure lifecycle is separate: records live in
[frontend-generation-defects.mjs](../../tests/fixtures/frontend-generation-defects.mjs)
and only [frontend-generation-lifecycle.mjs](../../tests/frontend-generation-lifecycle.mjs)
classifies observations against them. Its
[tests](../../tests/frontend-generation-lifecycle.test.mjs) recognize each
recorded debt and reject it after any one primary cause or dependency target
changes (navigation for G9); that test belongs to its record. They test the
classifier once with synthetic observations. The
[harness](../../tests/frontend-generation-harness.test.mjs)'s prerequisite and
fixture checks need no lifecycle and hold whether or not a case is recorded.
W705 and W706 safe-advice controls remain active.

## Requirements and controls

“Source” below means real independently checked clients on a supported variant.
“Observer” means an explicitly injected diagnostic/publication result layered
over real checked outputs. Observer controls exercise the predicate's boundary;
they do not establish a compiler fix. Supported variants avoid the original bug
and likewise do not establish that its original source is fixed. Every row also
rejects the counterexamples of its requirements' conditions, which the
contract tables list; the last column states only what distinguishes the case.

| Cases | Authority | Accepted observation and allowed variation | Distinctions that must be refused |
| --- | --- | --- | --- |
| G1, G1-initial, G1-reverse, G1-same-kind | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: check the original declaration and clients without the duplicate, then inject its refusal. Duplicate wording/code may vary within the documented refusal contract, including the kernel's own same-kind refusal. | Another type for the original binding; a duplicate accepted or refused for another reason; a real constructor client that checks or names another missing name; a real model/fold output. |
| G2 | [FG3](../roadmaps/frontend-generation.md#fg3-infer-universes-from-the-generated-telescope) | Source: the domain moves into the model's universe (`op(A : U, x : A)`). Hom/Iso, computation, `map_op` preservation and level clients check at U0/U1; that variant's U1 level pin is U2. Stating a U0 model's Hom in U0 is refused with `found U1, expected U0`. | A missing preservation field or level client; an accepted lowering or one with other endpoints; a different same-code Hom mismatch. |
| G3 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Observer: retain checked base clients, withhold Hom/Iso, and require E817 with operation op, argument p and law l for both clients. Recognized focused wordings decode to that same cause. | A leaked family root or member; swapped semantic roles, a reversed or denied dependency, a carrier instead of a law, an arrow-operation refusal, or another code. |
| G4, G4-flat | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: Nat motives, with distinct branch results and independently stated accepted/refused equations. | Constant match result; wrong clause result; same E546 with a different primary cause. |
| G5, G5-single | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Real original clients with unsafe advice suppressed; existing controls preserve ordinary safe W705/W706. Only identified advice at the source target, in any order, authorizes the associated rewrite. | Any issued warning, whatever its code, other than exactly the identified advice within its target; an authorized rewrite that loses a client. |
| G6 | [FG1](../roadmaps/frontend-generation.md#fg1-unify-declaration-ownership-and-publication) | Observer: child E340 has dependency target P, with or without an attached root cause. Parent E343 has untranslated subject Undefined and independent clients check. | Another dependency, including Q whose attached cause mentions P; an untranslated-name message with E340; another parent subject. |
| G8 | [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Observer: E606 with the specified found/expected endpoints; token or wider body span accepted. | Swapped or changed endpoints; a span that does not cover the token within the body; a different generation cause. |
| G9 | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Source: rename the field that the law binder collides with, keeping the written law, its labels and sites, and independently stated meaning. Identical repeated links are equivalent, and links that only touch a site belong to their own text. | At any written site, any link that is not the written label targeting its binder over exactly that label, including one beside the correct link; a site without a link. |
| G10 | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: E871 identifies helper k and captured field c; the binder, helper call, or enclosing conflicting clause supplies a nonempty origin. | A span that covers neither the binder nor the helper call within the clause; a different helper, field or unrecognized cause. |
| G11, G11-grouped-dependent, G11-inherited, G11-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename the derived parameter through its telescope/body, preserving all independent intended/captured equations in each context. | A refused intended equation or a checked captured equation, in any context. The captured refusal's E606 payload is deliberately free: the opposite verdicts carry the distinction. |
| G12, G12-inherited, G12-initial | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly), [FG4](../roadmaps/frontend-generation.md#fg4-carry-evidence-and-compiler-state-with-the-context) | Source: two-step nonrecursive unrolling, retaining zero/one/two-step and wrong-result clients in all three contexts. This establishes the finite witnesses only. | Constant iter makes the wrong equation check; ignoring the recursive result preserves the first step but fails the second with E606. |
| G12-shadowed | [FG2](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly) | Source: rename only the local iter parameter; intended/local and captured/field equations retain opposite verdicts. A separate field-type control checks today. | Replacing the local call by the earlier field result makes the captured equation check. |
| G12-range | [FG5](../roadmaps/frontend-generation.md#fg5-preserve-public-interfaces-and-source-provenance) | Observer: E845 identifies recursive iter in a field type; range over iter, iter(n), or a wider span within the written law. | A span that does not cover the reference within the law; a different operation, context or unrecognized cause. |

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
- The audit asserted the defect records alongside the requirements: every
  accepted observation had to be an unexpected pass, and every case had to be
  recognized debt. With the records removed against the fixing compiler
  `d4a5ecf3`, most audit tests and half the harness tests failed, although
  the contracts passed. Cases now hold only their contracts; records live in
  their own module and only the lifecycle classifier reads them. The audit
  judges requirements alone, debt recognition is keyed by record, the
  classifier is tested with synthetic observations, and G5's advice controls
  build advice from the identified edit instead of the current linter.
  Activating a case is now only the removal of its record; the PR's
  validation record gives the check against the fixing compiler.
- No counterexample reported a diagnostic on another declaration, so a matcher
  that ignored names passed every test. The matcher's compared fields and
  their counterexamples now come from one table. An expectation may state only
  those fields, and a stated field without counterexamples fails.
- Whether a diagnostic's cause received counterexamples depended on the
  expectation under test, and G8's missing cause failed only by a `TypeError`
  after checking. Obligations now state their witnesses' minimum expectations as
  data, replacing the hand-written minimum checks. A weaker fixture is rejected
  before checking, a cause outside the codes that always carry one must be
  required by a witness, and cause counterexamples come from the witness. The
  witnesses also pin G3's refusal words, G4's branch results, G5's interface
  clients, G9's observation sites and G10's helper and field.
- The G11 row listed a different same-code mismatch among the counterexamples
  that must be refused, which holds only for the historical record. It now
  states the opposite equation verdicts that carry the distinction.
- Range, link and advice requirements combine conditions, but their
  counterexamples violated only some of them. The only out-of-region span
  crossed both ends of its region, and none started inside its site; link
  counterexamples changed every link at a site together; misplaced advice
  crossed only the start of its target. Weakening either region bound, the
  site's start bound, every-link-at-a-site to some link, or advice's end bound
  passed every test; G10's clause start was guarded only by its defect record.
  Each condition now has a counterexample that violates it alone, and G8 gained
  a later declaration so that its body range ends inside the source. G5's
  unapplied-advice control runs every advice counterexample instead of a
  hand-written copy of that list.
- Three guards were weaker than this report stated. A span that covers a
  nonempty site is nonempty, so no counterexample violated the range's
  nonemptiness alone, and only the defect records noticed its removal; it is
  now a recorded fact, not a judged condition. The rule that every stated
  diagnostic field receives counterexamples ran only while building them,
  after validation had already rejected every fixture it could catch; fixture
  validation now applies the field table's rule to every expected diagnostic.
  G5's advice audit required the current compiler to refuse the arrow form,
  which a later preserving simplification would change; it now judges
  observer rewrite results that preserve or lose a client.
- The link requirement selected links by their exact span before judging
  them, so no counterexample moved a link: checking either bound alone passed
  every test. The cause was structural. Facts also judged refusal words,
  endpoints, duplicate reasons and child messages against expectations, and
  each requirement's checks and counterexamples were written separately, so
  completeness depended on a reviewer. Facts now only project evidence. Each
  requirement is a table of named conditions with their counterexamples and
  permitted variations, stated independently in the requirement map. Some
  counterexample must violate each condition alone, and a mutation sweep
  changes every comparison in the judging code. The sweep found three more
  unexercised checks: removing only one bound of a refusal's span, a
  misplaced link beside a correct one, and G3's single refused client, which
  could not tell every refusal from some. G3 now also requires its Iso client
  to be refused; the fixing compiler gives it the same focused E817. Compiler
  results compute some fields from the kernel when first read, so evidence is
  now copied as plain data when collected. Lifecycle tests moved to their own
  file, so retiring them no longer edits contract tests.
- G1 and G3 still judged causes by vocabulary: an internal "already bound"
  error counted as a duplicate declaration, and G3 accepted swapped argument
  and law roles or even a message saying they were independent. Moving those
  checks into conditions and exercising their comparisons did not correct
  their meaning. Both now use the shared diagnostic decoder and matcher.
  G1 states the duplicate subject, with its code left free; G3 states the
  operation, argument and law for both Hom and Iso clients. The requirement
  map independently requires those causes. Recognized alternative forms are
  accepted, unrecognized wording fails, and the audit independently states
  the misleading messages alongside the field table's role counterexamples.
  Redundant duplicate/refusal facts and conditions were removed. The records
  lose those redundant projections, and the kernel duplicate's root cause
  now records its decoded subject; they still observe the same compiler debt.
- Permitted diagnostic variations ignored a fixture's optional code pin, so
  a stronger duplicate expectation passed validation but failed its audit.
  Variation generation now receives the matched expectation, as counterexample
  generation already did. Wording still varies while a pinned code stays fixed;
  an unpinned duplicate still exercises both frontend and kernel codes. The
  audit exercises all collision cases with unpinned and pinned codes, including
  a code outside those two defaults, reordered diagnostics and a refused
  alternative code. Controls are constructed within the stated constraints,
  never filtered by the matcher whose acceptance they test.
- Witnesses stated minimums, but nothing required a case's names to have one.
  G1's `original` client, which the ownership obligation's "lost original
  client" names, G3's `usable` base client and G6's `independent` recovery
  client could each be deleted while every audit and harness test passed;
  only the temporary records noticed. Every client, refused client, absent
  output and declaration diagnostic a registered case states must now be named
  by one of its witnesses, so the map names all of them, and the audit
  rejects deleting those three and adding an unnamed name of each kind. A
  misspelled client now fails before checking.
- The guide and lifecycle said that retiring the lifecycle only deletes files,
  but the runner imports the records and `recordCase`. The contracts now
  export `assertCase`, which the lifecycle uses for unrecorded and strict
  cases; RC0 deletes the lifecycle's files and has the runner call it instead.
- Advice conditions compared issued and identified advice by position, so the
  identified advice in another order was refused. Both are now compared in
  one order: the reversed identified advice is a permitted variation, and a
  case may state its identified advice in either order.
- Witnesses kept names but not source anchors or rewrites, from which the
  range and advice counterexamples are placed, so weakening an anchor moved
  its counterexamples with it. Narrowing G8's token to `1`, G12-range's to `i`
  or G10's call to `k` passed every test, records included, and then accepted
  a refusal over that character or name alone. Widening G8's scope, G10's
  conflict or G12-range's scope, or replacing G5's rewrite with one that keeps
  every client, passed every audit and harness test. Witnesses now keep every
  expectation a case states: names as minimums, and anchors, rewrites, the
  collision's binding and the failed dependency's identity exactly. A case
  field that no witness can keep fails, so a misspelled expectation is not
  ignored. The G9 supported source now renames the field instead of the law
  binder, so it keeps the case's own observations. The audit rejects each of
  those edits.
- Lint evidence kept only W705 and W706, so the advice conditions never saw
  a warning under another code: today's unsafe advice under a new code was
  taken as withheld, its rewrite was never checked, and G5 and G5-single
  passed. Collection sat outside the mutation sweep. Every warning is now
  evidence, and a counterexample issues the identified advice under a new code;
  restoring the filter fails both cases' advice audits.

## Validation and lifecycle

Run the contracts, harness, lifecycle and audit together:

```sh
npm test -- tests/frontend-generation.test.mjs tests/frontend-generation-harness.test.mjs tests/frontend-generation-lifecycle.test.mjs tests/frontend-generation-audit.test.mjs
```

The audit requires an accepted observation for every executable case, a
counterexample that violates each condition alone, and no surviving mutant.
These checks establish coverage of the stated controls; the contents of
counterexamples, permitted variations and supported sources still require
semantic review. Use the contributor checklist on new cases. Add a condition
with its counterexamples, and name it in the requirement map. When the sweep
reports a survivor, add what distinguishes it rather than an exception.

To check activation, copy these files over the fixing compiler, replace the
records module with an empty `knownDefects`, and run the same four files.

An incorrect implementation that still checks clients is a separate audit
boundary from an unrelated diagnostic: semantic mutants cover constant
computations, ignored recursive results and capture of a shadowing parameter.
The [independent requirement map](../../tests/fixtures/frontend-generation-requirements.mjs)
records obligations, their witnesses and the requirements those witnesses keep.
Removing a fixture and its manifest row, or a requirement's applicability,
cannot erase an obligation.

Keep the roadmap as the behavioral authority when integrating downstream fixes.
Activate each fixed original case by removing its record, and preserve
downstream search-eligibility, explicit-path, provenance, named-constructor and
recursive-predecessor controls. Once all original cases pass, delete the
records module, the lifecycle module and its test file, and have the runner
call `assertCase` in place of `recordCase`. Retain the requirements, their
counterexamples and the distinguishing controls that still protect active
behavior. Integration, mutation and full-suite results belong in the PR's
validation record at the tested revision.
