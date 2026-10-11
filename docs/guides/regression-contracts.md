# Writing regression contracts

A regression must distinguish the intended behavior from the failure it guards.
Use the relevant language specification or roadmap as the authority for behavior;
an observed compiler result is evidence, not a specification. Link that authority
from the fixture manifest or test explanation.

Before writing assertions, identify the required outcome, permitted variation,
prerequisites and the evidence that distinguishes the defect. In particular,
diagnostic codes identify categories: two different type errors can share a code.
Retain the relevant subject, expected/actual types, dependency, source origin or
proposed edit. Prefer existing structured fields. Where the public API supplies
only text, extract the distinguishing payload and document what is ignored.
Avoid snapshotting unrelated formatting or generating expected semantics from
the same implementation under test.

Use the shared diagnostic decoder and matcher in
[`frontend-generation-diagnostics.mjs`](../../tests/frontend-generation-diagnostics.mjs).
An expectation states the declaration, code and relevant `cause`, independently
of the historical defect record. It may state only fields from the matcher's
field table, and each field there carries its own counterexamples, so a stated
field is always compared and perturbed. E343 names its untranslated subject,
E340 its dependency, E871 its helper and captured field, and E845 its recursive
operation and context. A range check composes with this meaning; it cannot
replace it.
Code-only E606 equation refusals remain appropriate when independent accepted
and refused clients establish the semantic distinction. Pin found/expected
endpoints when those endpoints are themselves the contract, as in G8.

Decode a recognized diagnostic form into its semantic roles before comparing
it with the independently stated cause. G1 requires `{duplicate: "N"}`;
its frontend and kernel codes may differ, so only this cause may omit `code`.
G3 requires `{operation: "op", argument: "p", law: "l"}` for each client.
Unknown wording remains an unrecognized reason. Finding the words somewhere
in a message does not establish the declaration, roles or dependency direction.
Keep valid alternative spellings explicit and test them against the same cause.

Generate permitted variations within the matched expectation's constraints:
alternate wording may remain valid when a diagnostic code is pinned, but a
different code does not. Exercise stronger fixtures through the whole audit,
not just validation. Do not filter generated controls through the acceptance
matcher; that would hide the matcher rejecting a valid alternative.

For contracts that classify expected failures, exercise these boundaries:

| Control | Required result |
| --- | --- |
| Recorded defect | Recognized debt, never successful implementation |
| Valid corrected behavior, including permitted alternatives | Desired requirements pass; a stale defect record demands activation |
| Different failure, including one with the same code | Ordinary failure |
| Well-typed but semantically wrong implementation | Ordinary failure, even if declarations check |
| Broken fixture or unmet prerequisite | Ordinary failure, never known debt |

Keep the contract and the expected-failure lifecycle apart. A case holds only
its contract; defect records live in their own module, and only the lifecycle
reads them. Collect compiler results once, as plain data, and judge them with
pure functions. Index each test by what it depends on: a test that needs a
record is keyed by that record and disappears with it, a test of the classifier
uses synthetic observations and records, and lifecycle tests live in their own
file. Activating a case is then only the removal of its record, and retiring
the lifecycle only deletes files. Check this by running the whole suite against
the fixing compiler with every record removed.

Exercise the different-failure boundary twice: against each recorded debt, and
against accepted observations with no record at all. Make the second structural
rather than a per-case review step:

- Write each requirement as a table of named conditions. Each condition carries
  the plausible wrong results that must violate it, and each requirement lists
  the valid variations it permits.
- Apply every one to an accepted observation of each case. The observation and
  its permitted variations must meet every requirement, and each
  counterexample must violate its condition.
- Require some counterexample to violate each condition alone. A span that
  crosses both ends of its region leaves either bound unguarded. A condition
  that another implies, such as the nonemptiness of a span that covers a
  nonempty site, cannot be violated alone; leave it out.
- State the conditions independently as well: deleting a condition deletes its
  counterexamples with it.

Facts only project evidence. They may locate it by declaration, site or region,
but must not compare it with an expectation or drop evidence that a condition
judges. Selecting only the links that span a label exactly is such a hidden
condition: no counterexample can violate it. Check the judging code from the
other side by mutation: change each comparison in turn and require the audit
to notice. A surviving mutant is a check that nothing exercises; add the
counterexample, permitted variation or witness that distinguishes it, such as
a second refused client when a condition quantifies over refused clients.

Mutation coverage exercises the implemented predicate; its meaning also needs
independently authored counterexamples. Preserve vocabulary while changing
meaning: reverse a dependency, swap an argument and a law, or report an
internal binding error that also says "already". Those cases must fail even
when every comparison in the original predicate has been exercised.

Map behavioral obligations independently of the fixture registry. A case-ID
inventory cannot discover a requirement omitted from both the source fixtures
and their manifest. Name the contexts, the incorrect alternative each witness
distinguishes and the requirements it must keep. State each witness's minimum
expectations as data, and derive what the audit perturbs from those minimums,
never from the expectation under test; otherwise weakening an expectation also
removes the counterexample that would expose it. Keep client verdicts,
publication and source expectations composable across diagnostic kinds. Resolve
source anchors before observation; ambiguous occurrences are fixture errors
unless explicitly selected.

Use real programs and independently stated clients for semantic evidence.
Exercise distinct branch results and inputs that distinguish dependence on a
recursive result. A first successor can coincide with a step that substitutes
the base value; add a second successor and explicitly reject that wrong source.
Pair intended equations with plausible incorrect equations that must be refused;
check that a constant or incorrectly resolved implementation cannot satisfy both.
A supported control that avoids the old compiler defect still needs these
semantic distinctions.

Keep the observation's guarantee precise. An absent reported output does not
imply an unavailable name: constructors can be available without being outputs.
Test name availability with real clients, including accepted clients when the
binding should survive. Assign diagnostic expectations per client, and compose
them with declaration diagnostics before comparing the complete expected
diagnostic set.
An observer audit must use results possible at that interface; obtain positive
controls from real programs before injecting a leak or refusal. A supported
finite unrolling proves only the selected computation witnesses.

Small injected diagnostic/link observations can test a contract's acceptance
boundary before a compiler fix exists; label them as such. They do not prove
that the compiler produces the desired result. Keep actual integration checks
when a fixed implementation becomes available. A supported simpler source can
prove that the predicate is reachable without establishing the original fix.
Every edit that derives such a source must assert that it applied: a partly
edited source can refuse a client for an unrelated reason, such as a type error.

When a review exposes a mistake, inspect its class across sibling contracts:
range checks, error projections, rewrite observers, activation state or context
variants. Add a distinguishing control for the mechanism, record the audit's
scope, and check required neighboring behavior. For example, suppressing unsafe
lint advice must preserve safe advice for both single and grouped binders.
Prefer fixing the mechanism, such as a shared requirement and its
counterexamples, or one table that drives both a check and its counterexamples,
to adding one more per-case control.

Before submitting a new contract or changing one, answer:

- Can this test reject a valid implementation? Which allowed alternatives were
  checked?
- Can a different bug produce the same observation? Which information is
  discarded?
- What deliberately broken behavior proves each requirement is sensitive?

Remove a case's record with its fix; nothing else changes. Once all cases are
active, retire the records, the classifier and its tests together while
preserving semantic assertions, case selectors and distinguishing controls. A
review fix must not weaken the expected behavior merely to match a new
observation.
