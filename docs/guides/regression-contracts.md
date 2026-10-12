# Writing regression contracts

A regression must distinguish the intended behavior from the failure it guards.
Use the relevant language specification or roadmap as the authority for behavior;
an observed compiler result is evidence, not a specification. Link that authority
from the case's manifest or test explanation.

Before writing a case, identify the required outcome, its prerequisites and the
evidence that distinguishes the defect. Diagnostic codes identify categories:
two different type errors can share a code, so state the whole message, with
its subject, expected/actual types, dependency or proposed edit.

## State the case in Cubist

Write the case as a Cubist module, with the outcome stated as the Cubist tests
state theirs ([`cubist-tests/README.md`](../../cubist-tests/README.md)): an
`// Error:` comment, with the exact message, above each declaration that must
be refused, and nothing above one that must check. Observe in JavaScript only
what a comment cannot state, such as a source range, a link, lint advice or a
published name, and put its desired value beside the observation.

Take a desired outcome from the specification, or from the fixing
implementation once it exists, and review it against the specification. Never
take it from an implementation that still has the defect: `inline-errors
--write` run on that compiler records the wrong behavior as accepted.

## Make the clients distinguish the defect

- Use real programs and independently stated clients, never expected results
  derived from the generator under test.
- Pair an intended equation with a plausible incorrect one that must be
  refused, so that a constant or wrongly resolved implementation cannot
  satisfy both.
- Exercise distinct branch results, and inputs that depend on a recursive
  result: a first successor can coincide with a step that substitutes the
  base value, so add a second.
- Test name availability with clients, not with the output list:
  constructors can be available without being outputs.
- Cover each context a defect can appear in (direct, inherited, initial
  model, grouped binders) with its own case.
- Keep safe neighboring behavior checked. Suppressing unsafe lint advice, for
  example, must keep safe advice for both single and grouped binders.

## Track open defects explicitly

While a fix is pending, record what the case shows today, separately from
the case. The case is a TODO only while it shows exactly that record. Any
other result fails and must be investigated, and a TODO never counts as
completion. The fixing PR removes the record, and nothing else changes.

When a review exposes a mistake, inspect its class across sibling cases, and
fix it where it occurs. Before submitting a case, answer:

- Can it reject a valid implementation?
- Can a different bug produce the same observation?
- Which wrong implementation does each client distinguish?
