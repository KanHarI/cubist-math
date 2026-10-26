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

New semantic fixtures live under `tests/fixtures/contracts/`. Give each
case a stable, globally unique ID and place its pragmas immediately before the
declaration or supported directive:

```cubist
# test(identity.local_assumptions)
# expect_axioms([])
def identity(A : U0, x : A) : A := x;

# test(refusal.wrong_type)
# expect_error(E606)
def impossible : Void := tt;
```

`# test` alone requires success and no warnings. `# expect_error(E###)` requires
exactly one refusal owned by that target, excluding dependent cascades. Repeat
`# expect_warning(W###)` for the exact warning multiset. `# expect_axioms([...])`
requires every checked output owned by the target (including each generated
family member) to have exactly those external transitive assumptions, including
type dependencies and excluding bound hypotheses. It cannot accompany an
expected refusal. Name each assumption by its label: `LEM` or `Choice` for
the library's axioms (only as read from `library/`), `module::Name` for
another module's axiom, and
`Truncate` or `LEM[Truncate]` for the archive's legacy builtins. An axiom's
label names its defining module and declaration, independently of source
aliases.

Pragmas can target definitions, inductives, theories, initial/free models,
`evaluate` and `print`; assumption expectations require a declaration. Parser
errors, missing imports, resource exhaustion and crashes never satisfy an
expected refusal. All imports must succeed even if unused; all unannotated
local declarations must succeed. Unknown pragmas, invalid combinations, duplicate
IDs and missing targets fail. Ordinary compilation rejects pragmas; test hosts
explicitly enable them. They never affect kernel admission.

Run `node --test tests/cubist-contracts.test.mjs`, or set `CUBIST_TEST_CASES` to a
JSON list of exact IDs. An explicit empty, duplicate or unknown selection fails.
Each selected fixture compiles once; its selected cases share the observation,
then its kernel is disposed. The full suite selects every case. Use existing
`evaluate ... expecting ...` and `computable def` syntax for computation, and
retain JavaScript for host failures, source links, message goldens, unmigrated
work counters and DOM. Put checked `// Error:` comments after the pragmas and
directly above the declaration so the comment reader attaches them to it.

Use `evaluate nonempty P by proof;` to check assumption-free evidence of `P`
without fully normalizing the proof. Its counterpart,
`evaluate empty P by proof;`, checks evidence of `P -> Void`. For
disequalities, use `evaluate empty (x = y) by proof;`; different refutations
need not have the same normal form. Decision
procedures can also be tested by inspecting their `left`/`right` branch.
Reserve full-normal-form assertions for computations whose result matters.

For exact diagnostic ranges, pair `# expect_error` with
`# expect_error_at(iter(n))`. The balanced token sequence must occur exactly
once in its target's written source; whitespace and comments are ignored.
The diagnostic's primary site and the published gap's range must both cover
that sequence exactly, in the same module. Missing or ambiguous anchors fail
instead of choosing an occurrence.
An anchor is source text, not an expression that the checker evaluates.

`# expect_searches(1)` requires exactly one charged coherence search on an
ordinary definition. Missing counters fail even for an expected zero. It does
not assert cache-dependent kernel step counts or elapsed time. These two forms
replace the G8 and G12 range/work wrappers; their exact message goldens remain
in JavaScript. Further observations should be added only for actual migrations.

Fixtures can import sibling Cubist modules through the ordinary source loader;
use distinct stable case IDs throughout the bundle. Each fixture still runs
with its own program and kernel. Host reset/failure injection remains in JavaScript.

The test runner, comment tool and tests-area benchmark share the same observer.
The benchmark keeps contract failures visible even when a declaration checks.
`inline-errors --write` validates existing pragmas before writing comments and
never creates or changes semantic expectations.

Existing diagnostic presentation fixtures remain Cubist modules, with the outcome stated as the Cubist tests
state theirs ([`cubist-tests/README.md`](../../cubist-tests/README.md)): an
`// Error:` comment, with the exact message, above each declaration that must
be refused, and nothing above one that must check.

Before comparing comments or recognizing a known defect, account for every
checker failure. These cases require all imports to check, including unused
and transitive imports. Every local failure must have a matching reported
error; consume each error once and reject any failures left over.
This preserves intentional local refusals without hiding imported failures.

The comment comparison sees local errors and warnings, at the line of their
declaration. It does not see a declaration with no output,
which reports nothing, or where in its line a refusal lies. Require each
declaration without a comment to have an output of its own, and observe in
JavaScript only what the comparison cannot see and no pragma expresses, such
as a link or a published name, with its desired value beside the observation.
State an exact source range in a contract fixture with `# expect_error_at`.
Lint advice is a warning, which a comment states.

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
- Include an input where the fix's result differs from a blanket one: a
  universe that needs U1 for one theory must stay U0 for an ordinary one.
- Test name availability with clients, not with the output list:
  constructors can be available without being outputs. A generated
  interface the contract needs, such as a constructor or an initial model's
  `model` and `fold`, needs a written client: a generated output that
  disappears reports nothing.
- Cover each context a defect can appear in (direct, inherited, initial
  model, grouped binders) with its own case.
- Keep safe neighboring behavior checked. Suppressing unsafe lint advice, for
  example, must keep safe advice for both single and grouped binders.

## Track open defects explicitly

While a fix is pending, record what the case shows today, separately from
the case. The case is a TODO only while it shows exactly that record. Any
other result fails and must be investigated, and a TODO never counts as
completion. The fixing PR removes the record; the case and its desired values
stay as they are.

When a review exposes a mistake, inspect its class across sibling cases, and
fix it where it occurs. Before submitting a case, answer:

- Can it reject a valid implementation?
- Can a different bug produce the same observation?
- Which wrong implementation does each client distinguish?
- Would a partial fix pass, one that resolves the right name but publishes
  the wrong declaration, or refuses on the right line over the wrong token?
  Reverting the fix shows only that the case sees the defect.
