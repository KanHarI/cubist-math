# Frontend generation comparison manifest

`frontend-generation.mjs` pins FG0's evidence at `00d4ecce`. Each G1–G6
and G8–G12 entry names its source, responsible phase, intended contract,
and checked clients.
[frontend-generation.test.mjs](../frontend-generation.test.mjs) implements
the comparison, including independent equations rather than generated-output
snapshots. Run it with `npm test -- tests/frontend-generation.test.mjs`.

All listed clients must be verified without assumptions. G1 covers both
orders of definition/inductive collisions, definition/initial-model
collisions, and same-kind duplicates, preserving the first binding and its
clients. G2's clients fix the public Hom/Iso types and composition
computation at U0 and U1. G3 preserves the base theory while withholding
both unsupported artifact families. G4 covers both flat and nested matches.
G5 uses positional operation calls, identity and a generated model/fold to
test the actual lint rewrite for both single and grouped operation binders.
Named operation calls are not currently supported. Passing controls require
W705 and W706 for ordinary safe unused binders and check their arrow-form
rewrites.
G11 requires opposite outcomes for intended and captured
equations, including helper chains, grouped/dependent binders, inheritance
and generated clients. G12 checks a computing call and keeps a passing
E845 refusal control for recursive unfolding in a law. `G12-range` tracks
that refusal's nonempty range over the original `iter(n)` call as a
separate FG5 expected failure, so it can be activated independently of the
FG2/FG4 value-call fix.

G8–G10 additionally compare diagnostic codes, endpoints, original source
ranges, every written binder/use label and definition target. These
observations do not normalize internal names or missing links away.
G8 permits a range within the written definition body that covers the
wildcard's body token; it does not require the range to narrow to that token.
B1 checks file-level selection before later globals, changed selections,
imports and generated constructor domains. `historicalCoverage` and
`passingCoverage` map fixed examples to existing tests. H1 names the
`Constant`/`K`/`idem_at` and `Named`/`named_fold` cases in
[`initial_models.cubist`](../../cubist-tests/initial_models.cubist), checked
by the normal Cubist regression suite. The mapping verifies their parsed
declarations and the module's inclusion in that suite. Further controls
exercise inherited, bare/partial helpers with free fields under colliding
law binders, initial-model recursion and explicit path bodies.

`expectedFailures` is temporary, executable debt. Each listed contract is
run, must fail an assertion, and is reported as TODO. Crashes and setup
errors fail the suite. Every fixture's source sites, observation counts and
lint rewrite targets are validated outside the expected-failure handler and
in the always-running mapping test. An unexpected pass fails too: remove that
ID from the set in the fixing PR. `CUBIST_GENERATION_STRICT=1` runs every contract
as an ordinary assertion, useful to expose the complete unresolved list.
TODO tests never count as evidence that an implementation phase is done.

G7 is a historical symptom, not a currently reproduced defect. FG1 must
inject a genuine failed parent projection and verify its dependents,
publication rollback, and progress. It must not repurpose a now-passing
capture example as evidence of an open bug. The later phases extend this
manifest with their full exit cases; FG0 does not claim those gates exist.
