# Frontend generation comparison manifest

`frontend-generation.mjs` pins FG0's evidence at `00d4ecce`. Each G1–G6
and G8–G12 entry names its source, responsible phase, intended contract,
and checked clients. `frontend-generation.test.mjs` implements the
comparison, including independent equations rather than generated-output
snapshots. Run it with `npm test -- tests/frontend-generation.test.mjs`.

All listed clients must be verified without assumptions. G2's clients fix
the public Hom/Iso types and composition computation. G3 preserves the
base theory while withholding both unsupported artifact families. G5 uses
named calls, identity and a generated model/fold to test the actual lint
rewrite. G11 requires opposite outcomes for intended and captured
equations, including helper chains, grouped/dependent binders, inheritance
and generated clients. G12 checks a computing call and keeps a separate
E845 refusal control for recursive unfolding in a law.

G8–G10 additionally compare diagnostic codes, endpoints, original source
ranges, every written binder/use label and definition target. These
observations do not normalize internal names or missing links away.
B1 checks file-level selection before later globals, changed selections,
imports and generated constructor domains. `historicalCoverage` and
`passingCoverage` map fixed examples to existing tests; further controls
exercise inherited, bare/partial helpers, initial-model recursion and
explicit path bodies.

`expectedFailures` is temporary, executable debt. Each listed contract is
run, must fail an assertion, and is reported as TODO. Crashes and setup
errors fail the suite. An unexpected pass fails too: remove that ID from
the set in the fixing PR. `CUBIST_GENERATION_STRICT=1` runs every contract
as an ordinary assertion, useful to expose the complete unresolved list.
TODO tests never count as evidence that an implementation phase is done.

G7 is a historical symptom, not a currently reproduced defect. FG1 must
inject a genuine failed parent projection and verify its dependents,
publication rollback, and progress. It must not repurpose a now-passing
capture example as evidence of an open bug. The later phases extend this
manifest with their full exit cases; FG0 does not claim those gates exist.
