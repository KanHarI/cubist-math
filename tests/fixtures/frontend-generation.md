# Frontend generation comparison manifest

`00d4ecce` is the historical revision where the inventory's defects were
observed, not a runtime pin or a compatibility promise for future compiler
revisions. The suite always checks this checkout with its fresh WASM build.
Each exported case in `frontend-generation.mjs` has its own ID, finding group,
source, responsible phase, intended contract and explicit known-defect record.
[frontend-generation.test.mjs](../frontend-generation.test.mjs) implements
the comparison, including independent equations rather than generated-output
snapshots. Run it with `npm test -- tests/frontend-generation.test.mjs`.

All accepted clients must be verified without assumptions. G1 covers both
orders of definition/inductive collisions, definition/initial-model
collisions, and same-kind duplicates, preserving the first binding and its
clients. Collision cases require E343 from clients of each refused constructor
(`c`, `N.one`, `N.mul`), while the reverse-order case preserves its original
constructor. Separate output checks forbid `N.model`, `N.fold_map` and `N.fold`.
Constructors never appear in the output list, even when available to clients.
G2's clients fix the public Hom/Iso types and composition
computation at U0 and U1. G3 preserves the base theory while withholding
both unsupported artifact families. G4 covers flat and nested matches with
distinct results, every written branch, and a refused constant-result equation.
G5 uses positional operation calls, identity and a generated model/fold to
test the lint rewrite for both single and grouped operation binders. The case
records each warning's code, declaration and message and verifies its location
within the rewrite target before applying the associated replacement. Changed
or partial advice is an unrecognized observation until its edit is reviewed.
Named operation calls are not currently supported. Passing controls require
W705 and W706 for ordinary safe unused binders and check their arrow-form
rewrites.
G11 requires opposite outcomes for intended and captured
equations, including helper chains, grouped/dependent binders, inheritance
and generated clients. G12 checks `twice` computation directly, through
inheritance, and through an initial model, with zero, one and two recursive
steps and a refused base-only result. The second step distinguishes using the
recursive result from substituting the base value in every successor.
G12-shadowed pairs intended/local
and captured/field equations; a passing field-type control keeps a local
recursive name free of E845. G12 also keeps a passing
E845 refusal control for recursive unfolding in a law. `G12-range` tracks
that refusal's nonempty range over the original `iter` reference as a
separate FG5 expected failure, so it can be activated independently of the
FG2/FG4 value-call fix. The range may cover the reference, the call or a wider
part of the written law. G6 requires the child's E340 to identify its failed
parent. The parent retains the original cause; the child's message may also
attach it for inspection.

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

The [design decision on #205](https://github.com/KanHarI/cubist-math/pull/205#issuecomment-6096591882)
replaces the catch-any-assertion handler. `frontend-generation-contracts.mjs`
collects diagnostic name/code pairs, primary cause payloads, client verdicts,
lint advice, output absence and source observations, and evaluates independent
desired requirements. Type mismatch evidence retains found/expected types;
generation evidence retains the obligation and required evidence; capture and
recursion evidence retain the responsible references. Terminal line/column text
and remediation prose are omitted from those extracted payloads. Other primary
failures retain their reason without the terminal location. E340 cascades retain
their declaration/code entries and dependency targets; attached cause wording
does not replace the independently retained primary cause.
Every contract consumes its supplied case; group labels never select another
fixture's data. The derived `gaps` lookup shares those same case objects by ID
for the downstream FG5 provenance/browser consumers. Accepted clients must be
assumption-free.

The independent [requirement map](frontend-generation-requirements.mjs) names
behavioral obligations and the cases that witness them. Removing a case and its
manifest row together still fails if an obligation loses its witness. Minimum
constructor-availability, output-absence and equation requirements are checked
independently too, including the second recursive step in all three contexts.
Source scopes, conflicts and rewrite targets must occur exactly once; repeated
inner references require an explicit occurrence. Observers use resolved spans.

`clients` lists accepted declarations. `refusedClients` maps each refused client
to its own diagnostic code, so E343 name-availability probes and E606 equations
can share a case. Their expected diagnostics compose with the declaration's own
refusal and are compared as one complete set. `absentOutputs` and
`absentOutputFamilies` describe only the output list; they make no claim about
name resolution. Use real clients to observe that boundary.

Prerequisites are ordinary assertions: metadata must be valid, unaffected
clients must check, and G5's original interface must check before any rewrite.
Missing clients are represented explicitly in observations, so a misspelled
client cannot match a recorded defect. The whole diagnostic name/code set is
compared, including dependent failures; primary failure payloads distinguish
different causes with the same code. Labels and missing/wrong targets are
retained at every written occurrence. Repeated identical links at one occurrence are equivalent.

Only an exact match for the case's `knownDefect` facts is reported as TODO.
No exception or assertion message is classified as a defect. A different
observation fails normally and requires investigation; never regenerate these
records just to accept a new failure. A desired outcome with an outstanding
record is an unexpected pass. Remove only that case's entry from `knownDefects`
in the fixing PR to activate it. Sibling cases retain their own status.
`CUBIST_GENERATION_STRICT=1` checks all desired requirements as ordinary
assertions, allowing defect-free controls to pass before activation. TODOs
remain implementation debt and never count as completion.

The harness's own regressions exercise missing imports, misspelled clients,
unrelated type errors, invalid metadata, changed/extra diagnostics, missing or
wrong navigation, strict mode and independent activation. Supported controls
prove that flat matches, renamed navigation and all three G12 contexts can pass.
The G12 supported control unrolls two steps to avoid the old recursive-call defect;
it demonstrates these finite observations, not arbitrary recursive correctness.

[frontend-generation-audit.test.mjs](../frontend-generation-audit.test.mjs)
extends these controls to every case: the known defect is recognized, a different
primary cause fails, and a supported source or explicitly injected valid outcome
satisfies the desired requirements. It checks permitted diagnostic alternatives,
swapped mismatch endpoints, changed advice and ID-to-finding ownership.
Semantic mutants also replace matches/recursion by constants, ignore a recursive
result, or capture a local recursive name. Each recursive mutant has independently
stated client verdicts and E606 failures. Publication controls use real constructor
clients and real model/fold outputs before injecting their observations alongside
a duplicate refusal. No constructor output is fabricated. Ambiguous anchors fail. See the
[audit](../../docs/reports/frontend-generation-contract-audit.md) for each case's
scope and the distinction between observer controls and compiler integration.

## Coverage by executable case

Group prefixes such as `G2:` and `G11:` remain in test names for the FG6
mutation selectors. The bracketed case ID selects an individual variant with
`--test-name-pattern`, for example `\[G12-inherited\]`.

| Case ID | Finding | Behavior and context |
| --- | --- | --- |
| `G1` | G1 | Definition followed by inductive; preserve the first binding |
| `G1-initial` | G1 | Definition followed by initial model |
| `G1-reverse` | G1 | Inductive followed by definition, including the original constructor |
| `G1-same-kind` | G1 | Definition followed by definition |
| `G2` | G2 | Fixed argument domains; Hom/Iso and computation at U0/U1 |
| `G3` | G3 | Law-dependent transport; usable base and no partial families |
| `G4` | G4 | Nested derived match; distinct nil/off/yes results and refused constant result |
| `G4-flat` | G4 | Flat derived match; distinct nil/cons results and refused constant result |
| `G5` | G5 | Grouped operation binder; supported call, Hom and initial-model clients |
| `G5-single` | G5 | Single operation binder with the same interface checks |
| `G6` | G6 | Parent cause, child dependency and unrelated recovery |
| `G8` | G8 | Wildcard diagnostic endpoints and original body range |
| `G9` | G9 | Freshened binder and every use: public labels and navigation |
| `G10` | G10 | Capture refusal over the written binder or helper call |
| `G11` | G11 | Direct intended and captured equations |
| `G11-grouped-dependent` | G11 | Helper chain with grouped/dependent parameters |
| `G11-inherited` | G11 | Inherited helper chain |
| `G11-initial` | G11 | Initial-model helper client |
| `G12` | G12 | Direct `twice` zero/one/two-step computations and refused base-only result |
| `G12-inherited` | G12 | Inherited `twice` zero/one/two-step computations and refused base-only result |
| `G12-initial` | G12 | Initial-model `twice` zero/one/two-step computations and refused base-only result |
| `G12-shadowed` | G12 | Local recursive-name shadowing; intended/captured equations |
| `G12-range` | G12 | Legitimate type-unfolding refusal over the original reference |

## Downstream lifecycle

[#204](https://github.com/KanHarI/cubist-math/pull/204) supplies the FG0–FG6
contracts. This harness is evidence at FG0, not an implementation of those fixes.
The FG1–FG6 implementation stack inherited by
[#212](https://github.com/KanHarI/cubist-math/pull/212) activates fixed cases.
Its RC0 cleanup may remove the known-defect records, TODO/strict-mode handling,
and tests specific to that temporary lifecycle once all cases are active.
Keep the desired observations, stable case IDs and group selectors. Active
semantic mismatches must still produce assertions for the mutation gate.
RC1/RC2 can migrate the clients and observations to Cubist's existing runner;
this helper introduces no pragma syntax, module loader or production diagnostic
representation. Historical provenance remains documentation.

G7 is a historical symptom, not a currently reproduced defect. FG1 must
inject a genuine failed parent projection and verify its dependents,
publication rollback, and progress. It must not repurpose a now-passing
capture example as evidence of an open bug. The later phases extend this
manifest with their full exit cases; FG0 does not claim those gates exist.
