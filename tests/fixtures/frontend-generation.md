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
G2's clients fix the public Hom/Iso types, composition computation and the
fixed-domain operation's preservation field at U0 and U1. A U0 model's Hom
must live in U1, and stating it in U0 must be refused as universe lowering.
G3 preserves the base theory while withholding both unsupported artifact
families. G4 covers flat and nested matches with
distinct results, every written branch, and a refused constant-result equation.
G5 uses positional operation calls, identity and a generated model/fold to
test the lint rewrite for both single and grouped operation binders. The case
records each warning's code, declaration and message and verifies its location
within the rewrite target before applying the associated replacement. Changed
or partial advice is an unrecognized observation until its edit is reviewed.
Named operation calls are not currently supported. Passing controls require
W705 and W706 for ordinary safe unused binders and check their arrow-form
rewrites. G11 requires opposite outcomes for intended and captured equations,
including helper chains, grouped/dependent binders, inheritance and generated
clients. G12 checks `twice` computation directly, through
inheritance, and through an initial model, with zero, one and two recursive
steps and a refused base-only result. The second step distinguishes using the
recursive result from substituting the base value in every successor.
G12-shadowed pairs intended/local and captured/field equations; a passing
field-type control keeps a local recursive name free of E845. G12 also keeps a
passing control that refuses unfolding `iter` in a law's type with E845, for
that operation and context. `G12-range` tracks
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
collects compiler and lint results once as evidence. Facts and requirements
are pure functions of that evidence: diagnostic name/code pairs, primary cause
payloads, client verdicts, lint advice, output absence and source observations,
judged by independently stated requirements. Type mismatch evidence retains
found/expected types; generation evidence retains the obligation and required
evidence; capture and recursion evidence retain the responsible references.
Terminal line/column text and remediation prose are omitted from those
extracted payloads. Other primary failures retain their reason without the
terminal location. E340 cascades retain their declaration/code entries and
dependency targets; attached cause wording does not replace the independently
retained primary cause.
Every contract consumes its supplied case; group labels never select another
fixture's data. The derived `gaps` lookup shares those same case objects by ID
for the downstream FG5 provenance/browser consumers; cases share no nested
state. Accepted clients must be assumption-free: a verified client with axioms
is observed as `assumes`, never `checked`.

The independent [requirement map](frontend-generation-requirements.mjs) names
behavioral obligations and the cases that witness them. Removing a case and its
manifest row together still fails if an obligation loses its witness. Each
obligation's `checks` names the contract requirements its witnesses must keep,
so a requirement cannot stop applying unnoticed. Minimum constructor-availability,
output-absence, public-type and equation requirements are checked
independently too, including the second recursive step in all three contexts.
Source scopes, conflicts and rewrite targets must occur exactly once; repeated
inner references require an explicit occurrence. Observers use resolved spans.

`clients` lists accepted declarations. `refusedClients` maps each refused client
to `{code, cause?}`, so E343 name-availability probes and E606 equations can share
a case. For example, `leaked_c` requires
`{code: "E343", cause: {untranslated: "c"}}`; `wrong` requires `{code: "E606"}`.
Their expectations compose with declaration diagnostics and are matched as one
complete multiset, independently of expectation order, by
[`frontend-generation-diagnostics.mjs`](../frontend-generation-diagnostics.mjs).
The same decoder supplies historical cause observations and active matching;
desired expectations never come from the historical record. G6 matches the
exact dependency target, G10 the helper/field pair, G12-range the recursive
operation/context, and G8 the ordered found/expected endpoints. Source ranges
remain independent requirements. Missing mandatory causes are fixture errors.
`absentOutputs` and
`absentOutputFamilies` describe only the output list; they make no claim about
name resolution. Use real clients to observe that boundary.

Prerequisites are ordinary assertions: metadata must be valid, and G5's
original interface must check before any rewrite. Everything else is an
observation. Missing clients are represented explicitly, so a misspelled client
cannot match a recorded defect. The whole diagnostic name/code set is compared,
including dependent failures; primary failure payloads distinguish different
causes with the same code. Labels and missing/wrong targets are retained at
every written occurrence. Repeated identical links at one occurrence are
equivalent.

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
wrong navigation, strict mode, independent activation and the accepted-client
helper.

Each contract requirement states its accepted behavior together with the
plausible wrong results that must violate it: refused, missing or
assumption-dependent clients; accepted refusals; leaked outputs; missing,
duplicated, recoded or recaused diagnostics; changed, partial or misplaced
advice; empty, off-site or out-of-region spans; relabelled, retargeted or
missing links. The [audit](../frontend-generation-audit.test.mjs) gives every
case an accepted observation and applies each counterexample to it. Each must
violate its requirement and fail with `knownDefect` removed and in strict mode,
so these controls survive activation; a mismatch with historical debt alone is
insufficient. Accepted observations come from
[supported sources](frontend-generation-supported.mjs), which avoid the original
defect, or from observer results layered over real checked outputs. The G12
supported source unrolls two steps; it demonstrates these finite observations,
not arbitrary recursive correctness.

The audit also recognizes each recorded debt and rejects it after any one
primary cause or dependency target changes. It checks permitted alternatives
(attached causes, wider spans, other refusal wordings) and ID-to-finding
ownership. Semantic mutants replace matches/recursion by constants, ignore a
recursive result, or capture a local recursive name; each has independently
stated client verdicts and E606 failures. Publication controls replay real
constructor clients and real model/fold outputs alongside a duplicate refusal;
no constructor output is fabricated. Ambiguous anchors fail. See the
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
| `G2` | G2 | Fixed argument domains; Hom/Iso, preservation, level and computation at U0/U1 |
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

[#216](https://github.com/KanHarI/cubist-math/pull/216) supplies the FG0–FG6
contracts. This harness is evidence at FG0, not an implementation of those fixes.
The FG1–FG6 implementation stack inherited by
[#224](https://github.com/KanHarI/cubist-math/pull/224) activates fixed cases.
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
