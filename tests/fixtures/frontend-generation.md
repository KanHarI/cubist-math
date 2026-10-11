# Frontend generation comparison manifest

These are active contracts integrated from [#205](https://github.com/KanHarI/cubist-math/pull/205).
Every case runs as ordinary assertions against this checkout's fresh WASM build.
`00d4ecce` is the historical revision where the inventory's defects were
observed, not a runtime pin or a compatibility promise for future compiler
revisions. RC0 retired the known-defect records, the expected-failure
lifecycle and its tests.
Each exported case in `frontend-generation.mjs` has its own ID, finding group,
source, responsible phase and intended contract.
[frontend-generation.test.mjs](../frontend-generation.test.mjs) implements
the comparison, including independent equations rather than generated-output
snapshots.

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
families, and its Hom and Iso clients must each be refused with a focused
E817. G4 covers flat and nested matches with
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
that operation and context. `G12-range` checks
that refusal's nonempty range over the original `iter` reference as a
separate FG5 case, independent of the FG2/FG4 value-call fix. The range may cover the reference, the call or a wider
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
declarations and the module's inclusion in that suite. H2–H5 map to the named
theory-resolution/hygiene regressions. Further controls
exercise inherited, bare/partial helpers with free fields under colliding
law binders, initial-model recursion and explicit path bodies.

The [design decision on #205](https://github.com/KanHarI/cubist-math/pull/205#issuecomment-6096591882)
replaced the catch-any-assertion handler. `frontend-generation-contracts.mjs`
is the contract layer. It collects compiler
and lint results once, as plain data. Facts project that evidence without
judging it: diagnostic name/code pairs, primary cause payloads, client
verdicts, lint advice and its span, output absence, refusal reasons, and the
links and refusal spans at their written sites. Requirements judge the facts
as tables of named conditions. Type mismatch evidence retains
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
so a requirement cannot stop applying unnoticed. Each witness also states, as
data, the minimum its case must keep: clients, refused-client and declaration
diagnostics, absent outputs and observation sites. These include
constructor availability, output absence, G2's public types and lowering
endpoints, G4's distinct branch results, G8's endpoints and every
second recursive step. A weaker fixture is rejected before any program is
checked. A diagnostic cause that its code does not always carry must be
required by a witness, and the audit's cause counterexamples come from there
rather than from the expectation under test.
Source scopes, conflicts and rewrite targets must occur exactly once; repeated
inner references require an explicit occurrence. Observers use resolved spans.

`clients` lists accepted declarations. `refusedClients` maps each refused client
to `{code, cause?}`, so E343 name-availability probes and E606 equations can share
a case. For example, `leaked_c` requires
`{code: "E343", cause: {untranslated: "c"}}`; `wrong` requires `{code: "E606"}`.
Their expectations compose with declaration diagnostics and are matched as one
complete multiset, independently of expectation order, by
[`frontend-generation-diagnostics.mjs`](../frontend-generation-diagnostics.mjs).
Desired expectations never come from the historical record. G1 requires
`{duplicate: "N"}` and permits recognized frontend and kernel refusal forms;
this is the only cause that may omit `code`. G3's Hom and Iso clients each
require E817 with `{operation: "op", argument: "p", law: "l"}`. These are
semantic roles: swapped roles, reversed or denied dependencies, and unrelated
messages using the same vocabulary fail. Unrecognized wording does not match
a cause. Both cases use the shared diagnostic requirement, without separate
keyword checks. G6 matches the
exact dependency target, G10 the helper/field pair, G12-range the recursive
operation/context, and G8 the ordered found/expected endpoints. Source ranges
remain independent requirements. Missing mandatory causes are fixture errors.
An expectation may state only `name`, `code` and `cause`, the fields the
matcher compares; declaration diagnostics also carry their source anchors.
`absentOutputs` and
`absentOutputFamilies` describe only the output list; they make no claim about
name resolution. Use real clients to observe that boundary.

Prerequisites are ordinary assertions: metadata must be valid, and G5's
original interface must check before any rewrite. Everything else is an
observation. Missing clients are represented explicitly, so a misspelled client
cannot pass as refused. The whole diagnostic name/code set is compared,
including dependent failures; primary failure payloads distinguish different
causes with the same code. Every link overlapping a written occurrence is
retained with its label, target and span. Repeated identical links at one
occurrence are equivalent.

Every case asserts each requirement of its observation; an unmet requirement
fails with the case's facts. Active semantic mismatches remain assertions for
the FG6 mutation gate.

The [harness](../frontend-generation-harness.test.mjs) checks that missing
imports, misspelled clients, unrelated type errors, invalid metadata,
changed/extra diagnostics and missing or wrong navigation fail normally. Each
mistake must leave the contract unmet and change the case's own observation.
It also checks the accepted-client helper.

Each contract requirement in
[frontend-generation-contracts.mjs](../frontend-generation-contracts.mjs) is a
table of named conditions. Each condition carries the plausible wrong results
that must violate it, and each requirement lists the valid variations it
permits; the tables, not this manifest, are the list. Diagnostic
counterexamples come from the matcher's field table, and a fixture that states
a field without counterexamples fails validation. The
[audit](../frontend-generation-audit.test.mjs) gives every case an accepted
observation. That observation and each permitted variation must meet every
requirement, each counterexample must violate its condition, and some
counterexample must violate each condition alone. The requirement map states
the conditions independently. A mutation sweep changes each comparison in the
facts that conditions read, the conditions and the diagnostic field matchers,
and each change must alter some verdict. Accepted observations come
from [supported sources](frontend-generation-supported.mjs), which avoid the
original defect, or from observer results layered over real checked outputs.
The G12 supported source unrolls two steps; it demonstrates these finite
observations, not arbitrary recursive correctness.

The diagnostic audit also states misleading messages independently of the
decoder and mutation generators. Exercising comparisons cannot establish that
their predicate expresses the intended meaning; G1's unrelated "already"
messages and G3's swapped or denied dependencies guard that boundary.

The audit checks further permitted
alternatives (attached causes, a span over the whole call) and ID-to-finding
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

## Verification

Run the active cases, harness, acceptance audit and provenance consumers
together:

```sh
npm test -- tests/frontend-generation.test.mjs tests/frontend-generation-harness.test.mjs tests/frontend-generation-audit.test.mjs tests/frontend-provenance.test.mjs
npm run test:generation:mutations
```

The mutation gate preserves the original required compiler mutations and adds
recursive lexical shadowing. These are different forms of evidence; totals do
not replace a named witness for each obligation. Commit-specific results belong
in the PR record.

G7 remains a historical symptom backed by the downstream publication and
failed-dependency injection tests. RC1/RC2 may migrate these active contracts
through the existing Cubist runner; this integration adds no test language.
