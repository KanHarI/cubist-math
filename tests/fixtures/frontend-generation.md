# Frontend generation comparison manifest

These are active contracts integrated from [#205](https://github.com/KanHarI/cubist-math/pull/205).
Every case runs as ordinary assertions against this checkout's fresh WASM build.
The historical inventory revision `00d4ecce` is provenance, not a runtime pin.
Known-defect records, TODO/strict-mode classification, diagnostic fingerprints
and tests specific to expected-failure activation have been retired.

The [roadmap](../../docs/roadmaps/frontend-generation.md) is the behavioral
authority. The independent [requirement map](frontend-generation-requirements.mjs)
names obligations, executable witnesses and distinguishing incorrect behavior.
Deleting a fixture and its table row together cannot erase an obligation.
The [acceptance audit](../../docs/reports/frontend-generation-contract-audit.md)
explains which controls use real source and which inject observer results.

[frontend-generation.test.mjs](../frontend-generation.test.mjs) checks every
case, including accepted and refused client equations without assumptions.
[frontend-generation-contracts.mjs](../frontend-generation-contracts.mjs)
combines client verdicts, output absence, diagnostics and source observations.
Refusal must not publish a constructor or generated model/fold member from the
refused group, or replace the earlier binding. Unsupported Hom/Iso generation
must preserve the usable base theory. Source scopes, conflicts and rewrite
targets resolve once; repeated inner tokens require an explicit occurrence.

`clients` lists accepted declarations; `refusedClients` maps each refused client
to its diagnostic code. Client diagnostics compose with the declaration refusal
as one complete expected set. `absentOutputs` and `absentOutputFamilies` describe
only reported outputs. Constructor availability is tested through real clients
(`c`, `N.one`, `N.mul`) that must receive E343. The reverse-order case retains
its original constructor; `N.model`, `N.fold_map` and `N.fold` have output checks.

G4 has distinct nil/off/yes results (nil/cons for the flat case). G12 checks
zero, one and two recursive steps directly, through inheritance and through an
initial model. The second step distinguishes using the recursive result from
substituting the base value in every successor. Both also refuse a plausible incorrect equation. G12-shadowed
accepts the local-parameter equation and refuses the captured-field equation;
a passing field-type control ensures that local iter receives no E845.
G11 retains intended/captured equations in all four contexts. G2 checks
Hom/Iso and computation at U0/U1. G5 preserves positional calls and named
generated-constructor clients, with both ordinary safe W705/W706 controls.
G6 permits an attached parent cause while requiring the actual dependency.
G8 checks endpoint roles and accepts appropriate written-body spans; the
additional downstream control pins its exact token and zero coherence search.
G9 checks every public label and definition target. G10 and G12-range require
nonempty origins covering the responsible binder/call or reference.

Preserved downstream controls include explicit-path negative cases, ordinary
and capture-sensitive bare/partial helpers, recursive predecessors after a
nested match, and the FG5 browser/CLI provenance consumers. They look up source
through the `gaps` view of the same case records. Group prefixes and bracketed
case IDs remain stable for mutation selection and focused runs.

H1 maps to the Constant/K/idem_at and Named/named_fold cases in
[initial_models.cubist](../../cubist-tests/initial_models.cubist); H2–H5 map to
the named theory-resolution/hygiene regressions. The source-spelling coverage
check remains pending RC0 cleanup; the actual regressions still run normally.

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


## Lifecycle and verification

Run the active cases, acceptance audit and provenance consumers together:

```sh
npm test -- tests/frontend-generation.test.mjs tests/frontend-generation-audit.test.mjs tests/frontend-provenance.test.mjs
npm run test:generation:mutations
```

The mutation gate preserves the original required compiler mutations and adds
recursive lexical shadowing. The audit separately checks injected publication
leaks, ambiguous anchors, missing requirements, and well-typed semantic source
mutants. These are different forms of evidence; totals do not replace a named
witness for each obligation. Commit-specific results belong in the PR record.

G7 remains a historical symptom backed by the downstream publication and
failed-dependency injection tests. RC1/RC2 may migrate these active contracts
through the existing Cubist runner; this integration adds no test language.
