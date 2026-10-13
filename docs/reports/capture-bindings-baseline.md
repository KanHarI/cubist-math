# Capture and bindings: CB0 baseline

CB0 adds witnesses, observation safeguards and measurements on the production
compiler at `f0417ee0ee5f824f030069be0e6d1666696de0d1`. It does not implement
binding identities or contextual execution. Those remain CB1–CB7 in the
[architecture](../roadmaps/capture-bindings.md).

## Adopted work and retained expectations

The [pinned comparison](capture-bindings-pr-comparison.md#stack-and-disposition) records
the ten reviewed PR heads. CB0 selectively adopts #224's 36 Cubist fixtures
and observer from `1fdc68a5e7da198f2b538dfbaa95e4bad40c97ca`, and #223's bounded
generator, shrinker and mutation runner from
`49499aa1c56c1b345eb0021468123cec377fb4b8`. No later production implementation
is merged. The old JavaScript fixture module and broad assertion-catching
TODO runner are removed.

Desired behavior stays in independently written clients and source comments.
A known-defect record is a separate observation of the current compiler.
Only an exact observation can mark a test TODO; new symptoms, missing outputs,
unexpected fixes and import/infrastructure failures fail normally. Strict
mode (`CUBIST_GENERATION_STRICT=1`) requires the desired behavior without
TODOs. There is no automatic expectation-update command.

The [case manifest](../../tests/fixtures/frontend-generation.md) explains the
36 inherited fixtures: 18 pass and 18 remain known defects. The old suite
represented them with 12 coarse TODOs. Eight new known-defect witnesses cover
bare recursive references, family domains, inherited pattern capture and
operand-selection capture. Eight composed preservation cases retain exact
known observations; their eight noncolliding controls actively check imports,
inheritance, renaming, helper depth, grouped/dependent parameters, caller
notation, initial/free clients and safe lint rewrites. Recursive/path
composition is deferred to CB2/CB3; its individual G4/G8/G12 witnesses remain.

The [binding cases](../../tests/fixtures/capture-bindings.mjs) include all
three #219 review reproductions, with absent/same-module/imported recursive
globals, plus the pre-existing bare-reference and family-domain defects.
They also cover local/call-produced opening effects, file-level precedence
and receiver reactivation, consumer-specific rule registration and required
activation failure. Imported ranges are checked against their source module
before any TODO classification. Rule-registration clients run locally and
across imports, and check the registered declaration identity.

At #219's pinned head, separate probes reproduce the wrapper's accidental
global acceptance, later-helper replacement of a header parameter, and an
inherited error range outside its caller source. The bare recursive-reference
and family-domain failures also occur on the replacement base. The valid
failed-activation probe needs a carrier-bearing theory; a theory without a
carrier fails earlier with E818 and does not test activation.

## Contextual execution remains pending

Seven [source scenarios](../../tests/fixtures/contextual-sessions.mjs) check
nested functions and inductions, before/after let shadowing, a usable prefix
of a failing declaration, multiple branch instances, discarded wildcard
coherence and proof goals. Their independent source clients run now. Their
query scripts and six lifetime/resource requirements are 13 explicit TODOs,
not mocked sessions or successful module-import substitutes. CB1/CB6 must
replace those TODOs with execution through the real scope-point backend.

## Mutation evidence

All four adopted mutations apply exactly once, have a passing unmodified
control, and are killed by assertions in isolated copies with unchanged
checker limits. Syntax errors, missing modules, timeouts and patches that
do not apply are invalid runs, not killed mutants.

| Mutation | Distinguishing check |
| --- | --- |
| Reference lowered by spelling | Retained-reference lowering in `references.test.mjs` |
| Captured file-level selection removed | Composed preservation control, seed 3 |
| Reservation conflict ignored | Original definition survives a later inductive collision |
| Failed publication committed | Injected parent projection failure and descendant rollback |

The other #223 patches are deferred, not counted as kills or silently retired:
label/provenance/lint mutations belong to CB5 (G5/G9 and generated inspection);
telescope mutation to CB1/CB2 (G11); universe mutation to CB4 (G2); evidence,
fallback eligibility and explicit-path-head mutations to CB3 (G4/G8 and
explicit-path controls). The historical recursive-update, recursive-source
guard and hlevel-globals survivors still need reachability/retirement evidence
at their migrated contracts. Each later package must replace its obsolete
patch with a distinguishing semantic witness before claiming retirement.

## Validation and costs

On 2026-10-13, the full suite passes: 919 tests, 872 pass, 47 TODOs, zero
failures. This includes all 3,857 canonical corpus declarations and formatting
of the new Cubist fixtures. Native tests passed on the unchanged runtime
baseline. TODOs are 18 inherited cases, eight binding cases, eight composed
capture cases and 13 contextual-execution requirements.

The cost report records three repeats of algebra, inheritance and fold
workloads, each with reference collection off/on in a fresh process, WASM
module and kernel session. It records the build stamp, frontend/source
digests, defaults, deterministic declaration fuel, observed kernel work,
published generated names, checked interfaces up to alpha-renaming, assumptions,
retained reference counts, arena use, process RSS and heap memory. Scope-point
and artifact-snapshot collection are explicitly unavailable at CB0. Generated
names are identified against authored declaration names; these are published
outputs, not the later retained-artifact API.

Across all modes/repeats, each workload has the same checked interface digest,
generated-name inventory and empty assumption set. Algebra has 323 checked
declarations and 224 generated names; inheritance has 145 and 73; fold has
328 and 227. Six kernel budget retries in the algebra/fold workloads succeed
under the existing growing-budget policy; there are no deadline failures.

Timing and memory are measurements rather than release thresholds. RSS
includes process startup; heap samples follow explicit GC, and arena samples
are taken after declarations. Kernel steps are cache-sensitive, even when
these fresh-session repetitions agree. CB1/CB6 will add retained scope size
and separate prefix/history/query latency. The release budget must be justified
from comparable evidence after migration.

Run the evidence with:

```sh
npm test
node tools/frontend-generation-mutations.mjs build/frontend-generation-mutations.json
node tools/frontend-generation-metrics.mjs build/frontend-generation-metrics.json 3
```
