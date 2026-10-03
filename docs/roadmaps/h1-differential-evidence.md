# H1 representation replay evidence

2026-10-02 removal: at the maintainer's decision, the apparatus this record
describes is gone. The pinned historical kernel (`tools/legacy-kernel.mjs`),
the representation option and the map τ (`web/h1-translation.mjs`), the
replay tool (`tools/h1-instruction-replay.mjs`) and
`tests/h1-differential.test.mjs` were removed, and the coverage tool's
`--representation` and `--normal-forms` options with them. The commands
below no longer run; what they showed is kept here as the evidence for
retiring Nat, W and pushouts.

2026-09-30 update: source programs now use declared Nat and W directly, with
H1 enabled by default. Primitive Nat/W are absent from the current kernel.
X1/X3 primitive instruction snapshots and the large primitive-W comparison
now use the exact pre-migration kernel at
`bfef585cfe09f4b94a658564dff505cd67855368`, built under
`build/reference-kernel`. They remain historical differential evidence.
Current source and corpus tests use the current producer; source W requires
explicit finite universe arguments, or a separate fixed-universe declaration
for higher universes. The former tier-1 primitive-W and mixed-W source probes
below no longer describe an available source API. Sum and pushout retain
their primitive APIs. See the [migration record](h1-program-types.md).

2026-10-01 update: pushouts are source-defined too (see the
[migration record](h1-program-types.md#source-defined-pushouts)), and sums
stay native by decision. The native pushout cases of X1, X3 and X6–X7 use
the pinned pre-migration kernel, as W's do. X8's source-level pushout call
no longer exists; its sum call remains. Replaying a native constructor whose
annotation is not its former now meets the retired-syntax refusal for
pushouts as for W.

Status: experimental implementation, 2026-09-30. The representation option
and archive replay are implemented. X2, X4 and X5 remain partially traced.
On 2026-10-02 the maintainer retired the differential fixtures as a release
gate (specification checklist item 6, and its 7.4): Nat, W and pushouts were
retired by source declaration rather than through τ, and sums stay native.
This record is historical evidence for those retirements. Its tests were
removed the same day, with the historical kernel. X2's remainder and
criterion are not pursued.

## The checked representation option

`CubicalProgram` accepts `representation: "declared"`. The CLI accepts the
equivalent option:

```sh
node cli/repl.mjs --representation=declared check archive/first-library/primes.cubist
```

Surface elaboration constructs the native derivation. A second instruction
kernel admits N, Plus, Tree and Push and checks each closed definition's
translated value at its translated public type. Its assumptions are the
source definition's abstracted dependency parameters; the image introduces
no extra logical assumption. The target kernel is available as
`program.translation.kernel`; inspection keeps the surface notation.
Evaluation directives also check the translated expression, expected value
and native computed value in that kernel.

Nat always maps. A sum, W type or pushout maps when its derivation reads
finite levels; its tier-1 occurrences remain native. A mixed call is rejected
by name and its source declaration is withdrawn. Definitions copied while
checking a failed image are rolled back. This creates no kernel equality
between native and declared sorts.

## Fixtures and outstanding coverage

| Cases | Evidence |
| --- | --- |
| X1, X3 | 202 successful judgements from the native instruction test, including 70 equalities, replay in the declared kernel. All 42 rejected requests involving native types and the unequal conversion query retain their verdict and error class. They cover Nat, W, pushout, Comp, HComp and Trans; additional source fixtures cover sums |
| X2 | Small Nat and sum normal-form comparisons, and a command that compares selected archive definitions, after administrative Beta/Eta. Literal alpha equality fails as described below; the whole archive value-normal-form comparison is not completed |
| X4, in part | The winding canonicity fixture and all three evaluation directives agree under both options. Whole-archive checking and re-derivation are manual observations recorded below, rather than a CI test |
| X5, in part | A small fixture tests the coverage report's revision, modified-tree flag, Node, CPU, platform, limits, times, steps and arena size. Whole-archive cost observations are manual evidence, including the source elaboration phase of the declared run |
| X6, X7 | Finite-universe calls for Nat, sum, W and pushout; tier-1 formers remain native |
| X8 | All three mixed-tier calls check natively and fail after translation; the verifier names each failed call |

`tests/h1-differential.test.mjs` checks these fixtures. The pinned historical native test emits
snapshots with `--fixtures FILE`; snapshots expand definition references
before their checkpoint disappears. `tools/h1-instruction-replay.mjs`
reconstructs the checked contexts and formulas, then independently derives
the typing and equality images. Refusal snapshots preserve the request and
independently check every premise in both kernels. Unfinished systems retain
their System/Tube/Overlap instruction chains, and entry failures retain the
entry's type. A single native request produces each rejection and its
snapshot, without evaluating its premises twice. Replay compares the actual
native error class with the recorded one and requires the declared class to
agree. Non-mismatch errors also retain the expected diagnostic, with explicit
diagnostics for changed declared APIs. Type mismatches compare their class:
fresh binder names during replay can change the detailed message.
In particular, the transport snapshot retains its input system
and wrong clause list; an ill-typed raw Trans term would not test that API
condition. Failed requests cover both changed constructor/eliminator APIs
and shared baseline operations involving native types: replacement, context
discharge, system compatibility, Glue, application, lifting, level misuse
and rewriting. The raw unadmitted definition used in the Lookup rejection
cannot be created in the target term checker, which refuses declared types;
it remains unavailable to Lookup. This workflow's rejection is preserved
without admitting the definition through a different API. Requests involving
only levels and universes are unchanged by τ and still run natively.

## X2 exposes a specification issue

The literal alpha-only criterion of specification 7.3 is false for the
homomorphic representation map, even for a sum selector. Its native normal
form has the shape

```text
λx. SumRec(M, left_case, right_case, x)
```

Mapping it gives `λx. Elim(Plus, M, [left_case, right_case]) x`. The declared
normalizer contracts this by function Eta to the unapplied eliminator.
The native recursor node has no corresponding unapplied form. Thus the
two displayed representations are convertible, but not alpha-equal. The
selected archive definitions `primes.add` and `primes.mul` exhibit the same
issue. The test preserves this counterexample explicitly.

A review must either allow administrative Beta/Eta in X2 or specify a
canonical representation map that removes the new redexes. The acceptance
criterion is left unchanged here. The comparison tool reports exact alpha
matches separately from matches requiring target normalization;
those counts do not silently satisfy the old criterion. An unrestricted
archive normal-form comparison was interrupted without a completed report;
it is not evidence of success.

The optional diagnostic comparison records `strictAlphaSatisfied` separately
from coverage success. Its `renormalizedImages` count uses the target's full
normalizer; it does not establish that only Beta/Eta was needed for every
counted definition. The examples above identify those reductions directly.
A concrete criterion to review is
`nf_declared(τ(nf_native(t)))` alpha-equal to `nf_declared(τ(t))`.
Adopting it would require a review of the map's preservation argument and
the whole-archive comparison; this draft does not amend specification 7.3.

## Commands and cost interpretation

```sh
node tools/instruction-coverage.mjs --limit-ms=60000 --report=build/h1-native-cost.json
node tools/instruction-coverage.mjs --limit-ms=60000 --representation=declared --report=build/h1-declared-cost.json
node tools/instruction-coverage.mjs --representation=declared --normal-forms --modules=primes --select='^primes__(add|mul)$' --report=build/h1-normal-form-sample.json
```

Run the first two sequentially for comparable observations. A declared
check's elapsed time includes both kernels; `checked.work` counts the
image kernel and `checked.sourceWork` counts its native elaboration phase.
Add both to compare total check work with native mode. Re-derivation counts
the image kernel alone. Arena size is that kernel's final interned arena;
peak RSS includes both kernels. No speed acceptance decision is implied.

### Clean PR-head cost, 2026-09-30

The two commands above completed sequentially in a clean checkout at
`3cb1d5f65ac49c979185b5c0a826ed0f497835a0`, with **modified tree: false**.
Both checked 365 modules, all 3,804 declarations and all 3,916 stored
definitions, with zero gaps and zero deadlines. This pins the corrected
PR implementation, rather than the earlier development tree at
`cc6b50fff248dd152cbb7051cf542dabb22c370d` (modified tree: true).
X4 and X5 remain partly traced: the whole-archive runs are manual evidence.
Before counting either release case, rerun these two commands sequentially
at the merged release head on a clean tree and record that revision.

| Observation | Native | Declared |
| --- | ---: | ---: |
| Archive checking, seconds | 38.4 | 56.4 |
| Re-derivation, seconds | 13.1 | 14.5 |
| Check instructions, both phases | 5,511,574 | 8,111,391 |
| Check steps, both phases | 198,727,662 | 407,266,541 |
| Re-derivation instructions | 2,006,960 | 2,357,050 |
| Re-derivation steps | 133,990,469 | 184,485,348 |
| Final target arena, nodes | 5,823,480 | 6,329,830 |
| Final target arena reserved capacity, MiB | 481 | 481 |
| Process peak RSS, MiB | 2,280 | 2,548 |

Machine: Apple M3 Pro, 12 logical CPUs, 36 GiB RAM; darwin arm64;
Node v24.13.0. Both runs used a 60,000 ms stored-definition re-derivation limit,
10,000,000 kernel steps, driver fuel 20,000, long computation 64, guide
fuel 400, guide head steps 4,000, oracle steps 20,000 and Glue steps
200,000. Archive elaboration uses the checker's ordinary operation budgets;
the command's time limit applies to re-derivation and optional normal-form
comparisons. RSS is a process observation and can vary independently of the
final arena; these observations do not establish a memory improvement.

Earlier runs under the unchanged default 5,000 ms limit completed in both
modes. A subsequent native repeat had one deadline on
`f4_galois_group__f4_symmetry_add`; its focused recheck under that same limit
passed in about 0.2 seconds. The complete sequential cost runs above use the
larger explicit limit and retain that distinction. Raw reports are generated
in `build/`; reproduce them with the commands above.
