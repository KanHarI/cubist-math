# H1 representation replay evidence

Status: experimental implementation, 2026-09-30. The representation option
and archive replay are implemented. X2 remains partially covered;
this record does not mark the differential release gate discharged.

## The checked representation option

`CubicalProgram` accepts `representation: "declared"` with
`experimental: ["h1"]`. The CLI accepts the equivalent options:

```sh
node cli/repl.mjs --experimental=h1 --representation=declared check archive/first-library/primes.cubist
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
| X1, X3 | 209 successful judgements from the native instruction test, including 74 equalities, replay in the declared kernel. All 42 rejected requests involving native types and the unequal conversion query retain their verdict. They cover Nat, W, pushout, Comp, HComp and Trans; additional source fixtures cover sums |
| X2 | Small Nat and sum normal-form comparisons, and a command that compares selected archive definitions, after administrative Beta/Eta. Literal alpha equality fails as described below; the whole archive value-normal-form comparison is not completed |
| X4 | All 3,804 archive declarations check, zero gaps; all 3,916 stored definitions re-derive. The winding canonicity fixture and all three evaluation directives agree under both options |
| X5 | Coverage reports record revision, modified-tree flag, Node, CPU, platform, limits, times, steps and arena size, including the source elaboration phase of the declared run |
| X6, X7 | Finite-universe calls for Nat, sum, W and pushout; tier-1 formers remain native |
| X8 | All three mixed-tier calls check natively and fail after translation; the verifier names each failed call |

`tests/h1-differential.test.mjs` checks these fixtures. The native test emits
snapshots with `--fixtures FILE`; snapshots expand definition references
before their checkpoint disappears. `tools/h1-instruction-replay.mjs`
reconstructs the checked contexts and formulas, then independently derives
the typing and equality images. Refusal snapshots preserve the request and
independently check every premise in both kernels. Unfinished systems retain
their System/Tube/Overlap instruction chains, and entry failures retain the
entry's type. In particular, the transport snapshot retains its input system
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

### Recorded cost, 2026-09-30

The two commands above completed sequentially at base revision
`cc6b50fff248dd152cbb7051cf542dabb22c370d`, with **modified tree: true**.
This is development evidence, not the pinned release/CI record. Both checked
365 modules, all 3,804 declarations and all 3,916 stored definitions, with
zero gaps and zero deadlines.

| Observation | Native | Declared |
| --- | ---: | ---: |
| Archive checking, seconds | 34.2 | 53.5 |
| Re-derivation, seconds | 11.7 | 14.0 |
| Check instructions, both phases | 5,511,574 | 8,111,391 |
| Check steps, both phases | 198,727,662 | 407,266,541 |
| Re-derivation instructions | 2,006,960 | 2,357,050 |
| Re-derivation steps | 133,990,469 | 184,485,348 |
| Final target arena, nodes | 5,823,480 | 6,329,830 |
| Final target arena, MiB | 481 | 481 |
| Process peak RSS, MiB | 2,474 | 2,462 |

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
