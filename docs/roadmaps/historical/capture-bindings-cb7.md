# CB7: retirement and release

Archived on 2026-10-17: this implementation sequence is complete. Continuing
contracts are indexed under [frontend](../frontend/README.md); the
[work plan](../work-plan.md) owns any subsequent work.

Status: complete and merged in #240, following CB6 #239; Claude round 2 was
clean at `32bda0ee`. The separate cleanup is merged in #241. Reconciled on
2026-10-17 against main `e729c2d5`; the release measurements below retain
their original revisions and resource exceptions. The subsequent
[RC record](refactoring-and-testing.md#verification-record) owns the final
1,463-test and 16-mutation evidence.

## Retired paths

The old `reference` node and `elaborationSyntax` adapter are removed. Their last
producer was an elaborator-local projection call with an already known binding
ID. It now uses the same private key directly at that elaboration boundary;
retained generators still use `bindingReference` and the checked binding adapter.
Structural receiver construction and source spelling remain independent.

The ordinary-module pilot exports `resolveBindingModule` and `lowerBindingModule`
had no production callers. Tests now construct fixture artifacts with the syntax
resolver and enter them through production `bindingDeclaration` admission,
preserving ordered visibility, duplicate ownership, cloned telescopes and failed
declaration controls. There is no second production module resolver.

The old `recursiveCall` syntax has no producer. Its elaboration, traversal and
display cases are removed. Retained recursive references use exact ordinary
calls and the shared `withRecursion` permission transition. The original structural
restrictions, dependent/generalized arguments and query isolation remain checked.

E801/E860/E869/E871 and the E866 expansion workaround have no live implementation;
their catalogue rows stay retired and their codes are not reused. Historical
source migration remains isolated in `legacy-syntax.mjs` and
`verify-proof-migration.mjs`. Only the migration reader requests old name-based
notation semantics; incomplete historical contexts explicitly refuse replay.

## Adopted mutation contracts

The existing runner and its limits are reused. No historical baseline is changed.
All twelve contracts are killed at clean revision `07bb8c78`; each has a
passing baseline and a distinguishing assertion failure. Process, syntax and
fixture-precondition failures are not counted as kills.

| Historical contract | Current boundary or retirement evidence |
| --- | --- |
| Binding labels | Source introduction metadata; CB5 written-link and hover control |
| Alpha-renaming labels | Binding adapter's public binder label; same source control |
| File-level selection | Source activation; uncolliding preservation witness |
| Reference spelling | Binding adapter resolution; exact imported inheritance |
| Derived telescope | Complete retained interface; G11 intended/captured computations |
| Hom universe | Retained Hom type inference; generic fixed-domain successor/refusal control |
| Refined evidence | Shared scope refinement; checked evidence and dimension restrictions |
| Reservation | Shared declaration ownership; original value survives collision |
| Failed publication | Native transaction boundary; fault-injected parent rollback |
| Synthetic provenance | Written-source ownership; generated-header links |
| Lint interface | Public telescope boundary; named constructors and generated clients |
| Explicit path head | Pattern compiler; wrong explicit bodies cannot become automatic obligations |
| Fallback eligibility | The old recursive-position restriction was intentionally replaced in CB3. Automatic path evidence is checked for every eligible implicit path. G8 now records the charged failed search and preserves the primary mismatch; explicit wrong-path controls still refuse. |
| Fresh-label survivor | Fresh core variable spelling is private; source introduction and binding-adapter labels carry the public name. Source links/hover and alpha-invariant checked terms are the observable controls. |
| Recursive-update survivor | `withRecursion` now updates callable and permission aliases together. Nested/dependent match and contextual replay controls exercise current permissions; the former one-alias update is gone. |
| Recursive-source-guard survivor | Its sole consumer was producerless `recursiveCall`, removed here. Exact recursive bindings and ordinary structural-call refusals remain. |
| Hlevel-globals survivor | Text-generation exclusion lists are gone. Evidence predicates are captured by identity; retained carrier/universe and same-spelled source controls exercise their meaning. |

## Release evidence

The [release report](../../../tests/fixtures/capture-bindings-release-costs.json)
contains all 45 samples at clean `0c27548a`: three repeats of three workloads
with references off/on, scopes on, artifacts on and both on. Each sample starts
a fresh process, WASM module and kernel handle. Node v24.13.0 on Apple M3 Pro,
Darwin 25.5.0; build digests and unchanged limits are in the report. The
[pre-retirement report](../../../tests/fixtures/capture-bindings-pre-retirement-costs.json)
is clean `3b9a0845`. Later adapter-option deletion affects no measured caller.

Every current workload inventory equals that checkpoint: interfaces, generated
names, assumptions and deterministic fuel. Kernel work also agrees across modes
and with the checkpoint in these runs; cache-sensitive work is not deterministic
fuel. The complete 3,857-check corpus inventory equals the CB0 record.
Against CB0 `7f9b4d28`, fuel changes by -144 algebra queries, +46 inheritance
queries and -159 fold queries, with unchanged search counts. Six inheritance
interfaces (P/Q/R `.make` and `.l`) have changed alpha-syntax hashes but native
conversion checks confirm definitional equality: retained helper applications
and ascriptions remain explicit. No cross-version fuel or syntax-hash equality
is claimed.

Retained process memory is sampled after GC, before serialization or queries.
V8 encoding measures inert scope/replay inputs and generated artifacts with
sharing preserved; encoded bytes are not heap estimates. Peak RSS includes
temporary serialization buffers. No live scope or native handle is serialized.

The report's `memory.disposed` is **not proof of graph release**. In all twelve
algebra/fold scope-enabled samples it includes a graph still held by the tool's
serializer: about 450–461 MiB absolute heap after disposal versus 485–497 MiB retained growth.
An independent exact-path probe reproduced 449.6 MiB after disposal, with the
program, recorder and replay object collected but the serialized scope map alive.
One further turn/GC released it to 33.1 MiB; omitting serialization yielded
33.4 MiB at the existing sample. Returning from the measurement frame and yielding
one turn did not resolve that serializer lifetime. Earlier v1/v2 readings and
the failed v3 interpretation remain in the review evidence; no runtime leak,
async-turn explanation, or release guarantee is inferred from them. Release
memory is not an acceptance threshold, so no extra GC protocol is added.

## Measured allowances and exceptions

Normal-check allowances were derived from the pre-retirement maximum plus its
observed max-minus-min spread, separately for each workload and collection mode:

| Workload | References off: ms / peak RSS MiB | References on: ms / peak RSS MiB |
| --- | ---: | ---: |
| Algebra | 1,541.2 / 334.9 | 1,842.9 / 386.4 |
| Inheritance | 572.2 / 204.7 | 646.1 / 267.2 |
| Fold | 1,672.9 / 340.9 | 1,942.6 / 386.6 |

All six timing allowances and five RSS allowances hold. Algebra refs-off repeat 1
peaks at **338.2 MiB versus 334.9 MiB allowed**; the checkpoint's repeats were
331.4/333.1/331.2 MiB. This is an explicit release exception, not a passing sample.
Retained heap growth remains 44.1/45.1/44.1 MiB versus the checkpoint's 45.1 MiB, and
no measured checker work changed. Accept this small OS high-water variation
without widening the allowance, rerunning for a favorable sample, or changing
compiler/process limits. Three observations do not establish a universal bound.

New optional collection has no CB0 equivalent. The final sample maxima are
3.595 s per check, 496.9 MiB retained heap growth and 150.1 MiB encoded graph,
with all 19,778 points available on the largest fixture. These fit the named-
fixture allowances of 5 s / 512 MiB / 160 MiB. The initial 4-second proposal was
exceeded by a 4,057 ms sample in v2 (`d482c652`); it was explicitly superseded
before v3 by 5 seconds, allowing the cross-run timing spread. That earlier sample
is not reclassified as passing the original proposal. Scopes remain opt-in;
these measurements do not guarantee costs for arbitrary modules.

[Replay evidence](../../../tests/fixtures/capture-bindings-replay-costs.json)
contains five existing fixtures, three sessions each, with artifacts off/on at
`733a59ce`. Each query gets a fresh native handle in a shared WASM process, with
no explicit JIT warm-up. Verdicts/text agree across modes and original kernel
work is unchanged. Maximum prefix/validation/history/query times are
299.2/1.21/1.02/2.69 ms, within the named-fixture allowances of 350/2/2/3 ms.
The sections fixture retains 129–133 MiB with scopes on, versus the earlier CB6
206 MiB observation despite added inspector entries. No resource limit changed.

## Validation and review

At product revision `5a4f8cef`, all **1,332 frontend tests** and **3,857 corpus
checks** pass, with zero skips/TODOs; native tests pass. At `07bb8c78`, all twelve
mutations and all three browser suites pass: contextual console, inspector and
the built static site `6a013d03e55c`. Product code is the same at both revisions.
The initial synthetic mutation survived because copied/imported observations
were independently rejected by `ownsSource`; the existing generated-header test
exercises synthetic syntax in its own module and kills it. The failed run remains
preserved. No product predicate or assertion was weakened to obtain the kill.

Claude round 1 verifies that retirement and coverage at `0c27548a`, finding the
two measurement-claim errors above and the unused module-wide adapter option.
The latter is removed: retained queue entries get an adapter only through
`lowerBindingDeclaration`. All 137 focused admission, generation, opening and notation tests pass after
that deletion. Claude round 2 is clean at `32bda0ee`, independently confirming
the deletion, numerical claims and committed evidence. Review stops at two rounds.

## Producer and consumer audit

The current-language retention boundaries were audited after the final removals:

| Boundary | Current path |
| --- | --- |
| Theory headers, fields, helpers and inheritance | retained-theories -> RetainedInterfaces -> bindingSyntax; sameBindingSyntax aligns identities for sharing; byName is only public duplicate/label indexing. |
| Deferred patterns, proof references and openings | binding-syntax owns slots; lowering preserves unresolved slots until actual scope transitions; retained unknown-type probes use constructorInventory/enclosing IDs. Ordinary source and matched-type constructor lookup remain allowed. |
| Named notation and lazy operands | retained named rules and checked notation-context receipts; operand caller contexts preserve lexical identity. |
| Base/Hom/Iso/initial/free generation | ArtifactBuilder and retained-*-artifacts emit bindingDeclaration; lowerBindingDeclaration is now the only retained queue adapter. No source-text generator or old reference/recursiveCall producer remains. |
| Publication and availability | existing groups/native transactions publish the checked env; CompilationBindings records identity independently of availability. Twelve mutation checks include refusal and rollback. |
| Diagnostics and views | source-syntax/link-sites carry origins; bindingDisplay renders binding-aware artifacts; captured identity is not looked up by destination spelling. |
| Context queries | ScopePoints receipts + full ordered ReplayInputs + isolated ContextualSession, with attempt ownership and explicit unavailable historical contexts. |
| Historical compatibility | legacy-syntax and migration readers; nameBased is requested only for old migration inputs. Current source does not retry through it. |

rg audit: removed elaborationSyntax, resolveBindingModule, lowerBindingModule and recursiveCall have no production occurrence. The explicit old/mixed reference rejection in binding-syntax remains intentionally. E801/E860/E869/E871/E866 occur in web only as retired catalogue rows. Source syntax traversal and structural receiver helpers remain because current source and retained consumers still use them.
