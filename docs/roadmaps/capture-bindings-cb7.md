# CB7: retirement and release

Status: implementation and release validation in progress, stacked on CB6 #239.
The user-requested cleanup across CB0–CB7 follows in a separate PR.

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

The existing metrics runner now compares references off/on, scopes on, artifacts
on, and both on. Each workload/mode/repeat uses a fresh process, WASM module and
kernel handle. Semantic interfaces, generated names, assumptions and deterministic
fuel must agree across collection modes. Kernel work is recorded with cache
conditions; it is not treated as deterministic fuel.

Retained memory is sampled after GC and before serialization or queries. Inert
scope/replay inputs and generated artifacts are also serialized with Node's V8
encoding to preserve graph sharing; encoded byte sizes are not heap estimates.
No live scope or kernel handle is serialized. Existing subprocess, checker and
description limits remain unchanged. Replay timing uses the existing contextual
pilot rather than another query backend.

At product revision `5a4f8cef`, all 1,332 frontend tests and 3,857 corpus
checks pass, with no skips or TODOs. This includes the catalogue and publication
fault-injection controls. Native tests pass. At `07bb8c78` (only mutation-witness
selection and documentation changed), all twelve mutations and all three browser
suites pass: contextual console, inspector and the built static site
`6a013d03e55c`. The 36-test retirement focus also passed before the final removal
of producerless recursion cases; the full gate includes that removal.

The subsequent changes affect measurement tools only. Final corrected memory
measurements and Claude review are pending.


The initial mutation run kills eleven of twelve candidates. The synthetic-node
mutation survives the copied/imported-observation tests because `ownsSource`
independently rejects those copies. The existing generated-header link test
exercises synthetic syntax in its own module and kills that mutation. Correct
the runner's selected witness, not the product predicate or the assertions.
The targeted rerun passes; a final clean-revision mutation report follows.
Native tests pass on `5a4f8cef`. Full frontend validation is still running.


The first complete cost run preserves corpus inventory, current interfaces,
assumptions, fuel and kernel work across all five collection modes. Its disposal
sample exposes a measurement-lifetime flaw: clearing the program variable inside
`sample` still leaves that function's local aliases to symbols and retained graphs
alive during GC. This also affects the old tool's disposal readings. Move only
the disposal sample to its caller, after `sample` returns inert measurements and
releases the entire frame. Do not infer a runtime leak from these aliased samples
or add a disposal/cache mechanism to the compiler. Re-run cost evidence after
checking that the measurement now permits graph collection. The valid earlier
check-time/retained-memory results and failed disposal interpretation are retained.


## Measured release envelope

All 45 initial samples at `07bb8c78` (three repeats, three workloads, five
collection modes) preserve the full CB0 corpus inventory. Current interfaces,
generated names, assumptions and deterministic fuel match the pre-retirement
`3b9a0845` checkpoint exactly. Observed kernel work also agrees across modes in
these fresh-process runs. No additional assumptions or unavailable points occur.

Against CB0 `7f9b4d28`, deterministic fuel changes by -144 algebra queries,
+46 inheritance queries and -159 fold queries, with unchanged search counts.
Six inheritance interfaces (P/Q/R `.make` and `.l`) have changed alpha-syntax
hashes but check definitionally equal in the native kernel: retained helper
applications and ascriptions remain explicit. Every other inventory field agrees.
The native-input build stamps match for that comparison. No cross-version fuel
or syntax-hash equality is claimed.

For normal checking, the release allowance is the pre-retirement maximum plus
its observed max-minus-min spread, separately for each workload/mode. This derives
headroom from measured variation rather than a new percentage or compiler limit:

| Workload | References off: ms / peak RSS MiB | References on: ms / peak RSS MiB |
| --- | ---: | ---: |
| Algebra | 1,541.2 / 334.9 | 1,842.9 / 386.4 |
| Inheritance | 572.2 / 204.7 | 646.1 / 267.2 |
| Fold | 1,672.9 / 340.9 | 1,942.6 / 386.6 |

The initial release samples fit all six envelopes. New optional collection has
no CB0 equivalent. Its measured largest check is 3.68 s, retained heap growth
498 MiB and sharing-preserved graph 150.1 MiB, for 19,778 available points.
The release envelope for these three named fixtures is therefore 4 s per check,
512 MiB retained heap growth and 160 MiB encoded graph. These are rounded bounds
on the measured workload; they are not guarantees for arbitrary user modules.
Scopes stay opt-in. Artifact-only collection adds at most about 2.1 MiB retained
heap in these samples. Peak RSS includes temporary serialization buffers; the
GC retained heap/RSS samples precede serialization.

Replay on `733a59ce` runs five existing fixtures three times, with artifact
collection both off and on. Every query's verdict/text agrees between modes;
original kernel work is unchanged. The largest observed prefix is 299.2 ms,
validation 1.21 ms, accepted-history replay 1.02 ms and new query 2.69 ms. For
these fixtures the measured release envelope is 350 / 2 / 2 / 3 ms respectively.
The section fixture retains about 129–133 MiB with scopes on, down from the CB6
pre-review 206 MiB despite additional inspector entries. No limit was raised.

The corrected cost rerun must confirm the envelopes and measure disposal after
the frame returns before this candidate is marked complete.

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
