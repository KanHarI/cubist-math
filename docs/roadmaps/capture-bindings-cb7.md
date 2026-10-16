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
The current candidate set ports twelve contracts to their actual production
boundaries; terminal results are pending.

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

Final native/frontend/corpus, catalogue, publication fault injection, mutation,
inspector/contextual/site browser results and measured release budgets are pending.
The first retirement focus passes 36 tests; it precedes removal of the unreachable
`recursiveCall` cases. Claude review starts after the implementation gates.


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
