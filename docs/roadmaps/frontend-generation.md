# Frontend generation: contracts and remaining evidence

The [inventory](../reports/frontend-generation-gaps.md#current-status-and-fixing-evidence)
owns finding status, fixes and distinguishing regressions. The
[work plan](work-plan.md#frontend-generation-track) owns delivery status,
ordering and dependencies. The [FG reports](../reports/README.md#frontend-generation-evidence)
retain implementation evidence at their revisions.

This roadmap stays active under the [archival rule](work-plan.md#release-checks-and-documentation):
the [original mutation-audit evidence](../reports/frontend-generation-gaps.md#mutation-audit-and-remaining-evidence)
and [performance follow-up](../reports/frontend-generation-gaps.md#performance-observations-p1)
still need a disposition. Its remaining work is to recover the original audit
manifest and justify a resource budget from comparable measurements. The
sections below retain normative acceptance contracts for future changes,
not instructions to repeat the delivered implementation slices.

Generation must preserve a declaration's meaning and interface through
capture, inheritance, substitution and elaboration. Unsupported constructions
must be refused before invalid artifacts are published. Kernel checking
establishes the generated terms' stated types; independent semantic checks
must establish that those types express the source that was written.

## Shared contracts

The names below describe information that each boundary must retain. They
do not require a separate class per row. Scope, substitution and source
identity obey the [syntax hygiene contract](syntax-hygiene.md).

| Boundary | Information it must retain | Forbidden shortcut |
| --- | --- | --- |
| Declaration ownership | Module, namespace, declaration kind, stable identity, source origin, reservation/check status | Using separate duplicate-name rules for definitions, inductives and generated declarations |
| Retained declaration/expression | Complete parameter telescope and scoped result/body, resolved external dependencies, open binder interface, selected notation, source origin | Resolving a captured occurrence from display spelling, or transforming a body after discarding its binders |
| Generation request | Captured theory record, caller-scoped arguments, parameter interface, requested artifact family, support result | Reading a later theory or `use` selection because its name matches |
| Artifact plan | Declared identities, dependency edges, public labels, origins, checked publication groups, obligations | Inferring dependencies from dotted names or retrying arbitrary failed templates |
| Elaboration context | Term/level/dimension scope, refinements, checked evidence, recursion state, value/type purpose, primary diagnostic, resource accounting | Reconstructing compiler state from source names or replacing a written mismatch with a failed speculative fallback |
| Source reference | Lookup identity/key, written label, binder definition origin, occurrence origin | Comparing a public label with an internal environment key to find the binding |
| Published interface | Checked artifacts, argument labels, supported derivations, diagnostic/provenance metadata | Presenting an unchecked reservation or unsupported capability as a usable declaration |

Raw local names remain valid in nominal syntax. Before retaining an
expression, classify every free occurrence as an explicit interface binder,
a resolved external dependency, or an unresolved occurrence to diagnose at
its original site. The destination must not supply a new interpretation
for an accidentally unclassified occurrence. Unknown syntax kinds must
continue to fail scope traversal visibly.

Generation has explicit steps: reserve names; capture interfaces; analyze
support and dependencies; build an artifact plan; elaborate in a staging
context, including universe inference; check; publish. Dependent artifacts
may use checked predecessors inside the staging context. A syntax-only
planner must not claim to have inferred types or discharged obligations.

## FG0: establish evidence and semantic comparisons

A behavioral contract states independently expected public declarations,
types, labels, computations, assumptions and refusal sites. Check both the
intended and accidentally captured equations; acceptance alone cannot
detect a changed law. Historical passing controls and new counterexamples
must remain distinct. A dependency failure may need controlled injection
when no source reproduction is known. An expected failure cannot count as
completion or silently become an accepted snapshot.

The [inventory](../reports/frontend-generation-gaps.md) maps baseline
reproductions to their distinguishing regressions.

## FG1: unify declaration ownership and publication

Ordinary and generated declarations share module-local ownership checks.
Reserve generated names before publication; keep legal local/import
shadowing and notation extensions separate. A duplicate must preserve the
original binding. A failed dependency retains its identity and root cause.

Publication groups have explicit required and optional dependencies. A
refused Hom family must leave the checked base theory usable. Checkpoints
cover environment aliases, native kernel registrations, theory records,
notation, inspection, exports and caches. Rollback, edits and import
invalidation must leave no partial group visible, and replay must agree
with the checked state. See the [FG1 evidence](../reports/frontend-generation-fg1.md).

## FG2: describe dependencies and supported generation explicitly

Dependency graphs use binding identities and an explicit ordered interface,
including complete helper telescopes. They distinguish carriers, laws,
evidence, operations, fixed external dependencies and unresolved occurrences.
Each construction strategy supplies its own support result and checked
mapping/transport obligations; sharing a graph does not equate morphism
and initial/free admissibility.

Unsupported model-dependent transport must be refused before Hom/Iso
emission, retaining the checked base. Structured references, complete
inlining scopes, lexical notation, value/type call classification and
located capture refusals obey [syntax hygiene](syntax-hygiene.md).
Every changed syntax representation needs a producer/consumer audit,
including traversal, serialization, relocation, diagnostics and lowering.
See the [FG2 evidence](../reports/frontend-generation-fg2.md).

## FG3: infer universes from the generated telescope

Infer a sufficient universe from all generated field types in their
parameter context: fixed domains, dependent arguments, family indices and
proof/evidence fields included. Use the least level justified by the
existing solver while preserving shared-universe and finite/tiered rules.
Hom, identity, composition and supported Iso artifacts use the same analyzed
telescope. Refuse unresolved obligations before publishing the family;
never replace inference with a blanket large level.

Acceptance includes U0/U1 and generic inputs, inherited operations,
dependent indices, genuine lowering refusals, public types and assumptions.
See the [FG3 evidence](../reports/frontend-generation-fg3.md).

## FG4: carry evidence and compiler state with the context

The [generation boundary](syntax-hygiene.md#generation-boundary) governs
checked model evidence, scope refinement, recursion state and optional
wildcard coherence. Evidence must be checked for the actual model, motive
and boundaries; an index hit cannot authorize elimination. Resource-limit
failures remain distinct from proof-search failure, and all attempted
work is charged. Successful coherence retains its inspection evidence.

Acceptance covers imported/inherited scopes, nested and dependent matches,
wrong-model evidence, incompatible endpoints, structural recursion and
explicit path bodies. Compare error code, endpoints and original body span,
not just a declaration's failure. See the [FG4 evidence](../reports/frontend-generation-fg4.md).

## FG5: preserve public interfaces and source provenance

The [source identity contract](syntax-hygiene.md#resolved-syntax-and-closures)
separates lookup keys, written labels, binder origins and occurrence ranges.
Every consumer, including CLI/browser inspection and definition navigation,
must preserve that separation. A refusal points to the responsible written
token; synthetic syntax must not claim source links.

Lint edits must preserve public argument labels and supported generated
interfaces through actual named-call, Hom/Iso and initial/free clients.
Preserving the standalone function type alone is insufficient. Suppress
arrow-form advice when it changes those interfaces; ordinary safe advice
must remain available. See the [FG5 evidence](../reports/frontend-generation-fg5.md).

## FG6: make preservation tests and measurements a release gate

Compose bounded deterministic transformations: alpha renaming under
shadowing, colliding generated stems, imports with explicit export
correspondences, inheritance under changed notation, complete-telescope
inlining, source-label preservation, optional coherence, earlier recursive
value calls and supported lint edits. Compare independent equations,
computations, assumptions, public artifacts and source observations, with
explicit identity correspondences rather than printed-text equality.

Record seeds, limits and minimized failures. A mutation needs a passing
unmodified baseline and an assertion failure in a named distinguishing
test; crashes, syntax/import errors and timeouts are not kills. Separate
required kills from justified equivalent/defensive probes. A survivor calls
for analysis, not an automatically weakened assertion.

Record revision/build stamps, workload, limits, kernel work, available
memory measures and wall time. Machine-dependent timing alone is not a
budget. Rerun unexpected corpus timeouts with unchanged limits and retain
the original outcome. Source/corpus and CLI/browser checks supplement the
direct semantic contracts. See the [FG6 evidence](../reports/frontend-generation-fg6.md)
and the inventory's [historical audit limits](../reports/frontend-generation-gaps.md#mutation-audit-and-remaining-evidence).

## Capability boundary

[L2.6](core-theories.md#initial-and-free-models-l26) owns opt-in registration,
uniqueness, universal equivalence, extra-law evidence and higher coherences.
Frontend preservation gates supplement those proof obligations. A type and
fold alone cannot register a checked deriving capability or imply support
for additional carriers, families or elimination principles.
