# FG2 retained dependencies and generation support

This implements FG2 in the [frontend generation roadmap](../roadmaps/frontend-generation.md#fg2-describe-dependencies-and-supported-generation-explicitly).
G3 and G10–G12 are active assertions, including all three G11 telescope
variants. The remaining expected failures belong to FG3–FG5: G2, G4, G5,
G8 and G9. Passing them as expected failures does not complete those phases.

## Retained interfaces and dependencies

`cubist/dependencies.mjs` reads the shared scope traversal. A retained
theory has an ordered open universe/parameter interface and a field graph
whose edges carry binding identities, source occurrences and categories:
carrier, operation, law, h-level evidence, helper, fixed external reference,
builtin, hole or unresolved occurrence. Selected notation is a fixed
external dependency. Parameter domains see preceding parameters, without
accidentally seeing a same-spelled field. Bound locals are excluded using
the same grouped telescope rules as substitution.

The graph follows field signatures and complete helper values transitively,
with cycle detection and an identity path to each reachable dependency.
A resolved reference is looked up by identity; changing its display label
cannot turn it into a carrier. Inherited graphs are rebuilt through the
renamed interface, preserving each field's origin identity. Unresolved
syntax still receives the ordinary base-declaration diagnostic; an invalid
base cannot publish its retained record for later reinterpretation.

Hom/Iso and equational initial/free generation consume the same dependency
facts but have separate support predicates. Conditional support includes
the actual fixed/push/pull mapping or fixed/recursive constructor argument
plan and named obligations for ordinary checking. It is not a claim that
the syntax analyzer has inferred universes or checked preservation. Initial
constructor lowering consumes its plan rather than deciding admissibility
again. Refusal metadata retains the responsible field/dependency identity
and occurrence; initial/free diagnostics still point at the user's request.

G3 now refuses model-dependent operation domains before emitting Hom/Iso
syntax. The same decision handles a law hidden behind an external type
alias and an inlined helper, carrier evidence and operation values. The base
theory and its ordinary clients remain checked and usable. Fixed external
arguments, captured global types and supported family indices keep working.
Higher-order covariant inputs can admit Hom while the equational strategy
refuses them, demonstrating that these are different predicates.

## Complete telescopes and calls

Derived records convert to complete declaration syntax for capture,
substitution, inheritance and inlining: parameter groups, each group's
domain, subsequent domains, result and body. Shared scope traversal
freshens a derived parameter consistently while preserving its public label.
Capture-avoiding field renaming preserves each occurrence's own span.
Fixed pattern/statement capture errors receive the actual conflicting binder
token and nonempty range (G10), rather than the start of the containing law.

Inlining has explicit type and value purposes. Type/law use still refuses
recursive unfolding with E845 at the written call. A derived value can call
an already checked recursive operation through its retained projection;
it does not inline that operation's recursive body. Structural self-calls
remain under the existing private recursion mechanism. A nonstructural
self-call remains refused. Imported and inherited ordinary calls compute,
including through an initial model.

Independent clients check the intended `op(x, S.c)` equation and reject the
captured `op(x, x)` equation. Tests cover helper chains, grouped/dependent
telescopes, public named arguments, imported/renamed inheritance and
generated clients without introducing assumptions.

## Notation-scope disposition

The old `notationScope` node and initial/free alias installation are removed.
Its single producer, elaboration case, captured-payload traversal exception
and retained `Theory.notation` field are gone. Expressions already retain
selected operators/literals and resolved external names. Their lexical
captures are now the only source of notation for copied fields.

The old wrapper also disabled source links. Removing that behavior initially
failed the existing `imported initial and free fields keep the theory's
notation without a caller selection` test: a captured rule expanded with
offsets from its original module. Synthetic evaluation now disables links
through its whole subtree, including copied rules. That distinction belongs
to provenance, not notation selection, and the original assertion remains.

Existing tests distinguish imported versus caller notation, renamed notation
declarations, parent versus child selection, copied fields versus caller
arguments, and selected model fields versus later same-spelled globals.
B1's file-level `use` precedence remains intentional. Failed selections
depend on FG1's publication lifecycle rather than on absence of an alias list.

## Producer and consumer audit

| Boundary | Consumer and evidence |
| --- | --- |
| Complete declaration syntax | `scopes.mjs` describes derived parameters once; `theories.mjs` uses it for capture, inheritance and inlining. `scopes.test.mjs` audits parser/producer kinds and repository syntax. |
| Binding identities and local receivers | Existing `reference` and `member` nodes remain structured. `references.test.mjs` checks transformation/serialization independence from spelling; `theory-resolution.test.mjs` checks local receivers, imported globals, family indices and colliding template stems. |
| Graph and support data | Plain record metadata, not a new AST kind. `elaborationSyntax` preserves the theory record; only expression references lower to environment keys. Categories do not masquerade as syntax kinds. |
| Builder boundaries | Source templates retain fresh holes with structured payloads. Public labels, occurrence positions and binder positions survive substitution and relocation. No private reference is reparsed as source. |
| Initial/free diagnostics and inspection | `failedExpansion` and `CubicalProgram` retain structured support alongside ordinary diagnostics; accepted generated declarations retain their plan. Existing CLI/publication/source-inspection tests exercise the result consumers. |
| Notation and provenance | The redundant producer/consumer layer is removed; `term` suppresses synthetic evaluation links. Existing notation, h-level evidence and browser checks validate the remaining path. |

## Validation and resource measurements

Implementation commits: `f70699fe` (telescopes/call purpose/source sites) and
`908fcd60` (dependency/support analysis and notation consolidation).
The implementation does not change kernel rules, declaration/search fuel,
or the initial/free capability boundary.

The final full suite at the completed implementation has 808 tests:
803 pass, five explicitly tracked later-phase TODOs, zero failures, zero
skips (122.4 seconds). This includes all ten focused dependency tests,
source/library checks, native-kernel tests, publication/CLI regressions and
the semantic capture controls. Inspector browser and final built static-site
browser checks pass, as do the diagnostic catalog and diff checks. No corpus
timeouts required retries and no resource limit was increased.

Measurements compare FG1's clean `fe05ea5e` with clean `908fcd60`. Raw
[FG1](frontend-generation-metrics/fg1.json) and
[FG2](frontend-generation-metrics/fg2.json) reports contain frontend/source
digests, the same WASM build stamp, default limits and three fresh kernel
sessions per workload. FG2 was measured without concurrent test load.

| Workload | Median ms, FG1 → FG2 | Instructions | Queries | Peak arena bytes |
| --- | ---: | ---: | ---: | ---: |
| Algebra import | 1286.9 → 1206.6 | 118,850 | 14,495 | 4,593,664 |
| Captured inheritance chain | 320.0 → 299.8 | 51,732 | 3,883 | 2,624,512 |
| Generated free fold | 1310.5 → 1206.0 | 125,859 | 14,990 | 4,593,664 |

Instructions, queries, instruction/query steps and arena peaks are unchanged
in all three workloads. The recovered kernel exhaustion counters remain
6/0/6, with no deadline failures or gaps. Arena memory is sampled after
declarations, not whole-process or JavaScript graph memory. Timings are
observations on this host, not a speedup guarantee or a regression budget.
