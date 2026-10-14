# CB1 implementation evidence

CB1 implements the identity, observation and replay contracts in the
[capture-bindings roadmap](capture-bindings.md). The ordinary-declaration and
nested-function pilots are executable. The default module frontend still
uses its existing representation; retained interfaces and deferred families
migrate in CB2/CB3. The source/generated-view UI and full contextual REPL are
CB6 work.

## Identity and elaboration boundary

`BindingTable` allocates revision/owner-qualified identities with immutable
labels, roles and source-qualified origins. `LexicalContext` records binding,
reserved, missing and deferred-slot resolutions. Cloning returns an explicit
freshening correspondence; substitution preserves an inserted argument's own
references, including under undecided slots. Serialized tables validate their
allocation correspondence when restored.

`resolveBindingSyntax` shares the existing scope schema and traversal.
Grouped domains are resolved once and shared by their entire group, outside
all that group's binders. Inferred declaration headers and
their parameter lambdas use the same canonical telescope. `BindingAdapter`
lowers identities to private keys; a missing source resolution cannot acquire
a destination meaning. Constructor candidates retain their enclosing
resolution and source inventory. Compiled matches and direct induction or
obligation clauses use the same slot-decision operation. Introducing a source
binder derives its key from its identity. Structural recursive-call checks
lower the decided slots before inspecting their arguments.

Migration is an explicit allowlist. The scope schema records plain-token
reference fields and their namespaces, including local witnesses and
simplification rule/set selectors. Simplification statements remain refused
at the identity boundary until those namespaces migrate in CB3.

`Translator.translateSyntax` accepts prepared syntax through the same checking
and admission path as parsed source. The complete ordinary-declaration pilot
checks dependent term/universe telescopes, dimensions, named arguments after
freshening, shadowing, recursive/generalized calls and structural refusals.
`resolveBindingModule` owns ordered declaration resolution, self-reference
eligibility and identity allocation; the pilot uses this production entry.
Module preparation and contextual queries share the context/constructor
inventory builder. Declaration admission and failure install the corresponding identity entry.
Recursive permissions have an environment key separate from their display
label, and every recursive scope transition updates the permission record and
callable alias together. Failed declarations do not supply usable identity entries. The pilot
prepares only the migrated ordinary family; it is not a second checker or an
automatic module-wide migration switch.

## Scope ownership and execution

An `ObservationFrame` owns references, proof steps and scope descriptions
through nested pending/selected/discarded attempts. Quiet and abandoned
attempts publish nothing. Fuel/work accounting remains independent. Explicit
before/after statement transitions record the actual continuation scope.

With `collectScopes: true`, `CubicalProgram` retains selected immutable scope
descriptions and a pinned source/import check. Context descriptions are data,
not typing authority. They contain lexical IDs, core context/value descriptions,
slot outcomes, recursion permissions, dimensions, rule evidence and targets.
Shared lexical/context components reduce retained memory; mutable recursion
permissions are projected separately at every point. Source positions and
owner/attempt paths identify instances. No description retains a live `Scope`,
checker, mutable environment or native handle.

Binding introduction clears shadowed metadata; refinement explicitly keeps
the same identity. Parsed syntax carries source-qualified origins before
expansion. Notation expansion preserves the authored origin and adds a use
frame; those scopes remain unavailable until CB3. Registered rule descriptions
are shared within a declaration and snapshotted anew after registrations.

`new ContextualSession(program, pointId)` opens one selected point. Each
`run(input)` entry creates a fresh native session and replays the full ordered
prefix, including imports, directives and earlier attempts. It materializes
only the requested description, compares that description, validates the local
context natively, rechecks accepted scratch lets and executes the new query in
a synchronous callback. `ElaborationStop` unwinds without proof recovery or
publishing the unfinished declaration. The isolated session is always disposed.

The pinned input includes read failures, source texts, the legacy reader flag,
fuel limits, kernel retry policy and deadline epochs. Changed prefix outcomes
or exhausted fuel/budget/deadline produce an unavailable result. They do not
select another point or increase a limit. Scratch history contains source and
binding correspondence only. Failure preserves it; source rechecks invalidate
sessions before asynchronous discovery completes. Successful results are
explicitly conditional on the selected scope.
Collection requires declaration transactions. Replay remaps recursive
permissions through the recorded environment-key correspondence, discarding
compiler-private aliases which query syntax cannot name.

The nested-function script checks a local equality, accepts a scratch let,
evaluates it to `succ(succ(k))`, rejects a type mismatch, then answers `Nat`.
Other executable controls cover before/after shadowing, a selected prefix in a
failed declaration, two-session isolation, stale checks, history failure,
invalid recorded lambda domains, recursion restrictions and original-program
state/work preservation. Three fulfilled CB1 contextual TODOs were retired;
the CB6 UI/coverage TODOs remain.

## Pilot costs

Reproduce with `node --expose-gc tools/contextual-pilot.mjs`, run alone. The
tool checks results and original kernel work, measures collection off/on, and
runs the complete five-entry session three times. Each request uses a fresh
native handle; WASM and the Node process are shared, without explicit JIT
warm-up. Process memory is measured around checks after GC and before JSON
serialization or queries. These are observations, not performance budgets.

After the round-1 corrections, Node v24.13.0:

| Measurement | Collection off | Collection on |
| --- | ---: | ---: |
| Check elapsed | 143 ms | 180 ms |
| Retained heap growth | 7.13 MB | 4.89 MB |
| Scope instances | 0 | 1,620 |
| Available instances | 0 | 113 |

| Request stage, across 15 entries | Minimum | Median | Maximum |
| --- | ---: | ---: | ---: |
| Full prefix replay | 69.22 ms | 81.69 ms | 117.84 ms |
| Native context validation | 0.164 ms | 0.178 ms | 0.381 ms |
| Accepted scratch history | 0.001 ms | 0.317 ms | 0.423 ms |
| New query | 0.168 ms | 0.313 ms | 2.108 ms |

These figures are not directly comparable to the earlier run at `69ec8a52`
(18.79 MB with collection, 199 ms median prefix). The corrected eligibility
boundary marks 628 notation-expansion instances unavailable until CB3, along
with 878 generated/selected instances and one inductive-self context. Earlier
measurements incorrectly treated those notation expansions as available.
Heap growth is a process observation across separate checks, including cache
retention and GC effects; it is not an estimate of collection's marginal cost.
Collection off/on performs identical kernel work: 14,186 instructions and
1,035 queries. Naively JSON-serializing the entire index still repeats shared
components (2.73 MB); it is not the intended CB6 transport encoding. The stored
replay inputs occupy about 28 KB. There is no retained execution session or
dependency-only replay optimization.

## Validation

The focused declaration/identity/argument/match/replay suites passed 57 tests.
The subsequent prefix-outcome, immutable-limit and scope suite passed 28 tests.
External review round 1 identified gaps in direct-clause slot decisions,
recursive record updates, binder metadata, source ownership and migration
boundaries. The expanded focused suite after the corrections passed 68 tests.
It includes induction obligations, nested recursive queries, pattern
shadowing, shared grouped domains and imported notation origins. The subsequent
full run passed 974 tests with 52 existing TODOs and no failures, including all
3,857 canonical corpus declarations. A final correction shares declaration
ownership between preparation and admission; all five declaration tests passed
afterward, including its new distinguishing duplicate-declaration control.
Subsequent external review results are recorded in the PR.
