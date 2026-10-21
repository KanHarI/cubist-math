# Quotient normalization: counted rewrites

Measured on 2026-10-19 against main `89f73ea1`, using the
[arithmetic-free quotient fixture](../../tests/fixtures/generic-prop-normalization.cubist).
The checkpoints follow the documented traversal and rule order. They expose
rapid expansion of generated transports into universe-composition witnesses;
the repeated events explained below do **not** establish a self-reproducing
beta redex or a wrong kernel rule.
The [full-normalization failure](rational-normalization.md) remains unresolved.

## What a step means

One step is a recorded delta, beta, eta, eliminator/projection, path, composition,
or face-restriction rule application. Substitution and construction of a
cubical rule's result are atomic at this granularity; a step can allocate many
nodes. Face restriction is recorded separately from beta reduction. Kernel work
budget ticks, recursive visits, allocation and cache lookups are not steps.

The diagnostic disables weak-head and full-normal-form cache shortcuts after
checking the fixture, so no cached answer jumps over contractions. Syntax
interning and substitution memoization remain enabled. This traces the native
normalizer's traversal and rules without reduction-cache shortcuts; its step
numbers are not a profile of the ordinary warm-cache query. In particular,
**many events repeat exactly because the caches are disabled**:

| Trace | Events | Repeats of an earlier identical event | Unique event triples |
| --- | ---: | ---: | ---: |
| Full | 50 | 26 | 24 |
| Body | 50 | 7 | 43 |
| Transport | 50 | 29 | 21 |

Here an event triple is `(rule, enteredTerm, result)`, using exact handles;
this is not a count modulo alpha or definitional equality. The transport
trace repeatedly unfolds the same `Prop(U0)` annotation at different traversal
positions. For example, events 2 and 4–10 recur exactly at 32 and 34–40.
Ordinary reduction-cache
hits would avoid redoing those completed contractions. This repeated work is
an effect of the diagnostic setup, not evidence of a production cache bug.
The two universe-composition events at 21 and 31 are distinct.

Three entry points prevent annotation work from obscuring the computation:

1. **Full:** the checked definition reference `to_prop`, including binder types.
2. **Body:** its body under the existing `h` and `q` binders. Their types are
   retained as context, but are not normalized as part of this query.
3. **Transport:** expose the body's quotient eliminator, select its third
   (generated squash) clause, then walk its term/path binders, using weak-head
   queries on intervening applications, to select the first outer `Comp`.
   A head query can perform several contractions. These preparatory operations
   happen **before** this trace's counter starts. The selected term remains
   open in its recorded context. This is a focused diagnostic, not a replacement
   for normalizing the whole definition.

The tool also supports `squash`, starting at the entire generated clause.
Its first 50 rewrites mostly normalize binder annotations.

## Checkpoints against expectations

For the full function, all checkpoints through 50 remain in the annotation
`h : IsSet(U1, Prop(U0))` after the initial definition unfolds. That is expected:
full normalization visits a lambda's domain before its body, and this
cache-disabled trace spends 26 of its 50 events repeating earlier contractions.
The position at step 50 is consequently not a claim about 50 work steps or
50 unique contractions of the ordinary query. `IsSet` unfolds
through `HasLevel`; `Prop` unfolds to a sigma type and `IsProp` to dependent
functions returning paths. The body has not been evaluated at step 50.

For the body, step 1 removes an ascription's identity beta redex; step 2 unfolds
`descend`; step 5 is instantiating its parameters; step 10 has exposed its `q`
lambda. Step 20 is instantiating `quotient_induction`, whose generated clause
already contains four compositions. At step 50 the traversal is normalizing the
class clause's `unit_is_prop` proof. An open `q` correctly leaves an eliminator
application: neither mathematical constancy of the map nor the quotient's
setness lets the evaluator choose a representative or erase its clauses.

The focused transport trace reaches the expansion directly:

| Rewrites | Expected operation and observed state | Distinct syntax nodes | `Comp` | `Glue` |
| ---: | --- | ---: | ---: | ---: |
| 0 | Generated composition in a path type | 72 | 4 | 0 |
| 1 | Path composition becomes a path lambda with a new composition and endpoint walls | 80 | 4 | 0 |
| 2 | Eta removes a motive wrapper in the path lambda's annotation; its body is unchanged | 81 | 4 | 0 |
| 5 | Unfolding and level-instantiating `Prop` exposes a sigma type behind an identity ascription; ordinary beta is next | 90 | 4 | 0 |
| 10 | The annotation is `Σ (A : U0). ∀ (x y : A). Path A x y`; the body composition remains to be processed | 88 | 4 | 0 |
| 20 | Sigma composition has produced a pair: its first field composes in `U0`; its second composes in the proposition-proof family, using the first field's filler | 114 | 6 | 0 |
| 50 | Two universe compositions have become nested `Glue` types; traversal is inside a glued type's path annotation | 531 | 12 | 2 |

Counts include annotations and reachable witness syntax, not all allocated
arena nodes or expanded tree occurrences. Exact structural duplicates are
counted once; no alpha-equivalent or definitionally equal nodes are merged.
The diagnostic reconstruction at step 20 contains two exact copies of one
node, hence 114 distinct structures versus 115 reconstruction handles.

The decisive intervening rewrites are:

```text
16  comp-sigma      Comp (Sigma ...) ...  -> Pair(..., Comp U0 ..., Comp ...)
21  comp-universe   Comp U0 ...           -> Glue(...)
22  comp-path      Comp (Path ...) ...    -> PLam(..., Comp ...)
23  path-beta      PApp(PLam(...), ...)   -> Comp(...)
29  comp-sigma     Comp (Sigma ...) ...   -> Pair(...)
30  fst-pair       Fst(Pair(...))         -> Comp U0 ...
31  comp-universe  Comp U0 ...            -> Glue(...)
41–42              restrict the Glue-system type and equivalence to their face
```

These are abbreviated **shapes**, not full terms. The complete inputs, all 50
rule events, binder context, and reconstructed ASTs at 1, 2, 5, 10, 20 and 50 are
in [snapshots.json](quotient-normalization-trace/snapshots.json). Negative node
IDs reconstruct active parent frames outside the kernel arena. A snapshot is
an intermediate expression, never a completed normal form or typing judgement.
Each event's `enteredTerm` is the weak-head frame's input before prerequisite
head exposure, not necessarily the immediate syntactic redex.

## What is expected, and what remains suspicious

The [path and sigma composition rules](../../kernel/src/composition_compute.c)
explain the first two structural changes. The
[universe rule](../../kernel/src/glue_compute.c) explains the larger expansion:
for each wall it constructs a `Glue` component and an equivalence witness by
transporting the identity equivalence. Those witnesses contain further
compositions and their types contain dependent functions, sigmas and paths.
Thus a single correct rule application can make the graph substantially larger.
The second `Glue` appears while computing the first one's base; this is nested
transport work, not an immediately repeated beta redex.

A useful expectation would be that constant-family transport simply returns its
input. That is **not** a general definitional rule in this kernel. Moreover,
these compositions carry boundary systems: even a constant type family does
not justify dropping the walls. The project's
[path-algebra contract](../cubical/path-algebra.md) distinguishes propositional
transport equalities from judgemental computation. These checkpoints do not
justify adding proof irrelevance or a new regularity rule.

The unresolved issue is whether the general dependent squash construction and
universe-composition witnesses are creating avoidable, repeatedly reconstructed
syntax, or whether this chosen term genuinely has a large full normal form.
The first 50 rewrites distinguish neither completely. The earlier large-budget
[partial graphs](rational-normalization.md#partial-reductions) motivated selecting
the squash transport for this focused trace; the full/body prefixes do not
reach it independently. This trace demonstrates the expansion mechanism in
that selected subterm. It supports continuing the existing audit of generated
squash transports, their specialization to a constant motive, and
identity-equivalence construction/readback. A compact checked generic
construction or sharing improvement must preserve the existing computation
rules and full normalization contract. Lazy observation alone cannot establish
that this problem is fixed.

## Reproduction and checks

The diagnostic is deliberately an unapplied
[instrumentation patch](quotient-normalization-trace/instrumentation.patch),
plus a [probe](quotient-normalization-trace/probe.mjs). It adds no runtime API to
the normal build. Apply it only in a disposable checkout of this PR (the kernel
sources it patches are unchanged from `89f73ea1`):

```sh
git apply docs/reports/quotient-normalization-trace/instrumentation.patch
make wasm
node docs/reports/quotient-normalization-trace/probe.mjs full 50 /tmp/quotient-trace
node docs/reports/quotient-normalization-trace/probe.mjs body 50 /tmp/quotient-trace
node docs/reports/quotient-normalization-trace/probe.mjs transport 50 /tmp/quotient-trace
```

Each run checks a fresh program and writes JSON and a raw event/frame log.
Replace `50` with `1`, `2`, `5`, `10` or `20` to stop independently there.
The tool is limited to this fixture and the first 50 rewrites, not advertised as
an exhaustive tracer for every kernel rule. Uninstrumented Sum, declared-type,
and HComp/Trans reductions explicitly stop the diagnostic if reached; none is
reached in these prefixes. The ordinary syntax-depth guard,
recursion guard, ten-million-work budget and 30-second deadline remain in place.
Reaching the requested checkpoint deliberately stops the query with a diagnostic
error; the tool reconstructs the expression from saved frames instead of
publishing a partial answer through the kernel. The scoped subterm modes use
raw `_cb_normalize` on syntax selected from an already checked definition;
they intentionally bypass JavaScript's top-level derived-handle guard and
issue no new typing judgement.

The probe writes the raw per-run schema (including frames and reconstruction
handles), rather than overwriting the committed compact artifact. The artifact
was packaged from the three 50-event JSON files: event objects become
`[step, rule, before, after]` arrays, snapshots retain root and focus path,
and node objects become the rows specified by `nodeSchema`. The reported
`structuralNodes` count interns keys `(kind, payload, child structural keys)`
bottom-up, then counts distinct reachable keys from each snapshot root;
`compNodes`/`glueNodes` count those kinds in the reachable graph. No binder
renaming, unfolding or reduction is performed by this packaging step.
The `squash` runs were validated as below but are omitted from the compact
artifact; the committed probe regenerates their raw logs and ASTs.

All six independent limits were run for all four entry points (24 runs).
Every run matched its prefix in the 50-step trace and reconstructed every
active parent without an unmatched context. The first 50 focused rewrites use
791 work ticks and allocate 575 arena nodes; these diagnostic counters are
separate from its 531-node reachable partial term. They include cache-disabled
recomputation and the tracer's extra allocation to record face-restriction
snapshots; they must not be used as the cost of an ordinary query.
With tracing disabled, the
original fixed-budget control was unchanged: Unit completed in 5,117 work ticks
with 1,156 allocations; Prop exhausted ten million ticks with 2,028,800
allocations. This confirms instrumentation-off reproduction, not a performance
improvement or a proof that later normalization terminates.
