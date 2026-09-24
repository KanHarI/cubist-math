# Proof ergonomics: implementation plan and executable design examples

Implementation checkpoint: 2026-09-24. This refines the
[roadmap](proof-ergonomics-roadmap.md). The [example directory](../examples/proof-ergonomics/README.md)
pairs explicit current programs with native-checked new syntax. The remaining
scoped algebra fixture ends in `.cubist.proposed` and is exploratory. Read the
[tactical handoff](../tactical/proof-ergonomics-handoff.md) before extending the
implementation. No mathematical roadmap is resumed.

## Recommended order

Ship explicit calculation, deterministic rewriting, and small explicit simp
sets first. In parallel, develop expected-type path abstraction and pointwise
equality: these need known types, not general unification. Then add direct
dependent path conveniences before attempting dependent context replacement.
Keep general inference, rule search, and structure elaboration separate enough
to measure their costs independently.

The checked first slice covers parts of PRs 1–7 below. The remaining items in
those rows and PRs 8–11 are dependency-sized work packages, not estimates of
elapsed development time. The handoff records the exact supported fragment.

## What the current code actually provides

| Existing seam | Consequence for implementation |
| --- | --- |
| [`Translator.block`](../../lib/cubical/translate.mjs) recursively translates the remaining statements, wrapping introductions in lambdas and checking local `have` proofs | Preserve this continuation model for one residual goal. A multi-goal scheduler is unnecessary for the first `rw` and `simp`. |
| [`NativeCubicalElaborator`](../../web/cubical-elaborator.mjs) supplies `infer`, `check`, `nf`, `equal`, `expect`, and `ascribe` | `nf` exposes the native **head**, not a full normal form. `equal` tests conversion; `expect` permits directed cumulative typing. Use each deliberately. |
| `sym`, `trans`, and `cong` preserve compact signatures using a checked identity application; [`path-algebra.mjs`](../../lib/cubical/path-algebra.mjs) supplies inert path builders | Factor shared builders and checked signature wrappers; do not independently reimplement their semantics for tactics. |
| Ordinary application propagates argument types, but eagerly infers its growing application spine | Add application-spine elaboration with a known signature before adding broad inference. Repeated native inference may otherwise consume any savings from shorter source. |
| `path`/`PathP`/`comp` bind dimensions separately from terms; `FunExt` already constructs a cubical path of functions | Expected-type path notation and pointwise equality can be small elaborator extensions with ordinary core output. |
| [`CubicalProgram`](../../web/cubical-program.mjs) records source references, qualified definitions, universe specializations, and assumptions | Automation traces need new records for transitions and generated witnesses; existing reference records alone are insufficient. |
| [`benchmark-runner.mjs`](../../web/benchmark-runner.mjs) owns native checkpoint/rollback/compaction and JS cache cleanup | Extract reusable declaration transactions. Ordinary translation catches errors but does not provide the benchmark's full transaction behavior. Do not promise statement rollback merely because an error is caught. |
| [`build-cubical-runtime.mjs`](../../tools/build-cubical-runtime.mjs) explicitly lists copied runtime modules | Add every new shared module to that list. Never edit generated `web/dist` copies as a second implementation. |

The roadmap's `finite_counting` module no longer exists. Use
[`finite_dependent_counts`](../../web/proofs/finite_dependent_counts.cubist),
particularly `finite_uniform_fiber_count`, for its finite-counting baseline.

## PR-sized work packages

| PR | Depends on | Concrete change | Acceptance evidence |
| --- | --- | --- | --- |
| 1. Baselines and syntax conveniences | — | Preserve selected statements/assumptions; grouped `intro`, grouped typed binders, typed multi-binder lambdas, `have h = e;`, and `have h : T := e;`. Expected-type untyped lambdas only with a known Pi. | Current/future paired examples; AST-equivalent explicit expansions; binder shadowing, comments and inspector spans. A pair without an inferable type still needs an annotation. |
| 2. Reconstruction and transactions | 1 | Add single-goal transitions, shared checked path constructors, and reusable declaration transactions. Initially exercise transitions through internal APIs. | A checked proof of the new goal reconstructs a checked proof of the old one; failed declarations discard generated helpers and rules; previously accepted declarations remain usable. |
| 3. `calc` and `rfl` | 2 | Terminal homogeneous `calc` statement; subsequent `_` means previous right endpoint; step justification is a term or nested proof block. `rfl;` emits a constant path and asks the kernel to check it. | Arithmetic chain fixture checks. Wrong intermediate endpoint/carrier fails at that step; nested `by { ... }` supports the following PR. |
| 4. Explicit `rw` | 3 | Fully instantiated homogeneous paths; ordered rules, reverse direction, `at lhs`/`at rhs`, one-based `occurrence n`; root and fixed-codomain application contexts. | Forward/reverse/congruence fixtures; occurrence order and dependent-context rejection; complete witness visible from the source selection. |
| 5a. Ground `simp only` | 4 | Explicit instantiated rules; bottom-up traversal, endpoint witnesses and residual goals; work budgets and cancellation. | Nested example, residual goal subsequently closed by `exact`, wrong proof rejection, cycle diagnostic. |
| 5b. Quantified `simp only` | 5a | Rigid first-order rule matching with dependent parameter types checked in telescope order; cache rule shapes by checked binding identity. | `simp only [nat_add_zero];`, repeated-variable rejection, underdetermined argument diagnostic, no full unfolding of large endpoints. |
| 6. Expected-type cubical notation | 2; independent of 4–5 | `path i => e`, `p @ i`, and `ext x;` for homogeneous equality of dependent functions. Preserve the explicit two-argument `path`. | Native-checked path, pointwise and naturality-square examples, wrong faces and captured dimensions rejected; nested path source inspection. |
| 7. Directed dependent movement | 6 | `along C by p from v`, direct `apd_path(f,p)`, expected-type `over C along p by { ... }` transport bridge. | Match the checked dependent examples; bridge work occurs only on request; loop-dependent transport and inverse laws retain witnesses. |
| 8. Rule environments and broader `simpa` | 5b | Checked registrations, imported/named sets, deterministic priorities, explicit exclusions, fresh simplified equality-hypothesis copies, conditional equality rules with selected/reflexive witnesses, depth-two checked equality-premise simplification, checked type-path transport for `simp`/`simpa`, lexical rule scope for universe templates, and a residual-goal-validated freeze action are implemented. General proposition premises and map-based proposition simplification remain. | Deterministic imports, no leaked local rules, minimal assumptions, false premises rejected, freeze-to-used-rules action. |
| 9. Scoped argument inference | 2, evidence from 5b/6 | Named arguments, scoped term metavariables, restricted unification, `_`, opt-in implicit binders, then universe constraints. | Omitted endpoint/carrier examples, occurs/scope checks, ambiguous universes rejected, inspector shows solved arguments. |
| 10. Multiple goals and dependent rewriting | 7, 9 | `apply`/`refine`, expected motives, selected dependent congruence and telescope reconstruction. Constructor-specific cubical support follows separately. | Recheck all downstream hypotheses; transport proof-dependent indices; reject unsupported HIT boundaries; no unsolved term reaches native encoding. |
| 11. Structure views and selected automation | 8, 9, migration evidence | Lexical notation packs and named views of existing Sigma structures, then records/sections; certified algebra normalization separately. | Field/group examples preserve expanded signatures and assumptions; nested scopes restore notation; no global instance search. |

Each PR includes its parser/formatter, native acceptance/rejection, and source
inspection coverage. Add its syntax to `web/language.html` only when delivered.
Do not mark the original milestones complete because these designs exist.

## Freeze these semantics before implementation

### Surface syntax and source preservation

Keep syntax nodes for new constructs until elaboration, with spans for each
binder, rule, direction marker, endpoint, and justification. Desugaring should
also retain the originating node so an inspector can display both the short
source and its expansion. Follow the existing tuple macro's expansion records.
The formatter must compare elaborated macro shapes where parser sugar changes
AST shape; it must not drop comments or turn a checked construct into a different
one when formatting.

Choose `have h : T := e;` rather than `have h : T = e;`: the latter is
ambiguous when `T` itself is an equality. Add `:=` and `<-` as tokens, then `@`
in PR 6. Keep ASCII canonical initially. Optional Unicode aliases can later
render path concatenation as `p · q`, inversion as `p⁻¹`, and transport as
`p_* v`, with explicit elaborated meanings and precedence tests.

Elaborate the shared domain of `(x y : A)` in the surrounding scope before
binding either name. Sequentially reparsing that domain after binding `x`
could change its meaning under shadowing. Generated inspector identities need
an origin span **and** expansion index; several generated nodes at one offset
must not overwrite one another.

`calc` is terminal in its block. Every step has the same carrier, determined
from the expected equality or first endpoint; later endpoints must check in it.
An omitted left endpoint is a reference to the preceding expression, **not** a
metavariable. Build a specified left-associated composition of step witnesses
and retain that association in inspection. Different proof association is not
assumed judgmentally equal.

In a `calc` step, `by term;` ends with a semicolon; `by { statements }` ends
at the closing brace, matching the existing block-style `have` convention.
For `p @ i`, application binds more tightly than equality and arithmetic;
parenthesized calls bind more tightly than `@`, which associates left to right.
The right operand is interval syntax and is checked in the dimension namespace.

For `rw [p, <- q] at lhs occurrence 2;`, each rule uses the indicated occurrence
in the **current** endpoint after preceding rewrites. A missing occurrence is
an error. Without a target, visit left endpoint before right endpoint. Within
an endpoint use preorder, outer applications first, then function and argument
left to right; count only eligible typed matches. Crossing an unsupported
dependent context gives an explanation and its source span. Do not search
inside the carrier, named definition bodies, binders, or composition systems.
Omitting `occurrence` selects 1. Reverse syntax reverses the witness.

`rw` may close the residual goal by conversion; therefore an example that
rewrites directly to reflexivity must not append an unreachable `rfl;`.
`simp only` always permits kernel conversion and administrative computation
needed to expose a type head. It supplies no hidden theorem rules. Rule matching
starts with folded heads, beta-redexes/projections and explicit unfolding hints;
no library-wide normalization pass runs before matching.

### Single-goal reconstruction, without kernel holes

Suggested new modules under `lib/cubical/`:

```js
// Proposed interfaces; these are not implemented exports.
// Scope is immutable and contains term telescope, aliases, dimensions,
// face restrictions, universe specialization and unfolding policy.
Goal = { target, scope, sourceSpan };
Transition = { nextGoal, rebuild, trace }; // rebuild : proof(next) -> proof(old)
RewriteResult = { before, after, carrier, witness, trace };
Rule = { binding, specialization, parameters, lhs, rhs, carrier,
         direction, premises, priority, sourceSpan };

// proof-goals.mjs
advance(goal, transition); // continuation composition; no unresolved core term
finish(goal, proof);       // check current proof, rebuild, check original proof

// proof-rewrite.mjs / proof-match.mjs / proof-simp.mjs
rewriteAt(term, rule, selector, scope, budget); // -> RewriteResult
compileEqualityRule(checkedLemma, scope);
matchRule(rule, checkedSubject, scope, budget);
simplifyEndpoint(term, ruleSet, scope, budget); // -> RewriteResult
```

Keep syntax immutable and preserve `DefRef` nodes and DAG sharing. These
interfaces pass core syntax, not long-lived raw native handles. A JavaScript
record labeled `checked` is bookkeeping, never a certificate.
The scope's face field is initially only the unrestricted face: the current
native query adapter accepts dimensions and a telescope, not a caller-supplied
face restriction. Restricted-face automation requires a separate adapter design.

For a goal `l =[A] r`, suppose simplification produces
`p : l = l'`, `q : r = r'`, and the remaining goal is `l' = r'`.
Reconstruct its solution `s` as `trans(trans(p, s), sym(q))`. Check the endpoints
and homogeneous carrier before building it; keep the resulting signature
compact. A rewrite at the right endpoint must use the inverse witness during
reconstruction. This formula also explains why endpoint replacement alone is
insufficient.

To lift a rewrite through a fixed-codomain application context, construct a
typed one-hole lambda and use `cong`. Reject the context if its result type
depends on the hole. Do not infer nondependence from visually identical source
types. Later dependent lifting returns transport or a `PathP`, not this API's
homogeneous `RewriteResult` by fiat.

Surface builtins can hide unsupported core constructors: `transport(...)`
lowers directly to `Comp`. PR 4 cannot descend to its apparent source arguments
just because its overall result fiber is fixed. Supply explicit `cong`, wrap
the operation in a named function and rewrite an ordinary application, or defer
that position until a checked constructor adapter exists.

Commit source traces only when their enclosing declaration succeeds. On failure,
restore native allocations/definitions, universe specializations, assumptions
created by the attempt, unfolding helpers, source records and rule registrations.
Extract and audit the benchmark transaction instead of copying it: it does not
currently cover all the future state listed here. Use one owning declaration
transaction; speculative matchers should avoid creating global definitions.
Nested checkpoint support is not assumed.

### Rule matching and resource control

The first quantified matcher handles applications of rigid names to parameters,
constructors, and repeated parameters. Treat binders, dependent paths, Glue and
HIT systems as unsupported match contexts. Instantiate parameter types in order,
using the subject's checked carrier to constrain type parameters. Native-check
the completed lemma application. A repeated variable requires conversion with
its previous assignment, not another assignment. No higher-order synthesis of
functions from their values is attempted.
The core's `Path` tag covers both equality and PathP. Conservatively reject a
rule whose family contains its bound dimension; having tag `Path` alone does
not establish homogeneity. Reuse `freeDimensions`, `substituteTerm` and
`substituteDimension`, including their capture-avoidance behavior.

If a parameter occurs only on the right or in an unselected premise and cannot
be determined, request an explicit instantiation. A rule proof argument used
by its conclusion must retain its exact selected witness. Match caches may not
identify different proofs merely because their endpoints agree.

Index rules by folded head and carrier shape; try explicit lists in source
order. At each node, simplify children, then try root rules in that order; after
a rewrite restart at the resulting node. Compare states by scoped structural
identity with collision checks, never by arbitrary equality of inhabitants.
Reject/diagnose cyclic rule applications even if intermediate endpoint goals
could be closed. Conversion closes only after the requested simplification
finishes successfully.

Thread a shared budget through matching, traversal, witness construction and
native queries. Count visits, attempted matches, applied rewrites and distinct
generated DAG nodes. Set numerical defaults after measuring the PR 1 corpus;
record them in a test fixture. Poll the existing native deadline and a host
cancellation signal at bounded intervals. Browser worker termination remains
the fallback if synchronous work cannot observe a queued cancellation message.
Report budget exhaustion as an unfinished proof, with the last rule and residual
goal; do not silently return partial success.

Start with declaration-local caches. Cross-declaration reuse requires keys
including checked rule identities, specialization, context, dimensions/faces,
unfolding policy and a native arena generation. Clear/remap entries on rollback
or compaction. A cached rewrite includes its witness.

PR 8 now uses `simp_rule nat_add_zero;` and
`simp_set nat_units = [nat_add_zero];`. Registration validates checked
homogeneous equality types, exports qualified rule identities through imports,
resolves explicit set names lexically, de-duplicates rules and orders defaults
by priority then identity. Local hypotheses enter only through explicit lists.
`simp ... at h as h2;` binds a fresh checked equality copy instead of replacing
dependents. Conditional equality premises use selected local witnesses,
conversion/reflexivity, or depth-two simplification by other selected rules.
Active rules are excluded, and the resulting premise path is checked. For a
non-equality goal, `simp` can rewrite its type at the root or through ordinary
fixed-codomain applications and transport a following proof back along the
checked type path. `simpa` similarly simplifies both the supplied proof type
and goal, transports the proof to their common type, checks it, then transports
back. Homogeneous equality goals retain endpoint reconstruction. Arbitrary
logical equivalences and proposition-specific conversions still need explicit
checked maps; these are not inferred from two functions.
Rule selection is children first and then source order at each node. A rigid
shape match with a mistyped inferred argument is ineligible, so another rule
can still prove the goal. A universe template uses the simplification sets
captured where it was defined, including during source inspection. The freeze
action withholds a reduced `simp only` list if replay changes either residual
goal; this matters when an omitted rule affected a failed premise search.

### Application elaboration and PR 9 inference boundary

Introduce a synthesis result `{ term, type }` for an application spine. Infer
the head once; for each supplied argument expose the next Pi, check the argument
at its domain, and substitute it into the result type using capture-avoiding
substitution. Retain a final native check of the complete application. Benchmark
native query counts as well as elapsed time with reuse enabled and disabled;
this optimization is useful even when all arguments remain explicit.

PR 9 extends that spine with frontend-only metavariables. Each variable stores
its creation telescope, dimensions, expected type, universe constraints and
source span. First solve rigid first-order constraints from supplied arguments
and the expected result; accept a solution only after occurs, scope and native
type checks. Postpone blocked constraints to a worklist; report unsolved or
ambiguous constraints at the call site when no progress remains. No kernel
encoding or declaration commit is allowed with an unresolved variable.

Named arguments require binder-name metadata from source signatures; generated
fresh core names are not a stable public API. Explicit arguments remain the
fallback. Universe cumulativity yields inequalities, not unique solutions:
infer only a determined specialization in the first version, and request an
explicit universe otherwise. A later documented principal-universe policy
would be a separate change. Interval coordinates and faces are not ordinary
term holes. Type-directed argument completion must never instantiate a path
witness merely because some inhabitant of its endpoint equality exists.

## Cubical language changes worth prioritizing

### 1. Expected-type paths and pointwise equality — high priority, small search cost

For a known `PathP(i => A(i), a, b)`, elaborate `path i => body` by reusing
the expected family, checking `body : A(i)`, and emitting `T.line`. The kernel
checks its endpoint restrictions. For `f = g` at a known dependent function
type, `ext x;` changes the goal to `f(x) = g(x)` and reconstructs
`path i => fun x => h(x) @ i`, with explicit domains/family in generated core.

This is geometric abstraction with no lemma search. It works for dependent
functions over the same domain/family, but does not automatically prove an
arbitrary dependent path between varying function types. Existing `FunExt`
already gives the required construction. An explicit `path(family, body)` is
the remedy when no expected family is known.

The frontend's `dimensionBody` still counts enclosing dimensions despite the
codec/kernel's liveness improvements. Add a frontend nesting regression and
address that allocation separately if it limits real examples; never reuse a
dimension needed by a local variable's type. Dependent path reversal also
requires reversing the family: the current `sym` implementation assumes a
constant carrier and is not a generic PathP inverse.

**Hypothesis to measure:** fewer repeated family elaborations and fewer native
queries for manually supplied `FunExt` parameters. The checked proof need not
be smaller than the existing direct cubical expansion.

### 2. Keep dependent proofs as paths until transport is actually needed

Given `p : x = y` and `f : forall a : A, C(a)`, expose
`apd_path(f,p) : PathP(i => C(p @ i), f(x), f(y))`, lowering directly to
`path i => f(p @ i)`. Preserve existing `apd`, whose result is equality **after
transport** and which currently invokes the path-over bridge.

`along C by p from v` abbreviates the existing
`transport(C, x, y, p, v)` using the checked endpoints of `p`. The family stays
explicit: inferring an arbitrary family just from its endpoint fibers is not
well determined. `over C along p by { ... }`, checked against a known PathP along `p`,
opens the transported-equality goal and lowers to `path_from_transport`.
It checks `C` as a type family, infers `x,y` from the homogeneous path `p`,
and verifies that the expected interval family converts to `C(p @ i)`.
For expected endpoints `a,b`, its subgoal is `transport(C,x,y,p,a) = b`.
There is no higher-order recovery of `C` from the expected family. The existing
explicit `path_from_transport` remains available for a general interval family.

**Hypothesis to measure:** APIs accepting PathP directly avoid constructing
bridge conversions at intermediate steps. Do not install both bridge directions
as simp rules or claim their round trips compute to identity; the library
provides higher paths witnessing them.

### 3. Naturality squares as nested paths — high priority, no new primitive

With `H : forall a : A, f(a) = g(a)` and `p : x = y`, write the square as
`path j => path i => H(p @ i) @ j`. Its outer family is
`H(x) @ j = H(y) @ j`; the outer endpoints are `cong(f,p)` and `cong(g,p)`.
This states the two-dimensional object directly rather than first choosing a
concatenation equation. The sample includes its full current-language expansion.

Use the expected nested PathP to display all four edges and corner checks in
the inspector. A later `square` notation can name those edges, but should be a
view of this type, not a new square solver. Four arbitrarily supplied boundary
paths need not have a filler; boundary compatibility at corners alone is not
proof of filling. Conversion between a square and a concatenated-path equation
needs a checked construction.

### 4. Boundary-oriented box notation — useful after PR 6

Replace deeply nested `face(..., fun (...) => ...)` only with an explicit box:

```text
// Proposed syntax, checked under an outer live coordinate i.
compose j in A from p @ i {
  on i = 0 => x;
  on i = 1 => q @ j;
}
```

For `p : x = y`, `q : y = z`, this lowers to the current `comp` family/base
and two faces. The composition direction binds the family and tube bodies,
not the faces or base. Generalize `A` to an explicitly written varying family
only with the same scoping rule. No missing walls are silently guessed. Native
checking must validate face overlaps and base agreement, including restricted
local-variable types. A separate `fill` form can expose the existing derived
filler at a specified coordinate. Do not generalize from boxes to arbitrary
closed boundary filling.

### 5. Mathematical structure scopes and named Sigma views

Before new record representations, support lexical notation packs backed by
ordinary terms. The proposed field example chooses its structure once and
binds `+`, `*`, `zero`, and `one` to known field operations. The translator
already resolves natural-number `+` through the lexical `add` binding; make
this mechanism explicit and inspectable instead of adding typeclass search.

Keep the structure scope around the **statement and proof**, and expand its
operation bindings at declaration boundaries. Do not create implicit coercions
between fields or overload numerals until a particular interpretation has been
specified. A qualified pack identity and its expansions belong in the inspector.

Named views can map existing structures to their checked projections (for
example `F.carrier`, `F.add`, `F.add_assoc`) without changing public Sigma
representations. A later record literal checks fields in dependency order and
lowers to the existing pair type. Equality of records with proof-dependent
fields still needs the appropriate paths/coherences; fieldwise comparison must
not discard those fields.

### 6. Goal-derived induction and coherent structure equality — later

An induction statement can abstract the target over its selected scrutinee,
provided dependencies are generalized explicitly and uniquely. Present the
resulting motive before checking branches. For pushout/suspension elimination,
offer point and PathP bridge branches together; goal inference must never drop
the bridge branch. This pairs especially well with `path i =>` and `over C along p`.

An `ext using lemma` facility can turn equality of structured maps into the
obligations of a selected checked lemma. Automatically solving those obligations
requires actual `IsProp`/`IsSet` evidence in the relevant fibers. No rule may
erase an arbitrary loop or choose a unique transport witness in a general type.

Defer unrestricted higher-order unification, global coercion/instance search,
automatic univalence, and general-purpose boundary solving. The priority here
is predictable source-to-proof construction with fewer redundant parameters.

## Measurement and release checks

The initial [source/benchmark snapshot](../examples/proof-ergonomics/baseline.json)
selects `nat_add_assoc`, `right_unit`, `finite_uniform_fiber_count`,
`group_conjugate_multiply`, and `field_scalar_laws`. It records source tokens
using the current tokenizer, native checking steps, rewrite candidate work,
final-check arena snapshots and one timing observation; it is not a speedup
claim. The selected import graph checked 497 concrete declarations and 24
templates with no failed, blocked or timed-out entries at a 1 s limit.
The separate [rewrite-work snapshot](../examples/proof-ergonomics/rewrite-work.json)
checks 19 paired explicit and ergonomic declarations, including conditional
premise search, with inspector references disabled.

Before PR 1 completion, extend measurement to repeated explicit carrier/endpoint
arguments, aggregate reduction-step deltas, generated DAG size, peak temporary
arena use and retained arena use after compaction. The benchmark now records
per-declaration native checking-step deltas and attempted rewrite traversals;
`infer().native.arenaNodes` is still a cumulative session snapshot, not a
per-declaration peak or delta. Record instrumentation definitions, source
revision, options and machine. Use repeated runs with warm-up, medians and
variance; preserve the raw samples. Compare statement types by native conversion
and explicit assumption lists. Recheck proof-dependent consumers as well.

Separate three questions: how much source authors write; how much matching and
elaboration work happens; how much generated proof the kernel checks. A shorter
source with slower matching is not automatically an optimization. Conversely,
an inferred family that produces the same core can still materially improve
proof authoring.

| Feature | Mandatory rejection/regression examples |
| --- | --- |
| Reconstruction | `0 = 1`; reversed right-endpoint witness; wrong carrier; residual goal left unsolved |
| Matching | repeated parameter assigned inconsistently; parameter only on RHS; premise requiring itself; deterministic explicit-list cycle |
| Cubical scope | interval used as a term; dimension escaping path binder; equality valid only on a face reused globally; bad square edge |
| Dependent movement | wrong fiber; transport along distinct loops identified without a witness; `cong` used on a dependent result |
| HoTT | `p : x = x` simplified to `refl(x)` without a higher path; untruncated witness extracted from `Truncate(A)`; maps treated as arbitrary type equality |
| Infrastructure | failure after generated specialization; rolled-back handle reused; same spelling imported from different modules; changed rule reused from cache |
| Performance | large folded endpoints from path-over tests; selective-unfolding regression; cyclic rules; cancellation during matching and checking |

Run focused parser/formatter/native/inspector tests in the implementing PR,
then the existing corpus and browser checks for releases. Relevant commands:

```sh
node tools/build-cubical-runtime.mjs
npm test -- tests/cubical-program.test.mjs tests/unfolding-syntax.test.mjs
npm test -- lib/cubical/tests/path-over.test.mjs lib/cubical/tests/dimension-slots.test.mjs
npm test -- primes paths finite_dependent_counts group_operations field_vector_spaces
npm run test:browser
make lint
npm test
```

The example README records the checks actually run for this planning change.
The commands above are future implementation gates, not claimed results.
No native rule changes are planned; run the relevant C tests/sanitizers if a
later transaction or adapter change touches native ownership or checking.

## Design precedents

Cubical Agda's [official cubical documentation](https://agda.readthedocs.io/en/latest/language/cubical.html)
illustrates interval path abstraction, function extensionality, partial faces,
and open-box composition. These motivate the surface designs; Cubist's own
kernel and existing builders determine their actual semantics.
Its [Path library](https://github.com/agda/cubical/blob/master/Cubical/Foundations/Path.agda)
also exposes a dependent-path/transport comparison. Cubist already has its own
[checked bridge](../cubical/path-over.md), so no external computation rule is
assumed. These are precedents, not a proposal to import another checker.
