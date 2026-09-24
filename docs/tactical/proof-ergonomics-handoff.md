# Proof ergonomics implementation checkpoint

Date: 2026-09-24. This is the implementation handoff for the
[roadmap](../roadmaps/proof-ergonomics-roadmap.md) and
[implementation plan](../roadmaps/proof-ergonomics-implementation-plan.md).
The feature is in progress. All accepted example declarations are checked by
the C/WASM cubical kernel and report no axiom dependencies.

## Implemented source fragment

- Grouped `intro x y;`, grouped typed declaration/quantifier/lambda binders,
  including consecutive `Universe` schema parameters,
  expected-type `fun x => ...`, `have h = e;`, and `have h : T := e;`.
- Terminal homogeneous `calc { lhs = rhs by proof; _ = ... by { ... } }` and
  `rfl;`. Each step has an actual checked path; `_` means the preceding right
  endpoint only inside `calc`.
- `rw [p, <- q] at lhs occurrence 2;` (or `at rhs`) on homogeneous equality
  goals. Rules are fully instantiated paths, applied in source order. The
  default target counts eligible occurrences across left then right, skipping
  unsupported dependent positions before trying the right endpoint. Eligible occurrences use preorder
  through ordinary `App` nodes only. Each fixed result type context is checked
  as a one-hole function before path congruence is constructed.
- `simp only [rules];` and `simpa only [rules] using proof;` for explicit instantiated or rigid first-order
  universally quantified homogeneous equalities. It visits children before
  parents, left goal endpoint before right, source rule order at each node.
  `simpa` simplifies the supplied equality type and goal, then uses checked
  endpoint paths to reconstruct the original goal. All inferred rule parameters
  must occur on the matched side. A rigid syntactic match with an incompatible
  parameter type is skipped so later rules remain available. Cycle, missing
  match, unfinished residual goal, traversal, rewrite-count and generated-term
  bounds cause failure.
- For other type-valued goals, `simp` rewrites the type along checked paths and
  transports a following proof back to the original goal. `simpa` simplifies
  the supplied proof type and target type, transports the proof to their common
  type, checks it there, and transports it back. Root rewrites and ordinary
  fixed-codomain application contexts are supported; arbitrary maps between
  propositions are not synthesized.
- `simp_rule lemma priority 10;` registers an already checked homogeneous
  equality for deterministic default simplification. `simp_set units = [lemma];`
  names an explicit collection. Registrations and sets flow through imports;
  duplicate default rules collapse by checked identity, sorted by descending
  priority and then identity. Conflicting imported set names are ambiguous until
  locally overridden. Universe templates retain the rule environment from
  their definition when specialized or inspected. `simp;`, `simp [units];`, `simp only [units];` and the
  corresponding `simpa ... using proof;` use those environments.
  `simp without [lemma];` removes a default rule; `simp [units] at h as h2;`
  binds a checked simplified copy of local equality proof `h`. Conditional
  equality rules can use an explicitly selected local witness through
  `simp with [h];`, a premise proved reflexive by conversion, or a homogeneous
  equality premise simplified by other selected rules. Premise search has a
  depth-two limit, 64-attempt budget and shared elapsed-work deadline; active
  rules cannot justify themselves. The generated witness is checked and passed
  to the theorem. Premise rules appear in the inspector trace and frozen
  `simp only` list. Arbitrary proposition-premise solving remains open.
- Expected-type `path i => body`, path application `p @ i`, `ext x;` for equality
  of functions with a fixed Pi carrier, `along C by p from v`, `apd_path(f,p)`,
  and `over C along p by { ... }`. The last form requires an explicitly chosen
  family and checks its transport-equality proof before applying the existing
  PathP bridge. Existing `apd` keeps its transported-equality result.
- A shared declaration transaction now checkpoints native checking for normal
  program loads as well as benchmarks. Successful definitions are relocated
  after compaction; failed attempts remove new definitions, specializations,
  assumptions, and encoded-handle caches. Source references for `calc`, `rw`,
  and `simp` link to their checked constructed witness; `calc` also links each
  checked step with a distinct expansion identity. The simplifier likewise
  exposes each checked rewrite path and selected rule in the inspector. Its
  “Replace with simp only” action preserves rule order, lists only rules that
  fired, and rechecks the edited source. Before offering a reduced list, the
  elaborator also repeats simplification with just those rules and requires the
  same residual goals and constructed proof up to conversion. This applies to
  `simp at`, `simp`, and `simpa`: later steps may depend on any of their paths.
  A changed conditional premise search withholds the action. It is unavailable
  when a used imported rule has no visible name in the current scope, or when
  a named simplification set would shadow an emitted rule name.

The actual checked source files are [arithmetic](../examples/proof-ergonomics/implemented/arithmetic.cubist),
[cubical](../examples/proof-ergonomics/implemented/cubical.cubist),
[dependent](../examples/proof-ergonomics/implemented/dependent.cubist),
[registered simplification](../examples/proof-ergonomics/implemented/registered-simp.cubist), and
[type transport](../examples/proof-ergonomics/implemented/type-transport.cubist). Their
explicit predecessors are in the adjacent `current/` directory. The scoped
algebra notation file remains exploratory.

## Soundness boundaries and remaining work

No new C rule was added. Rewriting does not descend into binders, dependent
applications, composition, Glue or HIT data. In particular, source
`transport(...)` lowers to `Comp`; rewriting one of its apparent arguments is
outside the early `rw` traversal. Use an explicit checked `cong` context or a
named function wrapper. Rewriting a hypothesis and all dependents,
proposition-specific maps, logical equivalences, and arbitrary PathP reversal
remain open. Non-equality goals can already be rewritten where an actual
checked path equates their types.

The current simplifier uses explicit or registered rules, a 64-rewrite cap, a
512-node traversal cap and an 8,192-candidate cap per traversal. Cycle-state
serialization polls the deadline and stops at a bounded expanded size, even
when the core term is a compact shared DAG.
It has bounded equality-premise search but no broader proposition simplification. The
source inspector shows the completed checked witness, individual calculation
and rewrite steps, and selected rule spelling.
Failures in an explicit `rw` or `simp` list now point to the selected rule's
source span, including a leading `<-`. A matched conditional rule with no
checked premise witness reports which parameter blocked it and suggests
`simp with [name]`. Imported default rules have no rule token in the current
file, so their failures still point to the `simp` statement. Subterm-specific
candidate spans remain unavailable because normalized core terms do not carry
source offsets. For a failed statement, the declaration itself is rejected;
no metas or subgoals enter the kernel.

The frontend still allocates interval slots for lexical nesting in
`Translator.dimensionBody`; deeper liveness support needs its own regression.
The current native query adapter has no public caller-supplied face restriction,
so automation remains at the unrestricted face. No unrestricted higher-order
unification or arbitrary `C` inference is claimed by `over`.

An experimental application-spine change reused a syntactically substituted
Pi codomain after every argument. One selected import-graph run rose from
0.64 s to 1.23 s (497 checked declarations in each run), so that change was
reverted. These single observations are enough to reject that implementation,
not to establish a general timing ratio. Further work should try lazy,
shared codomain substitution and count native queries and DAG size.

The selected 28-module baseline now records per-declaration native checking
steps, rewrite-work counters and a final-check arena snapshot: 497 checked
declarations and 24 templates. A separate explicit/ergonomic workload checks
19 example declarations and records every attempted rewrite traversal and
candidate visit, including failed matches and premise search. For example,
`add_zero_twice_simp` has 25 source tokens, 13 candidate visits and 309 native
checking steps; its 35-token explicit predecessor has 115 checking steps in
this one observation. Arena snapshots are cumulative kernel state, not
per-declaration allocation. Next implementation items: measure arena deltas
on selected real proofs and add explicit checked proposition-map support where
no path of types is available. General
named/implicit arguments, `apply`/`refine`, dependent hypothesis replacement,
scoped records/notation and certified algebra normalization follow the PR
dependencies in the implementation plan. Recheck assumptions and public theorem
types before migrating existing proofs.

## Verification recorded for this checkpoint

```sh
node tools/build-cubical-runtime.mjs
npm test -- tests/proof-ergonomics.test.mjs tests/cubical-program.test.mjs tests/cubical-benchmark.test.mjs
npm test -- docs/examples/proof-ergonomics/current/*.cubist docs/examples/proof-ergonomics/implemented/*.cubist
npm test
npm run test:browser
npm run build:site
npm run test:site
make lint
```

The focused JS suite checked native acceptance, formatter roundtrips, reverse
and selected occurrence rewrites, dependent-position rejection, cycles, false
equalities, nontrivial-loop preservation, and a rejected malformed naturality
square. It also checks imported rule scope, ambiguous named sets, exclusions,
conditional witnesses, and fresh simplified hypothesis copies.
The standard formatter and program/benchmark tests passed in the same session.
The full suite passed 326 tests and checked all 3,766 concrete corpus
declarations and 44 templates without failed, blocked, or timed-out items.
The five implemented source files checked 30 declarations without axioms; the
six explicit counterparts checked 19. The inspector browser suite, static
site browser suite, and `make lint` also passed. The rule-diagnostic test checks
source spans for `rw`, invalid `simp` rules, and missing conditional premises. The benchmark
test checks that successful declarations report native steps and arena
snapshots, while its rejected sample declarations report no final-check snapshot.
The nested-premise test checks two levels of native-checked witness
reconstruction through both `simp` and `simpa`, and rejects missing base rules
and self-justification.
The benchmark regression also checks local `simp with` and `simp at` examples
with inspector references disabled; local witness scope is independent of
source-link collection.
The type-transport test checks both directions of a supplied path of types,
rewriting beneath a type-valued family, a frozen `simpa only` replay, and
rejection of unrelated maps and cyclic type rules.
Four review regressions now cover children-first rule selection on equality and
type goals, skipping an incompatible quantified candidate, lexical rule scope
in universe-template specialization and inspection, and withholding a freeze
whose reduced rules change conditional premise search.
Further regressions reject truncated grouped binders and introductions without
hanging, and withhold `simp at`, `simp`, and `simpa` freezes that change a path
even when its residual equality or type goal is unchanged. Equality and
type-path cases cover both `simp` and `simpa`; reduced lists that preserve the
witness still appear, and their edited source checks.
Additional review regressions check shared-term size limits, rule/set name
collisions in frozen edits, grouped universe specialization, default `rw`
selection past a dependent position, and distinct inspector bindings for
template calculation steps and their source endpoints.
