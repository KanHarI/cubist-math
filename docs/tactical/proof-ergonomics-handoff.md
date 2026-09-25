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
  A source `fun` token with several binder groups opens the complete checked
  function in the inspector. Template source links include names introduced by
  `ext` and `simp ... at h as h2`, including their later uses.
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
  depth-two limit and shares the enclosing search's time limit. Each distinct
  premise is searched once per simplification; after 64 searches the rule just
  does not fire. Active rules cannot justify themselves. The generated witness is checked and passed
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
  and `simp` link to their checked constructed witness; each `calc` step's `by`
  keyword links to that checked step with a distinct expansion identity. The simplifier likewise
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
and rule-identity serialization poll the deadline and stop at a bounded expanded
size, even when the core term is a compact shared DAG. Rule selection and
exclusion apply this bound before comparing or compiling local rule identities.
Quantified rule parameter scanning visits each shared pattern node once and
checks the same selection deadline. An untyped lambda without an expected
function type reports a normal diagnostic, including inside a universe template.
The simplifier has bounded equality-premise search but no broader proposition
simplification.
Path composition and the other cubical syntax builders now preserve compact
shared terms while replacing native references and reserving binder names.
Composition uses the active proof deadline and an explicit syntax-size bound;
compact, deeply shared equality witnesses no longer expand into exponential
trees during `rw`, `calc`, `simp`, or `simpa` reconstruction.
Core free-variable scans and term/interval substitution now visit each shared
syntax node once per operation. This also keeps expected-type `path` and the
`over` transport bridge compact while retaining capture avoidance under
different binders.
The inspector's path-notation dependency scan also memoizes shared syntax and
has a display-work limit. Raw syntax views stop before JSON expansion exceeds
their size or depth limit and show a message; the checked mathematical view
remains available.
The native CLI adapter also reuses serialized handles for a shared syntax node
in the same interval context and bounds the number of emitted nodes per term.
The source inspector shows the completed checked witness, individual calculation
and rewrite steps, and selected rule spelling.
Failures in an explicit `rw` or `simp` list now point to the selected rule's
source span, including a leading `<-`. A matched conditional rule with no
checked premise witness reports which parameter blocked it and suggests
`simp with [name]`. Imported default rules have no rule token in the current
file, so their failures still point to the `simp` statement. Subterm-specific
candidate spans remain unavailable because normalized core terms do not carry
source offsets. For a failed statement, the declaration itself is rejected;
no metas or subgoals enter the kernel.
An error while specializing an imported universe template selects the caller's
template name and identifies the defining module and position in its message;
later declarations in the caller can still check.

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
The full suite passed 338 tests and checked all 3,766 concrete corpus
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
template calculation steps and their source endpoints. Further regressions
bound selected and excluded rule identities, inspect consecutive mixed
`Universe` binder groups, and replay a template calculation step through the
workbench transfer with its checked path identity intact. The latest tests also
check a quantified rule whose compact syntax has a highly shared pattern and
an untyped lambda template that must not abort later declarations. Inspector
regressions now check that a multi-binder `fun` link selects the complete
function and that template `ext` and simplified-hypothesis locals are linked
and replayable.
The latest resource regressions check `rw`, two-step `calc`, `simp`, and `simpa`
against 24-level shared terms under a 128 MB heap and a 100 ms kernel deadline.
The native serialization regression keeps a 28-level shared application graph
under 100 emitted lines.
Another regression checks that thousands of distinct native references receive
distinct temporary names and recover their original reference identities.
The latest cubical regressions check `path` over a 24-level shared carrier and
`over` over a 24-level shared endpoint under the same 128 MB heap and 100 ms
deadline. A core substitution test checks that sharing under two different
binders does not capture a free name.
The imported-template regression checks that a bad rule in a different source
file selects the caller's `broken__rule` token and reports the definition's line.

The interval and face DNF operations now share a bounded work budget while
elaborating each source formula. They check the active native deadline, cap
clause products before allocation, and reject oversized expansions with a
source-located lattice budget diagnostic. Reversal, substitution, endpoint-face
conversion, normalization, and entailment use the same bounds. The regression
accepts an eight-pair cubical path formula, rejects a fourteen-pair formula
under a 128 MB heap without hanging, and then checks the next declaration.
Direct lattice tests cover growth during reversal and endpoint-face conversion.

The subsequent native review found another route around the source guard:
substituting a 16-clause join of meets into a reversed interval could expand
inside C after the elaborator had accepted the compact input. Native join,
meet, reversal, and interval substitution now share a bounded comparison
budget and a 4,096-clause product cap; substitution checks its deadline at the
native call boundary. The reproducer now returns promptly. The elaborator
also keeps a dimension-independent path unchanged under `sym`, so the concrete
`sym(refl(0))` example still checks without expanding its reversal. A generic
path that needs a large distributed formula receives an explicit budget error.
This is a resource bound, not a new equality rule or a complete compact
interval solver.
The follow-up native test preserves an eight-pair formula and rejects the
sixteen-pair reversal of a neutral path promptly, while accepting the
constant-path case. The current full JS suite passed 346 tests, the native
suite and `make lint` passed, and the inspector and built-site browser suites
passed. The canonical corpus still checks 3,766 declarations with no failures.

Generic universe-template `calc`, `rw`, `simp`, and `simpa` tactic keywords now
link to their checked specialized witnesses. Each `calc` step's `by` keyword
links to its separate checked path. Specialization exposes the witness
description and simplification trace to the inspector. The freeze edit is
withheld for a generic template: checking a proposed edit at one universe
level cannot establish that it preserves the other levels. The template
itself remains a schema until a level is selected.

Native face substitution now computes `r=0` or `r=1` only when the input face
uses that endpoint. This lets a positive face accept a compact interval whose
unused negative endpoint would exceed the native lattice budget. Tube-face
substitution reports a budget error rather than an invalid-face diagnostic
when a genuinely needed expansion is too large.

## Shared syntax refactor and corpus adoption (2026-09-25)

The three later resource reproductions had one common cause: compact syntax
graphs were treated as expanded trees at different boundaries. The elaborator
now uses one bounded graph traversal and copying module for fresh names and
native-reference replacement. Pushout construction uses that traversal and
the active proof deadline. Native request caching keys interval contexts by
their assignments, and the native CLI emits shared result nodes once with
`$id`/`$ref`; the JS adapter reconstructs the original shared syntax. The
26-level Pushout source now checks under a 100 ms proof deadline, an 18-level
nested path input serializes below 2 KB, and a 22-level shared application
round-trips through the native CLI without expanding its JSON exponentially.
No kernel checking or equality rule changed.

The corpus cleanup removes 25 unused proof-local `let` bindings across 23
files and two identity `have` aliases from `field_product_is_set`. The latter
proof now introduces its four arguments together. Four group cancellation
proofs use checked `rw` chains; three redundant arithmetic path wrappers were
removed and their 35 calls use `sym`, `trans`, and `cong` directly. The named
arithmetic results remain; `nat_add_shuffle` and `nat_double_add` use `calc`. Existing
function-extensionality proofs in the binary and radix inductions use `ext`,
and two path-algebra proofs use nested `path` abstraction and `@` in place of
explicit interval families. Direct transport expressions in cardinality and
loop rebasing use `along`. Concrete binary examples use `rfl`, and the
factorial step uses `rw`. These edits preserve theorem statements and reported
assumptions for the retained results. The inferred types of `nat_add_shuffle`,
`cardinality_path`, and `rebase_loop` were compared with their old types by
native kernel conversion. Historical benchmark and migration JSON snapshots
still record the pre-cleanup corpus and are not current declaration inventories.
All 39 retained declarations in `primes` have kernel-convertible types and the
same reported assumptions as before the three helper declarations were removed.

Run `node tools/audit-proof-ergonomics-usage.mjs` to count AST occurrences in
the canonical corpus, excluding comments and design fixtures. Current counts
are 7 `rfl`, 5 `rw`, 7 `ext`, 6 `path` abstractions, 12 `@` applications, 3
grouped introductions, 2 grouped binder uses, 4 `along`, 2 `calc`, and two
uses each of `simp only`, `simpa only`, `over`, and `apd_path`.
Rule registrations, untyped expected lambdas, and value-style `have` remain
exercised in checked examples and regressions but have no corpus use yet.
Their absence is an adoption gap, not
evidence of a proof shortcut: avoid replacing a one-line direct proof with a
longer tactic invocation solely to raise the count.

Verification after this cleanup: the full JS suite passed 351 tests, including
the canonical corpus with 3,763 checked declarations, 44 templates, and no
failed or blocked declarations. All 36 changed proof modules and their imports
checked; the kernel tests, `make lint`, inspector browser test, and built-site
browser test passed. The undefined-behavior sanitizer passed the native C
suite and all 13 CLI adapter tests, including the shared output regressions.
The address-sanitized native binaries compiled, but the
sanitizer run stalled on its independent `test-lattice` binary, and a trivial
sanitized CLI query also did not finish within five seconds. Those sanitizer
executions were interrupted; they are not counted as passing checks.

## Focused simplification and dependent-path adoption (2026-09-25)

Eight existing proofs now use the four remaining requested features. These
are canonical library proofs, not new demonstration declarations:

| Feature | Existing declarations | Simplification |
| --- | --- | --- |
| `simp only` | `ring_distribute_left`, `ring_add_cancel_prefix` in [ring_laws](../../web/proofs/ring_laws.cubist) | Replace explicit congruence/composition chains with selected ring laws. Commutativity is instantiated at the required arguments rather than used as a looping general rule. |
| `simpa only` | `field_add_cancel`, `field_inverse_unique` in [ordered_fields](../../web/proofs/ordered_fields.cubist) | Normalize the supplied equality after applying the inverse operation; remove the `undoY`/`undoZ` intermediates and explicit chains. |
| `over` | `field_subtype_ext` in [field_extensionality](../../web/proofs/field_extensionality.cubist), `group_hom_ext_at` in [group_hom_universes](../../web/proofs/group_hom_universes.cubist) | Construct the genuinely dependent second-component path from transported law evidence, then assemble the pair path directly. |
| `apd_path` | `apd_constant` in [paths](../../web/proofs/paths.cubist), `ap_interchange` in [equivalence_from_inverse](../../web/proofs/equivalence_from_inverse.cubist) | Replace explicit interval families and pointwise function applications in existing homotopy laws. These use the constant-family specialization of dependent path action. |

The pair proofs rely on judgmental Sigma eta, making
`field_dependent_pair_path`, `field_sigma_eta`, and `group_hom_eta_at`
unnecessary. Their only corpus callers have been replaced, and the universe
regression now checks the retained homomorphism schemas at U0–U3. No whole
file became unused. This follow-up removes 109 source lines across six proof
modules, relative to the first cleanup above. No elaborator or kernel changes
were needed for these substitutions.

Native conversion checks against saved pre-edit sources confirmed the types
and reported assumptions of all 83 retained declarations, including 116
universe specializations. The two `apd_path` replacements also have
kernel-convertible proof terms. The simplification and pair-path rewrites
change proof construction; their consumers were rechecked rather than
assuming that all equality witnesses are interchangeable.

Verification: all six affected modules check, formatting preserves their
expanded syntax, and the full 351-test suite passes. The canonical corpus has
3,761 checked declarations and 43 templates, with zero failed or blocked
declarations. The AST usage audit reports exactly two uses of each requested
feature (`simpOnly`/`simpaOnly` are its names for the explicit `only` forms).

## Review fixes: search scope, dependent matches, premises and names (2026-09-25)

A review of this branch found four elaborator bugs and one older one. None
changes the kernel or its equality rules.

- Search time limits were taken when `rw`, `simp` or `calc` started and checked
  again while rebuilding the proof, after the rest of the block had been
  elaborated. A valid later statement taking over a second failed the tactic
  with "Path composition elapsed-work budget exceeded." Each rule search now
  starts its own one-second limit (`SEARCH_TIME_LIMIT_MS` in
  `lib/cubical/translate.mjs`) after user terms are elaborated. Rebuilding
  proofs and composing `calc` steps has no search limit: it is bounded by the
  number of rewrites or steps and still honours declaration cancellation.
- `simp`, `simpa`, `simp at` and type-goal `simp` failed on any match in a
  dependent position, even on a goal that already held. `findRewrite` in
  `lib/cubical/proof-rewrite.mjs` now returns a result instead of throwing
  for "no match". The simplifier skips such matches, tries the other endpoint,
  and mentions them only if the goal stays unsolved. `rw` keeps its reported
  error for an explicit endpoint and combines both sides for the default.
- Premise search re-searched the same failed premise on every pass and on both
  endpoints, and 64 attempts aborted the whole simplification. Outcomes are
  now remembered per rule and premise. Exhausting the limit only stops
  conditional rules from firing. Node, candidate, rewrite, cycle and size
  limits met while proving a premise leave that premise unproved; they are
  `SearchLimit` errors. The shared time limit (`SearchTimeout`) and kernel
  cancellation still stop the simplification. A freeze replay starts from
  fresh premise state.
- In ordinary declarations the `calc` step link started at the left endpoint
  and was often hidden by a smaller link there. The parser now records each
  step's `by` token, and both the elaborator and the template link walk use it.
- Older than this branch: generated names were `stem + serial`, so `a1` with
  serial 1 and `a` with serial 11 were both `a11`. The second binder captured
  the first, and `forall a : Nat, a = a1` checked as `forall a, a = a`. The
  kernel stayed consistent, but the checked statement differed from the
  source. A stem ending in a digit now gets a separator, making generated
  names unique, and every binding site asserts that its name is new.

Smaller changes: the formatter prints `simp_set name = [...]` with a space;
template inspection and specialization skip freeze replays whose result is
discarded; the elaborator's conversion query avoids live coordinate names; the
language reference describes the new behaviour. The address-sanitizer stall
recorded above is environmental on that machine: a trivial `int main(void)`
built with `-fsanitize=address` also hangs there.

Regression tests in `tests/proof-ergonomics.test.mjs` cover each bug and fail
on the previous code. The time-limit test advances a fake clock during a later
statement rather than depending on machine speed.

Remaining design work: tactic search limits are still wall-clock, so a search
near the one-second limit can pass on a fast machine and fail on a slow one.
Deterministic work budgets would remove that. Candidate failures are still
classified by the kernel's "Type mismatch." message, and instantiated rules
still match by conversion while quantified rules match syntactically.
The [HoTT roadmap](../roadmaps/hott-automation-roadmap.md) now owns this work:
deterministic fuel is A4, the goal layer and elaborator infrastructure A5,
and residual-goal diagnostics A6.

## Library migration tooling (2026-09-25)

Library-wide adoption of the new syntax is checked mechanically, not by review
alone. `node tools/verify-proof-migration.mjs [--base REV] [--level
identical|types] [module ...]` checks each edited module in the same native
kernel as its version at `REV` (default `HEAD`). With no module names it takes
every `web/proofs` module that differs from `REV`. The edited source is loaded
under a shadow module name, so both versions and their shared imports are
checked in one kernel session.

- `identical` requires every declaration's checked term and type to hash
  equally up to bound-variable and dimension names (de Bruijn indices) and the
  session serials of generated unfolding helpers, which are compared by their
  checked bodies.
- `types` requires kernel-convertible public types and the same assumption
  labels; proof terms may change.
- Both levels require the same declaration list and order. A template is
  compared through its specialization at the least universe levels (up to
  `U2`) at which the original checks.

`node tools/migrate-proof-syntax.mjs --rewrites a,b [--skip FILE.json]
[module ...]` applies source rewrites from
[proof-rewrites.mjs](../../tools/proof-rewrites.mjs) and formats the result.
The rewrites splice the recognized spans only, keep all other text, and skip
any span whose rewrite would drop a comment. Six rewrites elaborate to the
same checked terms (`params`, `fun`, `intro`, `have`, `along`, `path-apply`).
Four keep public types but change proof terms: library path wrappers to
builtins (`wrappers`), `exact refl(x)` to `rfl` (`rfl`), `path` with two
interval lambdas to `path i =>` (`path-lambda`), and `exact FunExt(...)` to
`ext` (`ext`). The skip file maps module names to declarations that must stay
unchanged. [proof-migration.test.mjs](../../tests/proof-migration.test.mjs)
covers the hasher, both levels, a changed statement, and every rewrite. The
formatter now separates adjacent lambda binder groups with a space.
