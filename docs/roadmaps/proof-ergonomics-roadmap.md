# Simplification and shorter proofs in Cubist

Progress reconciled on 2026-10-10 against main `cb525f07`. Open branch
work is recorded separately in the [work plan](work-plan.md#branch-work).

Status reviewed 2026-10-07: first release delivered on 2026-09-25. Milestones 0–3 check through
the native kernel: grouped binders and introductions, both `have` forms
(since 2026-09-30, `let`),
`rfl`, `calc`, `rw`, `simp` and `simpa` with explicit, registered and named rule
sets, `simp at h as h2`, bounded conditional equality rules, checked type-path
transport, and the "Replace with simp only" action. Milestone 4's cubical
shorthand (`path i =>`, `p @ i`, `ext`, `transport`, `apd_path`, `over`) shipped
early. A review on 2026-09-25 fixed four elaborator bugs and an older
name-capture bug; see the [implementation checkpoint](../tactical/proof-ergonomics-handoff.md).

The shared goal layer's core and motive abstraction are delivered (HoTT A5),
as are G0's checked universe binders and all of milestone 8, whose last
two extensions, L2.9a and L2.9b, were done on 2026-10-06. One-sort
inductive declarations, explicit `match`, and automatic clauses and
`obligations` were released with H1 on 2026-10-02 (work-plan L2.1, L2.2a
and L2.2b); the rest of milestone 7 is open. Milestone 5's argument
inference and implicit parameters were delivered on 2026-10-04 (L4.1a,
L4.1b), and its `apply` and `refine` withdrawn. Milestone 6's core
theories, with their notation and sections, were delivered on 2026-10-05
(L2.4) and revised on 2026-10-06 (L2.4c); named notations selected by `use`
replaced their notation (L2.10). The construction-and-fold prototype for initial/free models (L2.6) is in
[open PR #188](https://github.com/KanHarI/cubist-math/pull/188), not main.
Checked capabilities, universal proofs, algebraic normalization and structure
identity remain open.

The remaining dependent, cubical, induction and shared elaboration work moved
to the [HoTT and cubical automation roadmap](hott-automation-roadmap.md), and
kernel-facing interval work to the [kernel roadmap](cubical-kernel-roadmap.md).
Each open item below names its new owner. This roadmap keeps:
- general argument inference (milestone 5);
- theories, structures and notation (milestone 6);
- inductive declarations and pattern matching (milestone 7);
- computability as a checked property (milestone 8).

Milestones 5–7 build on the HoTT roadmap's goal layer (A5).
The [computation notation roadmap](computation-notation-roadmap.md) builds on
their inference, structures and matching for monadic `do` and arrow blocks;
it owns that planned extension and requires no new kernel rule.
This document covers language tooling and does not resume any mathematical
roadmap. Examples below not yet covered by the checked sample files remain
proposals.

**Restructured later on 2026-09-25.**
- The first library was migrated to the new syntax: tiers 1–2, merged in PRs
  #2–#4. It is archived, and the new library started with `library/naturals`,
  now `library/nat.cubist`;
  its results are recorded in
  [library-results.md](../library-results.md).
- This roadmap adopted milestones 6–8:
  - 6: theories, which replace the planned records, notation and sections;
  - 7: inductive declarations and pattern matching;
  - 8: computability as a checked property.
- Milestones 6 and 7 follow the [language feature
  proposal](inductive-language-features.md). They depend on the kernel's G0
  and item H ([kernel roadmap](cubical-kernel-roadmap.md),
  [design](higher-inductive-types-design.md)).
- The [work plan](work-plan.md) sequences all roadmaps.

The original [PR-sized implementation plan](historical/proof-ergonomics-implementation-plan.md)
is archived as a superseded sequence. Its checked examples and detailed
lowering contracts remain evidence; current scheduling is in the
[work plan](work-plan.md#first-actions).

## Remaining implementation contracts

Archiving the old sequence does not complete its unfinished work. These
active owners retain its requirements and acceptance cases:

| Remaining obligation from the old plan | Active owner and contract |
| --- | --- |
| Worker cancellation and remaining goal metadata, filling, face contexts and source spans | Work-plan L1.3/L1.2r; HoTT A4–A6. Preserve deterministic fuel, scoped reconstruction, rollback and browser/CLI agreement. |
| General proposition premises and map-based proposition simplification (old PR 8) | HoTT D1 and this roadmap's milestone 3. Construct checked witnesses, count premise search, reject cycles and false premises, and preserve inspection/freeze evidence. |
| Dependent context replacement and motive reconstruction (old PR 10) | HoTT A5/B1/E1 and work-plan L1.4/L3.2. Recheck downstream hypotheses, transport proof-dependent indices and reject unsupported boundaries. `apply`/`refine` are withdrawn, not pending. |
| Generated structure identity and transfer (old PR 11) | Core theories L2.4b and HoTT F1/F2, after L3.1/L3.2. Specify a supported grammar and prove preservation for nonidentity equivalences. |
| Certified algebraic normalization | This roadmap's milestone 6, separately scoped from the completed core-theory release. |

The old plan's [lowering and reconstruction contracts](historical/proof-ergonomics-implementation-plan.md#freeze-these-semantics-before-implementation)
and [measurement criteria](historical/proof-ergonomics-implementation-plan.md#measurement-and-release-checks)
remain linked requirements where the active owner has not replaced them.
Its obsolete feature order and implementation snapshots are historical.

The subsequent [HoTT and cubical automation roadmap](hott-automation-roadmap.md)
records why the current simplifier cannot reach path operations. It now owns
the remaining dependent, cubical and goal-derived induction work below; see
its [changes to the ergonomics plan](hott-automation-roadmap.md#changes-to-the-ergonomics-plan).

## Objective and current foundation

Reduce repetitive proof plumbing while keeping generated proofs inspectable
and checked by the existing cubical C kernel. Deliver a useful simplifier in
small increments, together with features that remove repeated arguments,
nested equality chains, and repeated structure projections.

The language has `intro`, `let`, `obtain`, `match`, `exact`, `rfl`,
`calc`, `rw`, registered `simp` and `simpa`, and explicit `only` modes; typed and expected-type lambdas;
tuple patterns; and equality operations including `refl`, `sym`, `trans`,
`cong`, `transport`, and `apd`.
The [language reference](../../web/language.html) is the current syntax authority.
There is bounded equality-premise simplification, but no general proposition
premise solver; `apply` was withdrawn (L4.4). Since G0, a universe variable
`U < UU0` is a kernel binder: a generic definition is one checked kernel
term. Since L4.1b, implicit parameters in double braces and universe
arguments are inferred where constraints determine them.

The instruction driver unfolds definitions on demand while deriving
computational equality. The old `with unfolding` hints were removed with
the term checker on 2026-10-02. Theorem simplification constructs checked
paths from equality lemmas; conversion follows the kernel's computation
rules.

For example, addition recurses on its first argument, so `0 + n` computes to
`n`. The proof that `n + 0 = n` is the existing
[`nat_add_zero`](../../archive/first-library/primes.cubist) lemma. Applying that lemma
automatically inside a larger expression is an initial simplifier use case.

Lean supplies useful precedents for a registry of simplification lemmas and an
explicit `only` mode. Its simplifier recursively applies rules, whereas `rw`
lets authors select a sequence of rewrites. These are design references, not a
promise to reproduce Lean's semantics in Cubist.
See [Lean's simp sets](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/)
and [simplification versus rewriting](https://lean-lang.org/doc/reference/latest/The-Simplifier/Simplification-vs-Rewriting/).

## Architecture and invariants

Put automation in the parser and elaborator. Its output is ordinary core
syntax, validated by the native checker before a declaration is accepted.
No simplifier result, JavaScript equality comparison, cache entry, or rule
attribute becomes a new trusted proof rule. No convenience adds an assumption
either: every result that uses no truncation or other assumption must remain
computable by the kernel
([HoTT invariant 10](hott-automation-roadmap.md#invariants-added-to-the-ergonomics-requirements)).

Large interval expressions need a separate elaborator-to-kernel improvement,
certified interval normalization, now [G5 in the kernel roadmap](cubical-kernel-roadmap.md#items).
Until then, the native clause and work limits make exponential distribution
fail promptly, and the elaborator simplifies constant-path reversal before
checking.

Use a shared rewriting service for `rw`, `calc`, `simp`, and `simpa`:

1. Read the checked type of a lemma and instantiate its parameters.
2. Match its left side against a selected, well-typed subterm.
3. Construct its instantiated path, reversing it when requested.
4. Lift that path through a supported enclosing context.
5. Compose paths and reconstruct the proof of the original goal.
6. Submit the complete term to the native checker.

For a fixed carrier `A`, simplifying `t : A` should return `t' : A` and
`p : t =[A] t'`. Simplifying the endpoints of an equality goal should compose
these witnesses with a proof between the simplified endpoints. Changing a goal
type from `G` to `G'` needs a checked reconstruction `G' -> G`; an actual path
of types can supply that map through transport. A goal stack records those
reconstructions, local contexts, source locations, and any unresolved subgoals.
No declaration may escape with unresolved metavariables or subgoals.

Pattern matching (milestone 7) keeps the same boundary. Structural recursion
and coverage are checked by the untrusted elaborator, which compiles `match` to
applications of kernel-generated eliminators. The kernel never trusts a
termination or coverage checker; a non-structural call is rejected before
checking. Computability is expressible and preserved (milestone 8):

- no convenience adds a non-computing dependency;
- automatic clauses use proved h-level evidence;
- the driver's unfolding strategy never hides computational content from evaluation.

Keep automatic computation demand-driven. Preserve named references and shared
subterms; do not fully unfold the library to discover matches. Specify which
computational reductions remain available under `simp only`; the word `only`
restricts theorem rules, not the kernel's ability to check conversion.

## HoTT and cubical requirements

These requirements apply from the first milestone, including to the apparently
simple nondependent fragment.

### Paths retain information

Equality proofs are mathematical data. Two paths with the same endpoints need
not be equal, and a loop `p : x = x` need not be reflexivity. Never introduce
proof irrelevance, UIP, axiom K, or a rule replacing arbitrary loops by `refl`.
Simplification can use a proved higher path between paths, retaining that
witness when the result is used dependently.

An `IsProp(A)` or `IsSet(A)` argument may justify additional simplifications
only where its checked witness is available. `IsSet(A)` makes each equality
type a proposition; it does not make all elements of `A` equal. Do not infer
either property merely because the source calls a definition a theorem.

### Dependent rewriting needs transport

Given `p : x = y` and `v : C(x)`, rewriting the index changes the fiber.
Produce `transport(C, x, y, p, v) : C(y)` rather than relabeling `v`.
Dependent function congruence requires `apd` or an appropriate `PathP` witness,
not ordinary `cong`. Rewriting a hypothesis also requires rebuilding later
hypotheses and the goal that depend on it, in telescope order.

The particular path can affect the result of transport. Preserve its direction,
composition, and coherence evidence. Unit, inverse, and associativity laws for
paths may be propositional rather than computational; use checked library
lemmas whenever conversion does not establish them.

Reuse the existing [dependent path/transport equivalence](../cubical/path-over.md)
and [dependent transport constructions](../cubical/dependent-transport.md).
Unsupported dependent contexts must produce a specific diagnostic in early
releases, rather than fall back to substitution of source text.

### Logical equivalence is not arbitrary type equality

Cubist's `and`, `or`, and `exists` carry data, and `IsProp` is a library property.
Two maps `A -> B` and `B -> A` alone do not establish `Equiv(U, A, B)` for
arbitrary types. For example, `A and A` cannot generally be identified with
`A` by treating the two components as interchangeable evidence.

A future logical simplifier may transform goals through explicitly constructed
maps. It must not turn those maps into a path of arbitrary types. For an
equality of types, require a checked equivalence and the appropriate univalence
construction, or a directly supplied path. Retain all existing assumption
dependencies of that construction. Restrict proposition-specific rules to
types with checked `IsProp` evidence. In particular, automation must respect
the elimination restriction on propositional truncation and must not extract
an untruncated witness by treating `Truncate(A)` as ordinary `exists`.

### Respect cubical scope and boundaries

Interval variables and ordinary term variables have different scopes.
Matching and reconstruction must preserve freshness, face restrictions,
endpoint types, and the scope of every `Path`, `PathP`, composition, and
transport binder. A term equal under the face `i = 0` cannot be reused as
unconditionally equal elsewhere. Reuse existing capture-avoiding substitution
and [dimension scope rules](../cubical/dimension-liveness.md).

Do not descend generically into composition tubes, Glue data, or higher
inductive constructors. Add support constructor by constructor, with witnesses
and boundary tests. For pushouts, suspensions, and other higher inductive
eliminators, retain the path and higher coherence branches as well as point
branches. Successful rewriting of points alone is insufficient.

### Make assumptions and witness identity visible

Rewriting under a function binder may need function extensionality; obtain it
through an existing checked construction or report its actual library
dependencies. Univalence and truncation rules must likewise retain their
dependency reports. A simplifier must not silently add classical choice,
excluded middle, or new axioms to an otherwise constructive proof.

Cache keys must account for the local context, universe variables, live
dimensions and faces, rule set, and unfolding policy. Cached results include
their proof witnesses; never identify two witnesses solely because their
endpoints match. Preserve native handle ownership and invalidate caches after
relevant source or imported rule changes.

## Milestones

Milestones 0–3 form the delivered first release. Milestone 4 and the
extensionality items moved to the HoTT roadmap. The remaining items build on
the HoTT roadmap's goal layer (A5):
- milestone 5's inference is needed before indexed families;
- milestone 6's theories use A8's projections and F1's structure identity;
- milestone 7 follows kernel stages H1–H3;
- milestone 8 is complete.

A box marked moved names the item's new owner.

### 0. Establish examples and remove straightforward repetition

- [ ] Select representative proofs from `primes`, `paths`, `finite_dependent_counts`,
  `group_operations`, and `field_vector_spaces`. Record source token counts,
  repeated explicit parameters, checking time, kernel steps, and arena usage.
  Keep the original public statements and assumption lists as a baseline.
  The selected graph now records tokens, elapsed time, native checking steps,
  rewrite candidate work and final-check arena snapshots; parameter repetition,
  per-declaration arena deltas and signature/assumption inventories remain.
  The HoTT roadmap's baseline (A7) extends this measurement.
- [x] Add grouped introductions, such as `intro A, x, h;`, by expansion to
  existing introductions, preserving an inspectable context at each binder.
- [x] Add grouped typed binders, such as `(x, y : A)`, and multi-binder lambdas.
  Add expected-type lambda binders only where the expected function type gives
  an unambiguous domain. Grouped universe variables, as in
  `(U, V < UU0, A : U)`, bind like separate ones.
- [x] Add `have h := term;` when its type can already be inferred, plus
  `have h : T := term;` as shorthand for an existing `have`/`exact` block.
  The distinct assignment token avoids ambiguity with equality inside `T`.
- [x] Define source spans and formatter behavior for each expansion. The
  formatter preserves the tokens and expanded syntax of every new form, and
  each form links to its checked term. Computing link sites in one place moved
  to HoTT A5.

Completion: conveniences elaborate to the same core meaning as their expanded
forms; shadowing, dependent binders, comments, formatting, and source inspection
work. Publish measured examples without claiming an unmeasured percentage gain.

### 1. Explicit rewriting and calculation chains

- [x] Moved to HoTT A5: introduce the goal/reconstruction representation.
  Done in PR #15: `rw`, `simp`, `simpa`, `ext`, `intro`, `over` and premise
  search build their proofs through one plan interface in
  `web/translator/proof-goals.mjs`.
- [x] Add `rw [p];` and `rw [<- p];`, with rules applied in listed order.
  Initially rewrite the first eligible occurrence in a documented traversal;
  add an explicit occurrence selector before supporting complicated targets.
- [x] Support rewriting equality endpoints and ordinary applications with a
  fixed result type. Report unsupported dependent positions precisely. `rw`
  reports a match in a dependent position, and the simplifier skips one.
  Pointing at the subterm needs source spans on core terms (HoTT A5); other
  constructors are HoTT A2.
- [x] Add `rfl;` to close goals whose endpoints are definitionally equal.
  `rw` leaves a goal unless it can close it by this rule.
- [x] Add `calc` for homogeneous equality chains, elaborating each step against
  its endpoint types and composing checked paths. Inequality and mixed-relation
  chains are a later extension requiring registered composition lemmas.

Example, checked in the [implemented arithmetic sample](../examples/proof-ergonomics/implemented/arithmetic.cubist):

```text
import primes;
use nat;

def add_zero_twice(n : Nat) : (n + 0) + 0 = n {
  calc {
    (n + 0) + 0 = n + 0 by nat_add_zero(n + 0);
    _ = n by nat_add_zero(n);
  }
}
```

Completion: forward/reverse rewriting, congruence, and chain reconstruction
pass native checking; wrong carriers, missing matches, variable capture, and
invalid endpoint chains fail with source locations. A failed statement leaves
the previous checked state intact.

### 2. Minimal useful simplifier: explicit rule lists

- [x] Add `simp only [rules];` on equality goals. First permit instantiated
  proofs, then universally quantified equality lemmas through a restricted
  matcher. Infer parameters from the matched side and its checked type; require
  explicit arguments when inference is ambiguous. Full implicit syntax is
  not a prerequisite.
- [x] Traverse supported subterms from children to parents, rewrite in a
  deterministic order, and repeat until stable or a resource limit is reached.
  Reuse congruence and path composition from milestone 1.
- [x] Return checked endpoint witnesses, then close by conversion if possible.
  Otherwise retain a reconstructed residual goal for the next statement.
  Diagnose an unfinished block with that residual goal. Printing the goal in
  that diagnostic moved to HoTT A6.
- [ ] Moved to HoTT A4 and A6: bound rewrite count, matching work, generated
  term size, and elapsed work; support worker cancellation. Detect repeated
  states and report the rules involved. A loop or exhausted budget never
  counts as success. Rewrite count, traversal, candidates, term size and
  premise search are bounded and recorded per declaration. Since HoTT A4 and
  A6 (2026-09-27), each search spends deterministic fuel instead of a time
  limit, and a cycle names its rules; worker cancellation remains.
- [ ] Keep associativity, commutativity, distributivity, and expanding
  definitions out of automatic default normalization. Explicit cyclic lists
  must still terminate with a useful failure. Cyclic lists fail with a cycle
  diagnostic. No library default rules are registered yet, so this remains a
  review criterion for the first default set (milestone 3).
- [x] Show used lemmas and intermediate equalities in the inspector. Each
  simplifier rewrite now exposes its checked path and selected rule.

Example, checked in the implemented arithmetic sample as `add_zero_twice_simp`:

```text
import primes;
use nat;

def add_zero_twice(n : Nat) : (n + 0) + 0 = n {
  simp only [nat_add_zero];
}
```

Completion: the example and nested fixed-codomain applications check; `0 = 1`
remains rejected; repeated variables in patterns must match consistently;
reverse rules and cycles have deterministic behavior. No general proof search,
dependent hypothesis mutation, or automatic logical equivalence is required
for this release.

### 3. Imported rule sets, conditional rules, and `simpa`

- [x] Add explicit metadata registering an already checked equality lemma.
  Since Cubist uses `def` for proofs and constructions, classify registrations
  by their checked type. Keep requests to unfold a definition distinct from
  requests to rewrite by a path; settle exact attribute syntax here.
- [ ] Define module export/import behavior, qualified identities, local scope,
  duplicate registration handling, priorities, and deterministic tie-breaking.
  Checked registrations and named sets now flow through imports, with sorted
  default rules and an error for ambiguous imported set names. A reviewed
  library default set remains open and stays in this roadmap. A generic
  declaration is elaborated once, in the rule environment of its definition.
- [x] Add `simp;`, `simp [rules];`, local exclusions, and broader `simpa`
  modes backed by registered sets. These forms and explicit `without [rules]`
  exclusions work for homogeneous equality goals. For other type-valued goals,
  `simp` rewrites along checked paths of types and transports the following
  proof back; `simpa` simplifies the supplied proof type and goal, transports
  between them, and checks the result. Rewriting is limited to the root and
  ordinary fixed-codomain applications. Proposition-specific maps are deferred
  to HoTT D1; dependent contexts moved to HoTT A2 and E1. Arbitrary logical
  equivalences are never turned into paths of types.
- [x] Permit conditional rules only when every premise gets an actual checked
  witness. Explicitly selected local equality witnesses and reflexive premises
  work, with witnesses retained in the instantiated theorem application.
  A homogeneous equality premise may also be simplified by other selected
  rules, to depth two within the enclosing search's time limit. Each premise
  is searched once per simplification; after 64 searches, conditional rules
  whose premise is not already known do not fire. Active rules are excluded
  from their own premise search; every resulting premise witness is checked
  before theorem application. General proposition premises are deferred to
  HoTT D1.
- [x] Add `simp only [h] at hypothesis;` first for hypotheses with no downstream
  dependencies, or bind a fresh simplified copy. The implemented
  `simp only [rules] at h as h2;` binds a checked fresh equality copy and keeps
  `h`; dependent replacement remains in milestone 4. Local hypotheses enter
  the rule set only when selected.
- [x] Offer an action that replaces an exploratory `simp` invocation with an
  explicit `simp only` list of the lemmas actually used. The inspector offers
  the action only when every used rule has a name in the current source scope;
  the edited source is checked again immediately. Removing unused rules must
  reproduce the same residual goals and constructed proof up to conversion
  before the action appears. Later proof steps may depend on a particular path,
  whether it came from `simp at`, `simp`, or `simpa`.

Completion: imports cannot leak local rules; unrelated unused rules add no
axiom dependencies to a proof; changes to a rule invalidate affected results;
explicit lists reproduce the proof's success. Traces explain failed premises
and rule selections without requiring authors to inspect kernel opcodes.

### 4. Dependent rewriting and cubical extensions (moved)

This milestone moved to the [HoTT roadmap](hott-automation-roadmap.md), which
reorders it around folded path operations, transport fillers and checked
library laws. Its requirements and completion criteria still apply there.

| Item | HoTT roadmap |
| --- | --- |
| Dependent applications, pairs and rebuilt telescopes | A2, E1, and B1's `subst` |
| Dependent paths through the `PathP`/transport bridge | E0 and E1 |
| Rewriting under binders | Not yet scheduled: A2 excludes binder bodies until a binder-aware traversal exists |
| Path, transport and structure simplification sets | A1, then C1–C2, classified by A7's conversion fixture |
| Proposition- and set-specific transformations | D0a–D2 (h-level templates, solver and subtype extensionality) |
| Cubical constructors | E2 squares and bounded boundary-filling experiments |

Delivered here ahead of that work: `path i =>`, `p @ i`, `ext x;`,
`transport v along p in C`, `apd_path(f, p)`, `over C along p by { … }`, and
`simp`/`simpa` transport along checked paths of types.

### 5. Inferred arguments and goal-directed proof construction

- [x] Add named arguments and `_` holes for values determined by a known
  function type, supplied arguments, or the expected result type. Implement
  scoped metavariables, occurs checks, and unresolved-hole diagnostics.
  This is work-plan L4.1a, delivered on 2026-10-04
  (`web/translator/arguments.mjs`, `cubist-tests/arguments.cubist`,
  reference [holes](../../web/reference/terms.html#holes)). Universe
  arguments stay explicit until L4.1b. Also needed by H2: indexed
  families are impractical without implicit indices, as in
  `cons(x, k + n, append(A, k, n, rest, ys))`.
- [x] Add opt-in implicit binders, and infer level arguments where
  constraints determine them. Delivered on 2026-10-04 as L4.1b: double
  braces before a definition's parameter list, `def f{{A : U}}(…)`, and
  after a definition's name at a call, `f{{Nat}}(x)`, which supplies the
  implicit arguments explicitly; and a universe hole as the least universe
  the call needs. After G0, universes are level expressions, and
  this item absorbs HoTT A9. Retain a way to supply every implicit argument
  explicitly. Reject ambiguous inference and universe lowering. This is
  L4.1b; it follows L4.1a and G0 without waiting for indexed-family kernels.
- [ ] ~~Add `apply theorem;` and `refine term;` with visible subgoals and explicit
  witness obligations.~~ Withdrawn on 2026-10-05 (work-plan L4.4): `let` and
  `exact` express both, and holes and implicit parameters infer what `apply`
  would.
- [ ] Goal-derived induction is milestone 7's `match`; `Path` induction
  remains HoTT B1. `constructor`/witness conveniences stay here, as ordinary
  pair or sum construction respecting truncation elimination restrictions.

Completion: representative algebra proofs omit repeated carrier and endpoint
arguments; inspectors reveal inferred arguments; ambiguity has a local remedy;
CLI and browser agree; every goal and metavariable is solved before acceptance.

### 6. Theories, structures and notation

Structures are theories used for their models
([proposal §1](inductive-language-features.md#1-theories-one-declaration-for-structures-initial-models-and-universal-properties)).
Models, homomorphisms, identity, notation and sections need no kernel change.
Initial and free models need milestone 7 and kernel H. The revised
[L2.6 contract](core-theories.md#initial-and-free-models-l26) requires
`deriving (morphisms, free)` or the weaker `morphisms, initial`, including
checked universal proofs. The first equational strategy is a supported
fragment of derivation, not a restriction on valid theory laws; extra laws
require proofs, and a failed derivation reports its obligation.

Release L2.4 covers the core models, homomorphisms, isomorphisms, named fields,
notation, sections and `extends`. It uses HoTT A8's projections and D0a's
checked h-level definitions; automatic evidence uses the later D1 solver.
Generated structure identity is a separate L2.4b
release through HoTT F1 and its prerequisites; it does not gate core theories.

- [x] `theory` declarations: carriers as fields with an h-level
  (`M : set U;`), the universe named in the header, operations with
  notation, laws, and `extends`. Delivered on 2026-10-05 as L2.4
  ([core theories](core-theories.md)) and revised on 2026-10-06 as L2.4c,
  all but the L2.4b items. They generate:
  - the type of models, named by the theory, `Monoid(U0)`: a Σ record
    with named fields and eta (`T.Model` until L2.4c);
  - `T.Hom`;
  - `T.Iso`;
  - in L2.4b, `T.equality : (M = N) ≃ T.Iso(M, N)`, generated through HoTT
    F1's structure identity machinery;
  - in L2.4b, supported `T.Displayed` and coherence interfaces.

  Projections use HoTT A8's syntax.
- [x] Scoped notation declared by a theory. Delivered with L2.4, where
  `open M` selected it; on 2026-10-06 `use M;` replaced `open`, and the
  [notation roadmap](notation.md) (L2.10) replaced the name-based operators
  and numerals with named notations: every source selects `use nat;`.
- [x] `section {{U < UU0}}(G : Group(U)) { … }`: shared models and parameters,
  generalized deterministically, including dependencies that occur in types.
  Resulting signatures are shown. Delivered with L2.4; the library's
  rationals are one section over a ring.
- [ ] Initial and free models with `fold`, `fold_unique` and `universal`
  (L2.6). The construction prototype is implemented in unmerged PR #188:
  `initial N : T(…);` and `free W(A : U0) : T(…) on A;` declare the type,
  `N.model` and `N.fold` for single-sort theories. The
  [revised contract](core-theories.md#initial-and-free-models-l26) of
  2026-10-07 requires morphism opt-in, pointwise `fold_unique`, `T.Hom.ext`
  and checked universal properties before publishing capabilities.
  Additional-law evidence and higher-theory coherences follow; recursors
  alone do not establish initiality. `CauchyStructure` and `CwF` need H3.
- [ ] Algebraic normalization targets `CommRing(U)` and similar models. It
  is separate from generic `simp` and produces checked certificates.
- [ ] Expected-type completion and lemma suggestions insert checkable source
  and show the resulting obligations.

General typeclass search, implicit coercion networks, unrestricted higher-order
unification and broad proof search remain deferred. Structure scope stays
explicit.

Completion, with generated identity required for L2.4b. Met by L2.4 on
2026-10-05 but for structure identity:
- a ring lemma takes one model argument and uses its notation (met: the
  ring lemmas of `library/algebra.cubist`);
- group structure identity is a generated instance, not a development
  (open: L2.4b);
- the forgetful map of an `extends` theory is generated (met: a model's
  parents' models);
- incorrect homomorphism preservation is rejected (met, as the type of
  the preservation field: doubling offered as a homomorphism of `Nat`'s
  multiplicative monoid is refused; no fixture records it yet).

### 7. Inductive declarations and pattern matching

This is the language of the [kernel design](higher-inductive-types-design.md#5-language)
and of the [feature proposal](inductive-language-features.md). Releases follow
kernel stages H1–H3. The first release also needs HoTT A5 (motive
abstraction). Milestone 5's scoped holes and named arguments (L4.1a) improve
it but do not gate it: explicit matching accepts explicit motives and
arguments. Explicit matching is L2.2a; automatic clauses in L2.2b additionally need
D0a and D1's first slice (h-level evidence). Implicit binders and level
inference (L4.1b) are a separate release.

**Status (2026-10-04).** Released with H1 on 2026-10-02: `inductive` with
parameters and universe parameters and no indices; h-levels by a generated
squash constructor (`prop`, `set`, `trunc(n)`); path constructors as
equalities and `PathP`; the expression `match` with `as … return`, one
scrutinee, structural recursion on one argument, clauses that bind
interval variables for path constructors, and hand-written squash clauses;
since 2026-09-29, the closing proof statement, whose motive is the goal
over the matched value, with the hypotheses about it generalized, and
recursive calls that pass values of their own for the other parameters, but
those the matched parameter's type depends on; since 2026-10-04, several
scrutinees, nested patterns, variables and `_`, the expression's motive
from the motive service where its expected type mentions the value, and the
match statement on sums, which replaced `cases`; and, with H1, automatic
squash clauses from checked h-level evidence and explicit `obligations`
(L2.2b). Not delivered: inferred motives with index generalization,
companion sorts, `cell` syntax (L2.8), proof-first h-levels (L2.3b),
dependent matching, views, canonical quotients, `deriving` and nested
declarations.

- [ ] `inductive` declarations:
  - parameters, and indices after the colon;
  - h-levels, with setness proved from the generated path characterization
    before a squash constructor is added;
  - path constructors as equalities, `PathP` or `cell` face systems;
  - companion sorts with `with`, relations with notation, and argument
    bundles.

  The elaborator produces H's signature normal form, and errors name the
  offending argument or face.
- [ ] `match`:
  - an expression and a closing proof statement;
  - several scrutinees, inferred motives with index generalization, and
    optional `as … return`;
  - structural recursion by name, across companion functions;
  - clauses for path constructors that bind interval variables;
  - automatic clauses for proposition-valued goals and set targets;
  - `obligations` blocks, with one respect proof per argument for quotients
    into sets.
- [ ] Dependent pattern matching on indexed families without K:
  - index unification by generated injectivity and disjointness;
  - reflexive equations deleted only with a setness proof;
  - coverage with impossible branches.
- [ ] Views: `match … using view` with any checked eliminator. This absorbs
  HoTT B5. Presentations are views derived from an equivalence. L2.7 needs
  the minimum D0b/F2 slice that supplies checked equivalences and transfer
  maps; broad transfer automation is a later extension.
- [ ] Canonical quotients: `quotient … canonical f`, represented by normal
  forms, with the quotient interface as a view.
- [ ] `deriving`:
  - `paths` (encode–decode characterization);
  - `decidable_equality`;
  - `universal`;
  - `irrelevance`;
  - `ind_prop` and `rec`.
- [ ] Nested declarations through strictly positive type constructors,
  elaborated through a specified, sound signature translation. General mutual
  lowering waits for the required H3/H4 fragment. An earlier H1 subset needs
  its own supported grammar, positivity argument and rejection tests; nested
  syntax alone does not make a multi-sort signature admissible.
- [ ] Legacy eliminator syntax (`induction … as … return`, the current
  expression `match`, `unpack`) stays parseable, so the archive keeps
  checking. The rebuilt library and the new reference use only `match`.
- [x] Remove the `cases` statement once `match` is released. `cases` never
  refines its goal, and `match` supersedes it. Its 24 uses in 11 archive
  modules are first rewritten to `match`, checked by the migration verifier.
  Then the parser, elaborator, formatter, highlighter, reference chapter 3
  and the error tables drop it. Done on 2026-10-04: the match statement
  takes sums apart, and the 24 archive uses and two in test sources
  migrated with identical terms. `cases` is refused with its match form,
  and the migration verifier reads a historical `cases` as `match`.

Completion, per release:

- **H1:** natural numbers, lists, W types, suspensions, the circle, `Trunc`
  and `Quotient` are declared and matched. The circle's `code` computes, and
  `code_meridian` holds by `rfl`. Status on 2026-09-28: the circle's winding
  number computes in source (`docs/examples/h1/winding.cubist`), with
  `cong(code, loop)` equal to `ua(succ)` by `rfl`; `Quotient`'s elimination
  into sets came with L2.2b (`quotient_induction` in
  `library/quotients.cubist`); the native comparisons are K2.4a.
- **H2:** `Vec`, `Fin`, well-typed syntax and `Id` are declared. `J` on
  `refl` holds by `rfl`, and `head` needs no `nil` branch.
- **H3:** a small context/type signature with genuinely dependent set/prop
  companion sorts and a joint interpreter computes a closed example. The
  `Real = initial CauchyStructure` and companion `neg`/`neg_neg` example
  remains deferred mathematical integration work.

At every release, non-structural calls, uncovered constructors, boundary
mismatches and missing h-level evidence are rejected with precise messages.

### 8. Computability as a checked property

The core was done on 2026-09-25 (work plan L0.1), and its two extensions,
L2.9a and L2.9b, on 2026-10-06. The milestone is complete. Delivered items
are documented in the language reference's Computability section.

- [x] Track each declaration's non-computing dependencies: user axioms,
  excluded middle, choice, resizing and any postulate. Compute them from the
  checked dependency graph, and show them in the inspector and CLI. These are
  the existing assumption lists; the CLI's `inspect` now prints them.
- [x] `computable def …`. The checker rejects the declaration unless the set
  is empty, and names the dependency chain. The experimental H1 marker
  was tracked separately and removed at H1's release on 2026-10-02.
- [x] `evaluate term expecting value;`, a checked normal-form test, and the
  CLI's `evaluate EXPRESSION` command.
- [x] L2.9a: patterns with holes on the expected side of `evaluate`, with
  an explicit matching contract and mismatch diagnostics. This does not
  inherently depend on H1. Done on 2026-10-06
  ([`evaluation.mjs`](../../web/translator/evaluation.mjs)): holes, pairs,
  injections and constructors match part by part, other expressions by
  normal form, and a mismatch names the part that differs.
- [x] L2.9b: witness readout from closed normalized truncations in the CLI's
  `evaluate` command. This needs native H1 truncation and G2's policy;
  it does not introduce a source eliminator from `Trunc(A)` to `A`. Done on
  2026-10-06 as `print(witness(t));` and the REPL's (and CLI's)
  `witness TERM;`.
- [x] Guarantee that evaluation unfolds definitions. The former unfolding
  hints were removed with the term checker. (`opaque def`, which changed nothing, has been removed.)
- [x] Recheck every `computable` and `evaluate` in CI. The migration
  verifier compares non-computing dependencies.

Only the truncation readout extension needs H1.

## Integration map

| Existing location | Planned work |
| --- | --- |
| [parser](../../web/cubist/parser.mjs), [formatter](../../web/cubist/formatter.mjs), [notation](../../web/cubist/notation.mjs) | Syntax, spans, roundtrips, and readable expansions. |
| [translator](../../web/translator/translate.mjs) | Proof-block statements, reconstruction, expected types, and parameter elaboration. Extract new matching/rewrite modules to keep this manageable. |
| [native elaborator](../../web/cubical-elaborator.mjs) | Native type/conversion queries, scoped contexts, checked witnesses, and dependency tracking. |
| [program](../../web/cubical-program.mjs), [modules](../../web/cubist/modules.mjs) | Rule registration, import identity, invalidation, and source inspection records. |
| [kernel adapter](../../web/cubical-kernel.mjs), [syntax codec](../../web/cubical-syntax.mjs) | Preserve native checking, handle ownership, and dimensions through generated terms. |
| [path library](../../archive/first-library/paths_.cubist), [path-over builders](../../web/translator/path-over.mjs) | Reuse proved congruence, composition, and transport constructions. |
| New: declaration elaborator and `match` compiler | `inductive`/`theory` to H's signature normal form; motive abstraction, index unification, coverage, structural recursion and obligations to eliminator applications (milestones 6–7). |
| Existing computability tracking | Preserve non-computing dependencies, `computable` and `evaluate`; with expected-value patterns and truncation readout (milestone 8, done). |
| [language reference](../../web/language.html), [CLI guide](../guides/cli.md), browser inspector | Document delivered syntax; show goals, inferred arguments, rewrite witnesses, generated eliminators, boundary diagrams and non-computing dependencies. The reference is rewritten into chapters with checked examples (see the [work plan](work-plan.md)). |

New helper modules and test files should be introduced with the milestone that
needs them. This roadmap adds no C kernel rule. Milestones 6–7 rely on the
kernel roadmap's G0 and H, which carry their own justification and review.

## Validation and completion

Each milestone needs focused parser/formatter tests, native acceptance and
rejection tests, and source-inspector coverage for its new constructs. Include:

- False equality, incorrect rule types, inconsistent pattern variables, free
  variables, unsolved holes, universe mismatches, and assumption tracking.
- Reverse paths, proof-dependent transports, dependent hypothesis chains,
  nontrivial loops, `IsProp`/`IsSet` boundaries, and truncation restrictions.
- Capture avoidance for term and interval binders, restricted faces, and
  preservation of higher inductive boundary conditions.
- Cyclic rules, conditional-rule recursion, cancellation, memory growth,
  import changes, and deterministic rule selection.

Use existing checks as applicable, adding focused tests for each implementation:

```sh
npm test -- tests/cubical-program.test.mjs
npm test -- tests/unfolding-syntax.test.mjs
npm test -- archive/first-library/primes.cubist
npm test -- archive/first-library/paths_.cubist
npm run test:browser
make lint
npm test
```

Run native kernel tests and sanitizers if kernel-facing changes warrant them.
For a release, recheck the full corpus. Compare migrated public theorem types
by kernel conversion and compare reported assumptions; generated proof terms
need not have the same syntax. Where later results depend on the particular
proof term, recheck those consumers and retain explicit coherence evidence.

Before expanding adoption, compare source tokens, author readability, checking
time, kernel steps, and arena memory against milestone 0. Include large shared
proofs and the existing selective-unfolding regression so automatic rewriting
does not destroy the benefit of folded definitions. Set numerical performance
budgets from that baseline and record results, rather than promising speculative
speedups or proof-size reductions.

The first useful release is milestones 1 and 2 plus their inspection and tests;
it was delivered together with milestones 0 and 3 on 2026-09-25.
The broader roadmap is complete when imported rules, dependent support,
argument inference, theories, inductive declarations and computability
checking have documented semantics, uses in the rebuilt library, and the
required validation. Update the
checkboxes and add a tactical handoff when implementation starts, recording
the supported fragment, assumptions, commands run, and next unfinished item.
