# Simplification and shorter proofs in Cubist

Status: first release delivered, 2026-09-25. Milestones 0–3 check through
the native kernel: grouped binders and introductions, both `have` forms,
`rfl`, `calc`, `rw`, `simp` and `simpa` with explicit, registered and named rule
sets, `simp at h as h2`, bounded conditional equality rules, checked type-path
transport, and the "Replace with simp only" action. Milestone 4's cubical
shorthand (`path i =>`, `p @ i`, `ext`, `along`, `apd_path`, `over`) shipped
early. A review on 2026-09-25 fixed four elaborator bugs and an older
name-capture bug; see the [implementation checkpoint](../tactical/proof-ergonomics-handoff.md).

The remaining dependent, cubical, induction and shared elaboration work moved
to the [HoTT and cubical automation roadmap](hott-automation-roadmap.md), and
kernel-facing interval work to the [kernel roadmap](cubical-kernel-roadmap.md).
Each open item below names its new owner. This roadmap keeps:
- general argument inference with `apply` and `refine` (milestone 5);
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
  #2–#4. It is now to be archived and rebuilt; its results are recorded in
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

Continue with the [PR-sized implementation plan](proof-ergonomics-implementation-plan.md)
and its [checked and exploratory sample files](../examples/proof-ergonomics/README.md).
That plan specifies reconstruction APIs, matching/occurrence semantics,
transactions, measurements, and cubical notation priorities. It brings
expected-type paths and pointwise equality forward without requiring general
argument inference.

The subsequent [HoTT and cubical automation roadmap](hott-automation-roadmap.md)
records why the current simplifier cannot reach path operations. It now owns
the remaining dependent, cubical and goal-derived induction work below; see
its [changes to the ergonomics plan](hott-automation-roadmap.md#changes-to-the-ergonomics-plan).

## Objective and current foundation

Reduce repetitive proof plumbing while keeping generated proofs inspectable
and checked by the existing cubical C kernel. Deliver a useful simplifier in
small increments, together with features that remove repeated arguments,
nested equality chains, and repeated structure projections.

The language has `intro`, `let`, `obtain`, `have`, `cases`, `exact`, `rfl`,
`calc`, `rw`, registered `simp` and `simpa`, and explicit `only` modes; typed and expected-type lambdas;
tuple patterns; and equality operations including `refl`, `sym`, `trans`,
`cong`, `transport`, and `apd`.
The [language reference](../../web/language.html) is the current syntax authority.
There is bounded equality-premise simplification, but no general proposition
premise solver, `apply`, or general implicit argument
syntax. Universe parameters are explicitly specialized by the elaborator until
the kernel's G0 makes universe-generic definitions checked kernel terms.

The checker already computes and unfolds definitions on demand, and
`with unfolding [names] { expression }` supplies a selective conversion
strategy. (An explicit `unfold(term)` existed before the cubical kernel and
was removed with it.) Neither uses arbitrary equality lemmas as rewrite rules. Preserve this
distinction: theorem simplification constructs paths; conversion remains the
kernel's existing judgment of computational equality.

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
- unfolding hints never hide computational content from evaluation.

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

Cache keys must account for the local context, universe specialization, live
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
- milestone 8 can start at once.

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
  an unambiguous domain. Consecutive `Universe` parameters in declarations
  also specialize correctly when grouped.
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
  `lib/cubical/proof-goals.mjs`.
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

Proposed example:

```text
import primes;

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
  premise search are bounded and recorded per declaration, and each tactic's
  time limit covers only its own search. Deterministic fuel, cancellation and
  naming the rules in a cycle remain.
- [ ] Keep associativity, commutativity, distributivity, and expanding
  definitions out of automatic default normalization. Explicit cyclic lists
  must still terminate with a useful failure. Cyclic lists fail with a cycle
  diagnostic. No library default rules are registered yet, so this remains a
  review criterion for the first default set (milestone 3).
- [x] Show used lemmas and intermediate equalities in the inspector. Each
  simplifier rewrite now exposes its checked path and selected rule.

Proposed example, after quantified-rule matching lands:

```text
import primes;

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
  library default set remains open and stays in this roadmap. Universe templates capture the rule environment
  at their definition, including for later specialization and inspection.
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
and rule choices without requiring authors to inspect kernel opcodes.

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
`along C by p from v`, `apd_path(f, p)`, `over C along p by { … }`, and
`simp`/`simpa` transport along checked paths of types.

### 5. Inferred arguments and goal-directed proof construction

- [ ] Add named arguments and `_` holes for values determined by a known
  function type, supplied arguments, or the expected result type. Implement
  scoped metavariables, occurs checks, and unresolved-hole diagnostics.
  Builds on the HoTT roadmap's goal layer (A5). Needed by kernel H2: indexed
  families are impractical without implicit indices, as in
  `cons(x, k + n, append(A, k, n, rest, ys))`.
- [ ] Add opt-in implicit binders, and infer level arguments where
  constraints determine them. After G0, universes are level expressions, and
  this item absorbs HoTT A9. Retain a way to supply every implicit argument
  explicitly. Reject ambiguous inference and universe lowering.
- [ ] Add `apply theorem;` and `refine term;` with visible subgoals and explicit
  witness obligations. Reuse the goal machinery (HoTT A5) rather than inventing
  assumed inhabitants for missing arguments.
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
Initial and free models need milestone 7 and kernel H.

- [ ] `theory` declarations: sorts with h-levels, operations with notation,
  laws, and `extends`. They generate:
  - `T.Model` as a Σ record with named fields and eta;
  - `T.Hom`;
  - `T.Iso`;
  - `T.equality : (M = N) ≃ T.Iso(M, N)`, generated through HoTT F1's
    structure identity machinery;
  - `T.Displayed`.

  Projections use HoTT A8's syntax.
- [ ] Scoped notation declared by a theory and opened with `open M`. Keep the
  current natural-number operators.
- [ ] `section (M : T.Model) { … }`: shared models and parameters,
  generalized deterministically, including dependencies that occur in types.
  Resulting signatures are shown.
- [ ] `initial T` and `free T on A` with `fold`, `fold_unique` and
  `universal`. These need milestone 7 and kernel H: H1 for single-sort
  theories, H3 for theories such as `CauchyStructure` and `CwF`.
- [ ] Algebraic normalization targets `CommRing.Model` and similar models. It
  is separate from generic `simp` and produces checked certificates.
- [ ] Expected-type completion and lemma suggestions insert checkable source
  and show the resulting obligations.

General typeclass search, implicit coercion networks, unrestricted higher-order
unification and broad proof search remain deferred. Structure scope stays
explicit.

Completion:
- a ring lemma takes one model argument and uses its notation;
- group structure identity is a generated instance, not a development;
- the forgetful map of an `extends` theory is generated;
- incorrect homomorphism preservation is rejected.

### 7. Inductive declarations and pattern matching

This is the language of the [kernel design](higher-inductive-types-design.md#5-language)
and of the [feature proposal](inductive-language-features.md). Releases follow
kernel stages H1–H3. The first release also needs HoTT A5 (motive
abstraction), D0a and D1's first slice (h-level evidence), and milestone 5's
holes.

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
  HoTT B5. Presentations are views derived from an equivalence.
- [ ] Canonical quotients: `quotient … canonical f`, represented by normal
  forms, with the quotient interface as a view.
- [ ] `deriving`:
  - `paths` (encode–decode characterization);
  - `decidable_equality`;
  - `universal`;
  - `irrelevance`;
  - `ind_prop` and `rec`.
- [ ] Nested declarations through strictly positive type constructors,
  elaborated as mutual declarations.
- [ ] Legacy eliminator syntax (`induction … as … return`, the current
  expression `match`, `unpack`) stays parseable, so the archive keeps
  checking. The rebuilt library and the new reference use only `match`.
- [ ] Remove the `cases` statement once `match` is released. `cases` never
  refines its goal, and `match` supersedes it. Its 24 uses in 11 archive
  modules are first rewritten to `match`, checked by the migration verifier.
  Then the parser, elaborator, formatter, highlighter, reference chapter 3
  and the error tables drop it.

Completion, per release:

- **H1:** natural numbers, lists, W types, suspensions, the circle, `Trunc`
  and `Quotient` are declared and matched. The circle's `code` computes, and
  `code_meridian` holds by `rfl`.
- **H2:** `Vec`, `Fin`, well-typed syntax and `Id` are declared. `J` on
  `refl` holds by `rfl`, and `head` needs no `nil` branch.
- **H3:** `Real = initial CauchyStructure` is declared. `neg` is defined with
  its companion, and `neg_neg` needs only the point clauses.

At every release, non-structural calls, uncovered constructors, boundary
mismatches and missing h-level evidence are rejected with precise messages.

### 8. Computability as a checked property

Every item but the fourth was done on 2026-09-25 (work plan L0.1). The done
items are documented in the language reference's Computability section.

- [x] Track each declaration's non-computing dependencies: user axioms,
  excluded middle, choice, resizing and any postulate. Compute them from the
  checked dependency graph, and show them in the inspector and CLI. These are
  the existing assumption lists; the CLI's `inspect` now prints them.
- [x] `computable def …`. The checker rejects the declaration unless the set
  is empty, and names the dependency chain. A `kernel extension: Hn` marker is
  shown but is not a non-computing dependency. The marker arrives with H1.
- [x] `evaluate term expecting value;`, a checked normal-form test, and the
  CLI's `evaluate EXPRESSION` command.
- [ ] Patterns with holes on the expected side of `evaluate`, and witness
  readout from normalized truncations in the CLI's `evaluate` command. Both
  wait for H1, while truncation is still an assumption.
- [x] Guarantee that evaluation always unfolds definitions and ignores
  unfolding hints. (`opaque def`, which changed nothing, has been removed.)
- [x] Recheck every `computable` and `evaluate` in CI. The migration
  verifier compares non-computing dependencies.

The remaining item needs H1.

## Integration map

| Existing location | Planned work |
| --- | --- |
| [parser](../../web/mathscript/parser.mjs), [formatter](../../web/mathscript/formatter.mjs), [notation](../../web/mathscript/notation.mjs) | Syntax, spans, roundtrips, and readable expansions. |
| [translator](../../lib/cubical/translate.mjs) | Proof-block statements, reconstruction, expected types, and parameter elaboration. Extract new matching/rewrite modules to keep this manageable. |
| [native elaborator](../../web/cubical-elaborator.mjs) | Native type/conversion queries, scoped contexts, checked witnesses, and dependency tracking. |
| [program](../../web/cubical-program.mjs), [modules](../../web/mathscript/modules.mjs) | Rule registration, import identity, invalidation, and source inspection records. |
| [kernel adapter](../../web/cubical-kernel.mjs), [syntax codec](../../web/cubical-syntax.mjs) | Preserve native checking, handle ownership, and dimensions through generated terms. |
| [path library](../../archive/first-library/paths.cubist), [path-over builders](../../lib/cubical/path-over.mjs) | Reuse proved congruence, composition, and transport constructions. |
| New: declaration elaborator and `match` compiler | `inductive`/`theory` to H's signature normal form; motive abstraction, index unification, coverage, structural recursion and obligations to eliminator applications (milestones 6–7). |
| New: computability tracking | Non-computing dependencies, `computable` and `evaluate` (milestone 8). |
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
npm test -- archive/first-library/paths.cubist
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
