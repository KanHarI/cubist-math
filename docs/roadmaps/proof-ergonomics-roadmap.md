# Simplification and shorter proofs in Cubist

Status: planning only, 2026-09-23. No implementation is claimed by this roadmap.
The next step is milestone 0. This document covers language tooling; it does
not resume any mathematical roadmap. All new syntax below is proposed syntax.

## Objective and current foundation

Reduce repetitive proof plumbing while keeping generated proofs inspectable
and checked by the existing cubical C kernel. Deliver a useful simplifier in
small increments, together with features that remove repeated arguments,
nested equality chains, and repeated structure projections.

Today the language has `intro`, `let`, `obtain`, `have`, `cases`, and `exact`;
explicit lambdas and induction motives; tuple patterns; and equality operations
including `refl`, `sym`, `trans`, `cong`, `transport`, and `apd`.
The [language reference](../../web/language.html) is the current syntax authority.
There is no `simp`, `rewrite`, `apply`, or `calc` tactic and no implicit argument
syntax. Universe parameters are explicitly specialized by the elaborator.

The checker already computes and unfolds definitions on demand.
`unfold(term)` explicitly normalizes a term and its type;
`with unfolding [names] { expression }` supplies a selective conversion strategy.
Neither uses arbitrary equality lemmas as rewrite rules. Preserve this
distinction: theorem simplification constructs paths; conversion remains the
kernel's existing judgment of computational equality.

For example, addition recurses on its first argument, so `0 + n` computes to
`n`. The proof that `n + 0 = n` is the existing
[`nat_add_zero`](../../web/proofs/primes.cubist) lemma. Applying that lemma
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
attribute becomes a new trusted proof rule.

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

Dependencies: 0 -> 1 -> 2 -> 3. Milestone 4 extends the supported cubical and
dependent fragment. Milestone 5 adds general argument inference on top of the
goal machinery from 1. Milestone 6 follows evidence from real proof migrations.
Small syntax conveniences in 0 can ship independently of the simplifier.

### 0. Establish examples and remove straightforward repetition

- [ ] Select representative proofs from `primes`, `paths`, `finite_counting`,
  `group_operations`, and `field_vector_spaces`. Record source token counts,
  repeated explicit parameters, checking time, kernel steps, and arena usage.
  Keep the original public statements and assumption lists as a baseline.
- [ ] Add grouped introductions, such as `intro A x h;`, by expansion to
  existing introductions, preserving an inspectable context at each binder.
- [ ] Add grouped typed binders, such as `(x y : A)`, and multi-binder lambdas.
  Add expected-type lambda binders only where the expected function type gives
  an unambiguous domain.
- [ ] Add `have h = term;` when its type can already be inferred, plus
  `have h : T = term;` as shorthand for an existing `have`/`exact` block.
- [ ] Define source spans and formatter behavior for each expansion.

Completion: conveniences elaborate to the same core meaning as their expanded
forms; shadowing, dependent binders, comments, formatting, and source inspection
work. Publish measured examples without claiming an unmeasured percentage gain.

### 1. Explicit rewriting and calculation chains

- [ ] Introduce the goal/reconstruction representation and a rewrite service
  initially accepting fully instantiated homogeneous equality proofs.
- [ ] Add `rw [p];` and `rw [<- p];`, with rules applied in listed order.
  Initially rewrite the first eligible occurrence in a documented traversal;
  add an explicit occurrence selector before supporting complicated targets.
- [ ] Support rewriting equality endpoints and ordinary applications with a
  fixed result type. Report unsupported dependent positions precisely.
- [ ] Add `rfl;` to close goals whose endpoints are definitionally equal.
  `rw` leaves a goal unless it can close it by this rule.
- [ ] Add `calc` for homogeneous equality chains, elaborating each step against
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

- [ ] Add `simp only [rules];` on equality goals. First permit instantiated
  proofs, then universally quantified equality lemmas through a restricted
  matcher. Infer parameters from the matched side and its checked type; require
  explicit arguments when inference is ambiguous. Full implicit syntax is
  not a prerequisite.
- [ ] Traverse supported subterms from children to parents, rewrite in a
  deterministic order, and repeat until stable or a resource limit is reached.
  Reuse congruence and path composition from milestone 1.
- [ ] Return checked endpoint witnesses, then close by conversion if possible.
  Otherwise retain a reconstructed residual goal for the next statement.
  Diagnose an unfinished block with that residual goal.
- [ ] Bound rewrite count, matching work, generated term size, and elapsed
  work; support worker cancellation. Detect repeated states and report the
  rules involved. A loop or exhausted budget never counts as success.
- [ ] Keep associativity, commutativity, distributivity, and expanding
  definitions out of automatic default normalization. Explicit cyclic lists
  must still terminate with a useful failure.
- [ ] Show used lemmas and intermediate equalities in the inspector.

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

- [ ] Add explicit metadata registering an already checked equality lemma.
  Since Cubist uses `def` for proofs and constructions, classify registrations
  by their checked type. Keep requests to unfold a definition distinct from
  requests to rewrite by a path; settle exact attribute syntax here.
- [ ] Define module export/import behavior, qualified identities, local scope,
  duplicate registration handling, priorities, and deterministic tie-breaking.
  Begin with a small reviewed default set; provide named domain-specific sets.
- [ ] Add `simp;`, `simp [rules];`, local exclusions, and `simpa only [rules]
  using term;`. `simpa` checks a reconstruction from the supplied term's type
  to the original goal, and fails if any obligation remains.
- [ ] Permit conditional rules only when every premise gets an actual checked
  witness. Initially discharge by an explicitly selected local hypothesis,
  conversion/reflexivity, or bounded recursive simplification; prevent recursive
  self-justification. Witnesses used by the conclusion must be retained.
- [ ] Add `simp only [h] at hypothesis;` first for hypotheses with no downstream
  dependencies, or bind a fresh simplified copy. Defer dependent replacement
  to milestone 4. Local hypotheses enter the rule set only when selected.
- [ ] Offer an action that replaces an exploratory `simp` invocation with an
  explicit `simp only` list of the lemmas actually used.

Completion: imports cannot leak local rules; unrelated unused rules add no
axiom dependencies to a proof; changes to a rule invalidate affected results;
explicit lists reproduce the proof's success. Traces explain failed premises
and rule choices without requiring authors to inspect kernel opcodes.

### 4. Dependent rewriting and cubical extensions

- [ ] Support selected dependent applications and pairs using transport and
  checked congruence lemmas. Rebuild changed local telescopes and the final
  goal together; preserve the original context for reconstruction.
- [ ] Add rewriting under binders with correct freshness and the necessary
  checked extensionality construction. Support dependent paths through the
  existing `PathP`/transport bridge.
- [ ] Curate separate path, transport, and structure simplification sets.
  Choose an orientation per family of laws; do not install both directions of
  the path/transport equivalence as automatic rules.
- [ ] Add proposition-specific goal transformations only with the required
  maps and `IsProp` evidence. Make set-specific rules explicitly require
  `IsSet`. Keep type equivalence and type equality operations distinct.
- [ ] Extend supported cubical constructors individually, preserving faces,
  higher inductive boundaries, and coherence witnesses.

Completion: dependent transport examples shorten without losing their path
witnesses; nontrivial circle loops survive simplification; mismatched fibers,
invalid faces, and unjustified proof irrelevance are rejected. Existing
univalence, path-over, and higher inductive examples continue to check with
their recorded assumptions.

### 5. Inferred arguments and goal-directed proof construction

- [ ] Add named arguments and `_` holes for values determined by a known
  function type, supplied arguments, or the expected result type. Implement
  scoped metavariables, occurs checks, and unresolved-hole diagnostics.
- [ ] Add opt-in implicit binders and infer universe specializations where
  constraints determine them. Retain explicit specialization and a way to
  supply every implicit argument. Reject ambiguous inference and universe
  lowering; do not silently change existing explicit signatures.
- [ ] Add `apply theorem;` and `refine term;` with visible subgoals and explicit
  witness obligations. Reuse the goal machinery rather than inventing assumed
  inhabitants for missing arguments.
- [ ] Add induction and case blocks whose motives come from the goal when
  uniquely recoverable; retain explicit motives and generalization controls
  for dependent arguments. Add `constructor`/witness conveniences as ordinary
  pair or sum construction, respecting truncation elimination restrictions.

Completion: representative algebra proofs omit repeated carrier and endpoint
arguments; inspectors reveal inferred arguments; ambiguity has a local remedy;
CLI and browser agree; every goal and metavariable is solved before acceptance.

### 6. Structures, notation, and targeted automation

Prioritize these suggestions using the baseline and migration results:

| Feature | Repetition removed | Design constraint |
| --- | --- | --- |
| Named record fields and record literals | Repeated nested projections and positional tuples for fields, groups, and maps | Elaborate to the existing dependent pair representation; honor field dependencies and retain expanded views. |
| Scoped notation for a chosen structure | Repeated `field_add(K, ...)`-style calls | Make the structure explicit in scope and inspectable; preserve current natural-number operators. |
| Sections with shared parameters | Repeating carriers, structure data, and assumptions on each local lemma | Generalize declarations deterministically, including dependencies appearing in types; expose resulting signatures. |
| `ext` with selected lemmas | Repeated function/structure equality boilerplate | Use checked extensionality or structure identity lemmas, with their assumptions and coherence obligations. |
| Expected-type completion and lemma suggestions | Repeated manual searches and parameter assembly | Suggestions insert checkable source and show the resulting obligations. |
| Algebraic normalization | Long polynomial or commutative algebra calculations | Separate from generic `simp`; produce checked certificates for a specified algebraic structure. |

General typeclass search, implicit coercion networks, unrestricted higher-order
unification, and broad proof search are deferred until concrete examples
justify their complexity. Prefer explicit structure scope and predictable
inference in the first releases.

## Integration map

| Existing location | Planned work |
| --- | --- |
| [parser](../../web/mathscript/parser.mjs), [formatter](../../web/mathscript/formatter.mjs), [notation](../../web/mathscript/notation.mjs) | Syntax, spans, roundtrips, and readable expansions. |
| [translator](../../lib/cubical/translate.mjs) | Proof-block statements, reconstruction, expected types, and parameter elaboration. Extract new matching/rewrite modules to keep this manageable. |
| [native elaborator](../../web/cubical-elaborator.mjs) | Native type/conversion queries, scoped contexts, checked witnesses, and dependency tracking. |
| [program](../../web/cubical-program.mjs), [modules](../../web/mathscript/modules.mjs) | Rule registration, import identity, invalidation, and source inspection records. |
| [kernel adapter](../../web/cubical-kernel.mjs), [syntax codec](../../web/cubical-syntax.mjs) | Preserve native checking, handle ownership, and dimensions through generated terms. |
| [path library](../../web/proofs/paths.cubist), [path-over builders](../../lib/cubical/path-over.mjs) | Reuse proved congruence, composition, and transport constructions. |
| [language reference](../../web/language.html), [CLI guide](../guides/cli.md), browser inspector | Document delivered syntax; show goals, inferred arguments, and rewrite witnesses. |

New helper modules and test files should be introduced with the milestone that
needs them. No new C kernel rule is expected; any proposed kernel change needs
a separate justification beyond convenience of elaboration.

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
npm test -- web/proofs/primes.cubist
npm test -- web/proofs/paths.cubist
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

The first useful release is milestones 1 and 2 plus their inspection and tests.
The broader roadmap is complete when imported rules, dependent support,
argument inference, and the selected conveniences have documented semantics,
representative library migrations, and the required validation. Update the
checkboxes and add a tactical handoff when implementation starts, recording
the supported fragment, assumptions, commands run, and next unfinished item.
