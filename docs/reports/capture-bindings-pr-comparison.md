# Capture and bindings: open-PR comparison

Comparison date: 2026-10-13. The ten open PRs below were read at the pinned
heads, including their relevant implementation and tests. This is a design
comparison and targeted #219 review, not a fresh full-suite certification of
each branch. The resulting [architecture and migration plan](../roadmaps/capture-bindings.md)
is proposed; no CB package is implemented by this document.

## Stack and disposition

| PR | Head | Base | Disposition |
| --- | --- | --- | --- |
| [#215: initial/free models](https://github.com/KanHarI/cubist-math/pull/215) | `ee1a5c36667aef448c4b05804ad4ff6efa9205c7` | `main` | Preserve checked constructors/folds, supported-equation boundaries and semantic clients. Migrate its retained syntax and generated templates. |
| [#216: frontend roadmap](https://github.com/KanHarI/cubist-math/pull/216) | `f0417ee0ee5f824f030069be0e6d1666696de0d1` | `initial-models` | Proposed replacement base; already includes merged FG0/FG1 work. Preserve the evidence harness and publication groups. |
| [#219: generation support](https://github.com/KanHarI/cubist-math/pull/219) | `d3d8f21eb3a2e8e64fbf5ec89ce2fb4b192aaa13` | `docs/frontend-generation-roadmap` | Replace nominal transformation/dependency resolution; retain complete-interface goals, distinct support plans and positive controls. |
| [#220: generated universes](https://github.com/KanHarI/cubist-math/pull/220) | `807cd5e4cda1942a06c6facee797107facf42405` | `fg2-generation-support` | Adopt ordinary universe inference and its tests; adapt construction to the common builder. |
| [#221: contextual evidence](https://github.com/KanHarI/cubist-math/pull/221) | `9c7034e0d73f4da60fa2fb47d0ad5d2297106c42` | `fg3-generated-universes` | Adopt checked evidence, refinement and fallback behavior. This solves a separate problem that binding IDs alone do not solve. |
| [#222: public provenance](https://github.com/KanHarI/cubist-math/pull/222) | `95c0a383c5751642dd868ef9ced04965bcd99c72` | `fg4-contextual-evidence` | Retain label, named-interface and lint guarantees; replace source matching by binding IDs and origins. |
| [#223: preservation gate](https://github.com/KanHarI/cubist-math/pull/223) | `49499aa1c56c1b345eb0021468123cec377fb4b8` | `fg5-public-provenance` | Adopt deterministic transformations, shrinking, mutation controls and cost observations; port implementation-specific mutations. |
| [#224: refactoring roadmap](https://github.com/KanHarI/cubist-math/pull/224) | `1fdc68a5e7da198f2b538dfbaa95e4bad40c97ca` | `fg6-preservation-gate` | Adopt implemented fixture/observer improvements and selected RC4/RC5 ideas. Supersede RC4's reliance on nominal binding repair; leave unrelated cleanup independent. |
| [#225: generated view](https://github.com/KanHarI/cubist-math/pull/225) | `d9c725b8d793c034d0bc6380fdc0356060331830` | `fg6-preservation-gate` | Retain optional artifact inspection, family status and browser behavior; render the new artifact representation. |
| [#227: generated inspection](https://github.com/KanHarI/cubist-math/pull/227) | `96b022f180ade9b6a6bba9e92616ba5f3207bf3e` | `feat/frontend-generation-view` | Retain source context, navigation and display guarantees; remove ambient spelling lookup from generated-reference links. |

#224 and #225 branch independently from #223; #227 follows #225. A
replacement can start from #216 and adopt behavior selectively. It need
not merge the full stack before changing its binding representation.
Superseding an implementation does not justify dropping its semantic tests.
This comparison does not merge, close or update any PR.

## What #219 demonstrates

The targeted review compared `d3d8f21e` with merge-base `c78c9d1a`.

1. **High: a hidden recursive call can bind to an unrelated global.**
   A nonrecursive helper calls an earlier recursive helper. Inlining that
   wrapper into an operation type or law exposes a bare recursive name;
   the replacement subtree escapes the type-purpose check. The field's
   capture scope then omits derived helpers, allowing that name to resolve
   to a same-spelled global or import. An incorrect client verifies. Without
   that global, the error becomes E343 rather than the base's E845.
   See [helper expansion and field capture](https://github.com/KanHarI/cubist-math/blob/d3d8f21eb3a2e8e64fbf5ec89ce2fb4b192aaa13/web/cubist/theories.mjs#L170).
2. **Medium: dependency analysis uses a later helper instead of an earlier
   header parameter.** `DependencyAnalysis.byName` combines all eventual
   fields with the interface. For `T(U < UU0, n : Nat)` containing an earlier
   `op(p : n = n)` and a later `def n : Nat := zero`, generation treats the
   earlier occurrence as a helper dependency. Hom/initial clients accepted
   by the base are refused on the head. See the
   [combined index](https://github.com/KanHarI/cubist-math/blob/d3d8f21eb3a2e8e64fbf5ec89ce2fb4b192aaa13/web/cubist/dependencies.mjs#L14).
3. **Low: an inherited binder's error range belongs to the wrong source.**
   Renaming runs before relocation and now reports the binder's position.
   An imported parent can therefore produce a range beyond the caller's
   length. Same-file parents conceal the source-ownership defect. See the
   [inheritance transformations](https://github.com/KanHarI/cubist-math/blob/d3d8f21eb3a2e8e64fbf5ec89ce2fb4b192aaa13/web/cubist/theories.mjs#L376).

The external review independently reported items 1 and 3. It also identified
two preexisting cases on `main` at `3c9090a9`: a bare recursive helper name
in a field type can be captured by a global, and helpers in family-sort
parameter domains are not expanded. Include both in the replacement's
acceptance tests without calling them #219 regressions.

A temporary experiment with a second field-type expansion/check, adding
derived names to capture scope and relocating before renaming fixed the
hidden-call and imported-range examples. It did **not** reject the bare
recursive-reference example: a call-only guard is insufficient. That
experiment was not applied to the repository. An interim repair needs
scope-aware validation of all free recursive dependencies, plus correct
ordered dependency resolution; repeating an inliner is not the final
architecture.

Source comparison through #227 shows these #219 binding paths persist:
the dependency resolver and scope traversal are unchanged, while later
theory changes address universes and labels. This is source evidence, not
a claim that every probe was rerun at every later head.

## Solutions to retain

### Complete interfaces and support plans: #219

Transforming a derived operation together with its parameter telescope is
the right direction. Preserve shared-domain grouping, public parameter
labels, legal helper-name shadowing, earlier checked recursive calls in
derived values, and separate Hom/Iso versus equational support decisions.
Replace `derivedSyntax`/`derivedRecord` conversion and name-indexed graphs
with one complete interface whose reference occurrences already have IDs.

### Universes and contextual evidence: #220 and #221

#220 removes guessed universe annotations from generated model, Hom and Iso
types. Ordinary elaboration sees their complete telescopes, including fixed
domains and preservation fields. Preserve that inference and its genuine
lowering-refusal tests; a binding graph must not become a second universe
inference engine.

#221 explicitly carries checked model evidence independently of presentation
aliases. Refinement changes the witness, type and model together, including
face handling. Its eligible recursive wildcard fallback retains the primary
failure when recovery fails and accounts for all attempted work. Preserve
these restrictions, resource errors and rollback behavior. Local REPL scopes
need this evidence alongside lexical identities, not an approximation rebuilt
from visible variable names.

### Labels, diagnostics and inspection: #222, #225 and #227

#222 separates lookup keys from public labels, preserves derived parameter
labels and protects public operation/law telescopes from misleading lint
simplification. Retain the observable behavior. Replace key/term-based source
matching with explicit binder/occurrence origins as consumers migrate.

#225 retains generated syntax before reference lowering, optionally and
without publishing failed families. #227 adds original source context,
imported navigation, declaration/reference inspection and a clear distinction
between displayed expansion and exported source. Keep these features and
their browser tests. In the
[generated renderer](https://github.com/KanHarI/cubist-math/blob/96b022f180ade9b6a6bba9e92616ba5f3207bf3e/web/generated-cubist.mjs),
resolved references can already use identities, but plain names can fall
back to the final module environment. Rendering must instead consume the
artifact's own binding links and origins; inspection must not resolve names
again.

Neither generated-view PR provides function-local contextual REPL sessions.
Their source and generated views supply useful entry points. The new backend
must replay a pinned scope in an isolated checker; the existing module REPL
is useful for command parsing, presentation and regression coverage.

### Preservation machinery and refactoring: #223 and #224

Adopt #223's bounded deterministic transformations, shrinker, exact mutation
controls and cost reports. Rewrite mutations against the new contracts.
An obsolete patch failing to apply does not establish that the new compiler
caught its defect. Keep the distinguishing semantic witness when retiring
an implementation-specific mutation.

#224 implements Cubist fixtures plus compact observations for outcomes,
spans, links, publication and work. Keep semantic expectations outside an
automatic error-golden rewrite path; account for every declaration and
unexpected diagnostic. Its proposed test pragmas and RC0–RC11 production
refactors are not thereby implemented.

From its [refactoring proposal](https://github.com/KanHarI/cubist-math/blob/1fdc68a5e7da198f2b538dfbaa95e4bad40c97ca/docs/roadmaps/refactoring-and-testing.md):

- Adopt RC4's single complete telescope, narrow builder and Hom-first pilot.
  Replace its proposed continued reliance on nominal `substituted` and
  `renamedApart` for retained bindings. The scope schema remains shared.
- Adopt RC5's structured diagnostic production and source ownership for
  binding-related errors. The entire historical English classifier does
  not need rewriting before the binding migration can start.
- Keep RC3 publication lifecycle consolidation independent while preserving
  its rollback and observer guarantees. Explicit scope lifetimes are needed
  for REPL replay; a wholesale lifecycle refactor is not a prerequisite.
- Leave broader test pragmas, worker-client consolidation, corpus tooling,
  syntax inventories and unrelated cleanup independently reviewable.

## Migration decision

Use the architecture's CB0–CB7 sequence. Prototype ambiguous pattern
resolution and isolated local-context replay early; both can invalidate an
overly simple identity-only design. Then migrate retained theory interfaces,
deferred scopes, artifact builders, diagnostic/inspection consumers and the
contextual REPL, deleting each replaced path as its semantic witnesses pass.

PR descriptions should identify their actual stack base and date any test
counts. #219's reported `fg1-publication` base and `808 / 803` validation
line are stale; the external review reports `842 / 837` with five TODOs.
Those reported counts are not new validation of this proposal.
