# CB5: diagnostics and public views

Status: implemented and validated in draft #238 on CB4 #237. CB4 is ready
after a clean second Claude review. CB5 has addressed the first external review and is entering round 2;
CB6 contextual sessions and CB7 retirement remain separate packages.

## Contract and implementation order

1. Preserve public labels, named interfaces and safe lint from #222 at
   `95c0a383`. Use retained binder identities and occurrence origins instead of
   reconstructing lexical identity from a term or label. Retire G5 exemptions
   only after their intended generated clients pass.
2. Carry source-qualified primary and related diagnostic sites through the
   existing source-unit and result boundaries. Imported expansion failures
   must not slice the client's text at the producer's offsets. Preserve authored
   origins and use existing expansion frames for caller blame and source links.
3. Adopt #225/#227's optional generated inspection and browser behavior using
   retained artifacts, checked publication state and binding-ID links. Remove
   ambient spelling lookup from inspection. Display failure must not change
   checking or invent an inspectable context for an unchecked declaration.
4. Print with a scoped ID-to-label correspondence. Public named-argument labels
   stay intact; display aliases are visibly identified. Source-expressible
   fragments must resolve back to the same binding structure. Otherwise print
   an explicit marker and identify the fragment as annotated display syntax.
5. Validate local/imported/renamed inheritance, labels and named clients,
   definition navigation, failed families, printing correspondence and the
   generated browser view. Run the full suite, corpus and production mutations,
   then publish a separate stacked PR and review with Claude (up to eight
   rounds with real findings, stopping on clean).

## Recurring design obligations

The [review record](../reports/capture-bindings-review-roots.md) shows source
ownership being lost at several consumers. CB3 now shares written-reference
lookup and rejects source actions from copied contexts. Extend those contracts
across diagnostics and non-editing views; do not add per-tactic patches or a
second source-location service. Local and caller-operand inspection must remain
available. Display labels cannot recover semantic identity, and reserved IDs
cannot supply checked inspection data.

Tracked examples from CB3 include imported inherited statement offsets,
generated definition/match annotations at foreign offsets, `rw` descriptions
and E452 reading substituted projection text, and view records for different
copies colliding at one source position. Generated instance selection belongs
with CB6; CB5 must preserve their identities rather than silently overwrite one.

## First checkpoint

Public operation/law telescopes no longer receive arrow-rewrite advice that
would remove their named arguments or generated capabilities. Ordinary unused
binders retain their advice. The adopted label/hover, named-constructor,
Hom/Iso and initial/free controls pass, including the distinguishing case where
the old arrow rewrite loses generated capabilities. Both G5 fixtures pass in
strict mode; their exemptions are retired. The focused generation/provenance/
lint run passes 49/49. This is not yet full CB5 validation or completion.

The next checkpoint carries structured diagnostics through the existing
source-unit/result boundaries: code, binding parameters, failure kind and
module-qualified primary/related spans. Source copies use their caller's
expansion site and retain the authored span. The existing final proof checks
accept a source site, so a late type mismatch keeps its closing statement
without adding kernel queries. Display text reads the program's existing
source map through `SourceUnit`; substituted rule descriptions share the
written-reference lookup. The generation/provenance/publication/proof-reference/
diagnostic run passes 95/95. Non-editing source-link ownership, distinct view
instances, the generated printer/UI and full validation remain unfinished.

The view collision has the same root as the repeated source-ownership findings:
an authored offset is a location, not an elaboration identity. Give each recorded
local observation its declaration and observation index, and carry its lexical
alias targets into inspection. This replaces reconstruction of view keys from
offsets and core-value matching; it needs no second registry. Source publication
shares the existing ownership rule, including non-editing annotations and
generated definition links. Copied observations remain available for their own
generated view but cannot overwrite or annotate the original source context.

The view checkpoint passes 53 focused observation, evidence, provenance,
inspection and scope tests. Pattern compilation preserves the original match's
source site while marking private aliases and additional compiled matches as
synthetic. This keeps checked coherence witnesses visible without publishing
foreign helper offsets. The existing witness regression caught and prevented
over-suppression; generated inspection and printing still remain to implement.

Optional `collectGeneration` now retains the original binding-aware declaration
artifacts from the publication groups, before lowering. It excludes live theory
records and never regenerates syntax from the checked terms. Existing publication
state separately determines availability, including failed and blocked groups.
The retention, publication and provenance run passes 47/47; the controls verify
identical checking work/results, inert syntax, exact declaration IDs, imported
origins, failure rollback and recheck invalidation. An unresolved source name
is refused before artifact construction, so the failed-family control uses a
well-resolved type mismatch instead. Printing and browser integration remain.

## Generated display checkpoint

The Generated Cubist tab and module selector now use retained declarations and
publication states. Unchanged source keeps its comments and inspection links;
failed and blocked families retain their syntax without claiming checked terms.
Editing and parse failures preserve the previous checked snapshot. Generated
links carry existing local/public inspection metadata by identity, including
the source module and binder position of an inherited helper.

The printer reuses the shared scope traversal to assign internal aliases and
keeps public parameter labels. It uses exact declaration and local IDs for
links, with no environment lookup or elaboration. Colliding captures, hidden
outer parameters, model openings, deferred patterns and notation contexts are
explicitly marked when ordinary source cannot express their binding structure.
Checked initial/free arguments use the existing core printer only after exact
global substitution; unsupported or potentially capturing fragments are marked.
Source-expressible fragments pass binding-structure round trips, including a
negative control that captures the wrong binder.

Primary and related diagnostic sites now navigate to their qualified source
positions. Imported binder navigation also preserves its precise offset, and
Back restores an example's checked source rather than opening the default proof.
The proof-block display control exposed an additional provenance gap: parser
rule records have spans but no `kind`, so the original source qualification
skipped them. The shared pass now qualifies every source span, including these
records; an imported inherited rewrite failure verifies caller and producer
locations. This closes the same source-ownership root recorded in earlier rounds.

Focused printer/provenance controls pass, including generated proof blocks,
imported navigation, captured declarations under model openings and a poisoned
environment lookup. The browser suite passes. A display sweep covers 45 source
modules and all 2,919 retained declarations without display failure.

Final validation of source head `9b1a7bda`: 1,241 tests pass out of 1,251,
with ten documented CB6 TODOs and zero failures. All 3,857 canonical checks
pass, and all four production mutations are killed. Source/tests stayed frozen
during validation. An older pilot test now asserts its exact qualified source
site instead of publishing that foreign offset into the pilot module.

Two intervening full/corpus runs hit five-minute wall-clock deadlines during
confirmed macOS maintenance sleeps, in different declarations. The unchanged
corpus passed in 22 seconds while awake; the final full run passed in 161
seconds with temporary sleep prevention. Compiler budgets were unchanged.
External review uses this validated implementation and stops on a clean round,
with up to eight rounds when real findings warrant fixes.


## External review round 1

Six display/location findings were grouped against prior review roots before
fixes; see the [review record](../reports/capture-bindings-review-roots.md).
Formatting placeholders now avoid every retained raw spelling, deferred uses
share their slot's marker, and disjoint scopes reuse display labels. Families
are placed by publication owner. Definition navigation carries its own qualified
site, distinct from declaring-module ownership, for checked and blocked symbols.
Synthesized helper statements retain their value origin and final inferred
checks locate rejections at their declaration. No resolver or registry was added.

Validation passes 1,247 of 1,257 tests, with the same ten CB6 TODOs and no
failures; all 3,857 canonical checks and all four mutation controls pass.
The browser suite and 45-module/2,919-declaration display sweep pass. The PR
remains draft for Claude round 2.
