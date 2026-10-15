# CB5: diagnostics and public views

Status: implemented locally on CB4 #237, under full validation. CB4 is ready
after a clean second Claude review. CB5 has not yet had its external review;
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
modules and all 2,919 retained declarations without display failure. Full
regression/corpus and production mutation gates are running; external review
will use the committed, validated implementation.
