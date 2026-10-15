# CB5: diagnostics and public views

Status: implementation in a separate worktree on CB4 #237 while its frozen
implementation is reviewed. CB6 contextual sessions and CB7 retirement remain
separate packages.

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
