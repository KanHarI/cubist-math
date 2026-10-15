# CB4: generated artifacts

Status: preparing on `cb4-artifact-builder`, stacked on CB3 #236. CB3's reviewed
worktree stays frozen; this package will not be published before that review
finishes. CB5–CB7 remain subsequent packages.

## Contract

Generated declarations compose retained expressions and binding identities
without printing source and parsing it again. A narrow shared builder handles
allocation, references, substitution and artifact freshening; it does not
resolve source names or introduce a second telescope representation.

Hom and Iso retain their existing variance/mapping plans and their distinct
support decisions. Equational initial/free support remains independent.
Parent references use explicit declaration identities and checked availability.
The ordinary declaration queue preserves independent base, derived, Hom, Iso
and initial/free publication groups and rollback.

Base model, Hom and Iso universes are inferred from their complete generated
types through ordinary elaboration, as in #220 at `807cd5e4`. Fixed domains
and preservation fields therefore contribute without a separate universe
calculator. Public parameter labels remain intact even though internal
binding identities are fresh for each artifact.

## Implementation and validation

1. Share the existing artifact allocation/reference/emission operations;
   preserve source-qualified origins and per-artifact cloning.
2. Replace Hom template construction with direct expressions, then Iso.
   Delete each superseded template/marker path, including its test-only API.
3. Use the common operations in base projections and initial/free artifacts;
   remove guessed model/Hom/Iso universe annotations.
4. Check semantic clients for preservation, identity/composition, inverse and
   fold computations, source/destination collisions, imported inheritance,
   exact parent availability, universe lowering refusals and FG1 rollback.
5. Retire G2's known-defect exemption only when its intended contract passes.
   Run the relevant suites, full corpus and production mutations. Freeze the
   resulting commit for Claude reviews, up to eight rounds with real findings,
   stopping on a clean round.

Before review fixes, compare with the recurring contracts in
[the review record](../reports/capture-bindings-review-roots.md). In particular,
source decisions belong to one producer, semantic identity is distinct from
availability, and origins must survive substitution and generation. Avoid
parallel builders or compatibility modes that preserve the text round trip.

The first checkpoint shares allocation, references, substitution and artifact
freshening between the existing direct base and initial/free builders. Their
existing retained-theory, initial/free and morphism controls pass 72/72 after
restoring the import still needed by the temporary morphism path. Hom/Iso
still use templates at this checkpoint; this is not CB4 completion.
