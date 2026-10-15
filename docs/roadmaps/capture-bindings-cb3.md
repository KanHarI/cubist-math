# CB3: deferred scopes

Status: implemented; external round-1 fixes validated on `cb3-deferred-scopes`,
based on the reviewed cleanup #235 at `790162dd`. CB4–CB7 remain subsequent packages;
the arbitrary-context REPL is still the CB6 deliverable.

## Completion requirements

- Complete retained pattern and proof scopes through the existing shared
  scope schema. Pattern roles resolve against the matched type and saved
  source inventory; destination constructors cannot change a saved decision.
- Complete lazy notation operands used as selectors. Preserve term and
  selection namespaces at source entry, including missing alternatives,
  through substitution, inheritance and elaboration.
- Retain proof-token references in their declared namespaces, including
  simplification witnesses/sets and unfolding hints. No late ambient lookup
  may recover a retained reference.
- Adopt #221's checked model evidence, refinement/face handling and restricted
  recursive wildcard recovery using exact projection identities and the
  existing observation ownership. Preserve CB1's isolated recursive-attempt
  accounting and cumulative kernel work/deadlines.
- Exercise production generation, ordinary declarations, imported copies,
  substitution and replay. Preserve all existing semantic clients and add
  distinguishing controls for every newly admitted form.
- Run the relevant focused and full suites, corpus and production mutations.
  Publish CB3 as its own PR stacked on #235. Freeze code for Claude Code review;
  use up to eight rounds when findings warrant them, stopping on a clean round.

## Design constraints from earlier reviews

The [review obligations](../reports/capture-bindings-review-roots.md) apply
before every fix round. Record whether each finding repeats incomplete data,
re-derived source decisions, confused identity/availability, or lost source
ownership; trace all consumers before changing the representation. Prefer
extending the existing scope, resolution, identity and observation contracts.
Do not add parallel resolvers, captured live contexts or fallback modes.

Proof statements already declare their binder positions in the shared schema.
`intro`, `ext` and `obtain` therefore use those owned IDs directly; the goal
supplies their checked values/types at statement execution. A failed statement
never executes its continuation. They need no second deferred-block engine.
Their focused controls check nested universe introductions, repeated labels,
dependent pair extraction, initializer visibility and cloning, with distinct
accepted and rejected computations. Private environment keys do not become
kernel binder labels.

Lazy syntax arguments now retain separate term and receiver interpretations
when their source meanings differ. Both are ordinary retained syntax, so the
existing identity mapping, cloning and substitution cover them. The shared
expression-scope boundary selects the interpretation when consumed; entry
lowering leaves the alternatives inert. Dependency analysis records an
unresolved operand and exposes its conditional branches to capture planning.
Ignored operands do not force missing namespace members. A forwarded operand
keeps its caller scope and notation; only an explicit operand recipe changes
that notation. Controls distinguish standalone notations, attached rules,
local model parameters, destination shadowing, nested forwarding, imported
generation and unused failures. The focused run passes all 55 tests. The full
run passes 1,195 of 1,208 tests, with 13 documented later-phase TODOs and zero
failures; all four production mutations are killed.

Proof-token references now enter the shared traversal as retained expressions.
All existing cloning, remapping, substitution and dependency operations see
them there. Simplification set names expand once to exact checked member IDs;
local witnesses, hypothesis copies and unfolding hints keep their ordinary
lexical identities. The set inventory is explicit, including known absence
and ambiguity; default simplification remains a contextual search. Focused
controls cover source/destination collisions, copies, pattern slots, inherited
coherence proofs, wrong premises and missing checked receipts. Closing an
unfolding helper preserves term versus universe binders in both abstraction
and application. The first complete focused run passes all 64 tests. The
consumer audit adds source-set preparation to isolated scratch queries through
the same producer, including accepted-history replay and local shadowing.
Known source failures remain inert during entry lowering and throw when
consumed, so an ambiguous set cannot abort the generated declaration queue.
The 45-test consumer/diagnostic run passes. Recursive and path combinations
are restored in the bounded preservation generator; all 16 combinations pass.

The production audit covers the ordinary-declaration adapter pilot, retained
generated declarations/inductives, helper substitution and imported inheritance.
Retained pattern probes use saved constructor inventories and enclosing
resolutions; matched-type tables determine constructor roles. The unrelated
destination-constructor control passes. The adapter validates every reserved
late lookup against the language namespace. Original, uncopied source still
resolves in its source environment; it is not a destination fallback for a
retained reference. The old fixed-binder capture callbacks were removed with
the superseded producers in #235.

Generated/selected scope observation and notation expansion remain explicitly
unavailable to the contextual UI until CB6. This does not block their CB3
elaboration migration or authorize presenting them as selectable contexts.

Checked model evidence now travels with `Scope`, using exact projection IDs
and one scope-copy operation so transitions cannot omit it. Generalization
and face restriction transform witness, type and model together. Snapshots and
isolated queries carry the same evidence. Reserved/refused projections and
same-spelled destination values cannot supply it.

The #221 fallback restriction conflicts with CB1's explicit S1/Two witness:
rejecting every nonrecursive wildcard mismatch would remove an already checked
recovery required by the main roadmap. CB3 keeps existing implicit-path
eligibility. Successful recovery selects only its own observations; ordinary
failed recovery selects the written prefix and reports its primary mismatch;
resource failures stop recovery. Recursive retries retain CB1's isolated
fuel/work records; fallback remains directly charged. Consequently G8's
inherited zero-search expectation becomes one charged failed search, with
its exact intended diagnostic and body span unchanged. No special predicate
guesses which nonrecursive targets might admit checked coherence.

Validation so far: the 51-test proof/evidence/replay/observation run passes;
all eight evidence tests, including the additional scratch-session and exact
availability controls, pass. All four production mutations are killed. The
first full run identified G4/G4-flat as fixed plus the G8 contract conflict
above. Their obsolete exemptions are retired. The final full run passed
1,193 of 1,206 tests, with 13 documented later-phase TODOs and zero failures;
all 3,857 canonical checks passed. This is a partial checkpoint, not CB3
completion or an external review verdict.

Final implementation validation: `cb3-final-full.log` passes 1,199 of 1,212
tests, with 13 documented CB4–CB6 TODOs and zero failures; all 3,857 canonical
checks pass. All four production mutations are killed. Source and tests were
frozen throughout both runs. The earlier proof-reference full run had one
diagnostic-catalogue failure after extracting local lookup; the shared lookup
now leaves the existing diagnostic constructors at their consumers, retaining
their codes. External review begins from the committed implementation below;
this validation does not substitute for its verdict.

External round 1 found two defects at shared boundaries. Evidence collection
now uses the existing `isTerm` predicate before inference, because source aliases
also carry dimensions, constructor descriptors and lazy operands. Proof-field
errors read their labels and same-module occurrence sites from existing
substitution frames. These repeat the input-classification and source-ownership
roots recorded in the review obligations; neither needs new state or a resolver.
Controls cover all three non-term alias categories, correct and wrong
computations, local/imported fields, shadowing and exact owned token spans.
General imported statement spans remain the pre-existing CB5 gap.

Round-1 fix validation: 18/18 focused tests; `cb3-r1-full.log` passes 1,201 of
1,214 tests, with 13 documented later-phase TODOs and zero failures. All 3,857
canonical checks pass, and all four production mutations are killed. Source
and tests were frozen for these runs. Round 2 will review this small delta.
