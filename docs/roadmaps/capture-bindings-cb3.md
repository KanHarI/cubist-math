# CB3: deferred scopes

Status: implementation in progress on `cb3-deferred-scopes`, based on the
reviewed cleanup #235 at `790162dd`. CB4–CB7 remain subsequent packages;
the arbitrary-context REPL is still the CB6 deliverable.

## Completion requirements

- Complete retained pattern and proof scopes through the existing shared
  scope schema. Pattern roles resolve against the matched type and saved
  source inventory; destination constructors cannot change a saved decision.
- Complete lazy notation operands used as selectors. Preserve term and
  selection namespaces at source entry, including missing alternatives,
  through substitution, inheritance and elaboration. Remove the current
  explicit migration refusal only after these controls pass.
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
