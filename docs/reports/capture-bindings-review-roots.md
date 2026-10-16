# Capture-binding review obligations

The CB2 reviews repeatedly exposed gaps in shared contracts. A fix is complete
only when the representation and every affected consumer preserve the missing
distinction. A passing reproduction alone does not establish that.

| Recurring root | Evidence across CB2 rounds | Contract to preserve |
| --- | --- | --- |
| Incomplete semantic data | Round 1: builtin/missing equality and omitted carrier universes/evidence. Rounds 2–4: grouped domains and anonymous term/universe positions. | The canonical representation carries every semantic position, including anonymous binders. Equality ignores display labels and source spans only where they are nonsemantic; it preserves reserved names, failures, binder correspondence and universe positions. |
| Consumers independently re-derive a source decision | Round 2: telescope/evidence order and fixed namespaces. Rounds 5–8: parent selections, operand receivers, file activations and replay disagree about the selection namespace. Round 7: notation validation and production disagree about meaningful operand views. | One source contract determines the expanded telescope, fixed references and selection classification. Consumers use its result. A receiver classified as a namespace or notation cannot later become an ordinary value through spelling lookup. Unknown inventories are not empty inventories. |
| Occurrence identity is confused with semantic identity or availability | Round 1: refused constructor identities. Round 2: parent Hom availability. Round 5: a query translator creates a different identity table. Round 6: distinct activation occurrences make equal source receivers unequal; unused namespace members affect sharing. | Identities belong to one compilation. Occurrence provenance, semantic captures and checked availability are separate. An attached notation's semantic context includes both receiver and rule-extension identity. Conditional uses carry only the alternatives they consume, and availability comes from explicit checked receipts/support plans. |
| Source ownership is lost at a phase boundary | Round 1: helper/inheritance failures lose the expansion site. Round 6: a deferred namespace failure loses its diagnostic. Round 7: source receiver offsets become client links. | Every transformation preserves source-qualified origins. A consumer reports expansion failures at the appropriate use and never interprets producer offsets as caller offsets. Source implementation references and caller operand references have separate observation ownership. |

Before applying fixes from a review:

1. Compare every finding with the previous rounds and group it by underlying
   contract. Record whether it is a recurrence, a new boundary of an existing
   root, or a new root.
2. Trace the information from source production through cloning, substitution,
   equality and dependency analysis to elaboration, publication and observation.
   Name where the distinction is lost before changing code.
3. Fix the shared representation or operation, then audit all consumers of that
   contract. Avoid a special case in the reproducer's consumer when another
   consumer can repeat the same loss.
4. Verify the intended result and a distinguishing incorrect result. Exercise
   static and deferred branches, source and destination collisions, copied or
   inherited syntax, and missing explicit receipts where applicable.
5. Lift a migration gate only when the entire newly admitted family meets its
   contract. Record remaining unsupported forms explicitly. Run the relevant
   integration and diagnostic checks before reporting completion.

For retained named rules, this means a source artifact with lazy operand
binders, explicit reader identities, operand-receiver syntax and optional model
attachment identity. Only the ephemeral elaboration receipt contains values or
environments. Invocation freshens the rule's owned bindings while each operand
keeps its caller scope. Written selection, file activation, operand recipes and
qualified operators use the same source classifier; deferred branches attach
extra rules only when that branch selects the declaring model. A standalone
notation opens no term labels. Model captures with different rule extensions
are distinct semantic notation contexts even when their receiver is the same.

Theory and named-rule source entry use retained producers. CB3's lazy operands
preserve their term and selection-namespace interpretations as retained syntax
children. The consuming expression boundary chooses the interpretation, while
cloning, substitution and dependency capture use the existing syntax traversal.
Treating an already resolved term operand as a selector could silently choose
a same-named model over a notation; entry lowering must preserve the alternatives.

The eight authorized external CB2 rounds are exhausted. Subsequent implementation
checks are not an additional external round or evidence of a clean external
re-review.

Production integration exercised the same four roots again: complete request
headers distinguish the enclosing theory head from parameter-scoped arguments;
source selections retain parent notation and lazy missing receivers; subordinate
translators reuse the checker's compilation registry; and source provenance
survives member lowering, inferred-argument observations and flattened generated
telescopes. Support planning examines every captured pattern alternative without
counting an unused binder or activation token as an unknown dependency. These
changes preserve the existing positive and distinguishing negative clients,
rather than changing them to accommodate generated artifacts.

## CB0–CB2 simplification audit

The follow-up audit found another consequence of the recurring roots above:
old paths and descriptive metadata survived after their responsibilities moved
elsewhere. Remove these instead of making every later consumer support both.

- CB0's mutation runner had an audit mode and configurable expected outcomes,
  although every supported mutation must be killed by a previously passing
  semantic test. It now has one mode, with optional mutation IDs. The distinction
  between a semantic failure, a failed precondition and a broken test run stays.
- CB1's scope collector still forwarded declaration registration and exposed an
  unused adapter factory. Declaration registration now goes only through the
  translator's compilation registry. Collection reads that registry.
- CB2 retained the full source lexical context on every member, and remapped
  it during inheritance, for an obsolete notation-recipe fallback. The source
  producer already resolves each operand recipe before admitting the operation.
  Validation now requires that recipe. Members retain their resolved syntax and
  open-interface IDs, without a second source resolver or lexical snapshot.
- Inheritance used to build and discard a remapped tree just to validate an
  interface map. It now shares correspondence validation with the actual remap
  operation. Invalid IDs and attempts to capture a local still fail before
  allocating a child binding.
- Helper expansion no longer stores an unused pending summary, and generated
  fields no longer copy unused checking trees and `interface-check` markers.
  The builder uses the complete checking expression in the base declarations;
  publication checks enforce admission. Dependency analysis still reports
  unresolved decisions to support planners.

The audit keeps the bounded mutation/shrinking evidence, distinct checking and
analysis expressions, inert DAG snapshots, transactional observation frames and
full-prefix replay. Each protects a tested semantic or resource boundary;
replacing these with plain JSON copies, normalized types or live scopes would
lose a guarantee. This followup preserves the default producer boundaries
established by CB2; it does not start CB3.

For a synthetic interface with 40 members and 200 unrelated imported bindings,
serialized member data fell from 716,897 to 101,787 bytes after removing the
lexical snapshots (about 86%). This measures that representation change only,
not total compilation memory or runtime.

Original audit validation before CB2 production integration: 1,191 tests,
with 1,143 passes, 48 then-existing TODOs and no failures;
all 3,857 canonical corpus checks passed. All four CB0 mutations were killed
by their expected distinguishing tests. The inheritance controls also reject
unknown IDs and local-binder capture without allocating child identities.

Validation after applying the cleanup to completed CB2: `npm test` passed
with 1,193 tests, 1,177 passes, 16 documented later-phase TODOs and no
failures. All 3,857 canonical checks passed. The targeted cleanup suite
passed all 102 tests, and all four production mutation checks were killed.


## Expanded cleanup after production integration

The first simplification pass was too narrow: it removed metadata while leaving
whole superseded producers behind. This repeats the second review root above:
consumers can independently reconstruct a source decision. Once CB2's retained
producers became the default and their clients passed, keeping both producers
and propagating a mode switch through replay no longer protected a migration
boundary. It kept a second implementation of that boundary alive.

The expanded cleanup removes the nominal theory and initial/free generators,
nominal named-rule capture, the lexical capture service and its duplicate
private environment keys, and the separate model-operand descriptor interpreter.
Theory, initial/free and named-notation source entry now have one implementation.
Replay uses the same implementation without producer-mode switches. Hom shape
planning and proposition classification consume retained identities directly;
their nominal/retained symbol adapters disappear. Initial source retention and
checked-argument elaboration share one module instead of importing each other.
The reference transformation tests remain, and source-resolution assertions now
exercise the retained resolver. No semantic positive or negative client was
removed to make this cleanup pass.

Following removed producers to their consumers also exposed diagnostic strings
that the old producer alone kept visible to the catalogue scanner. Active
namespace and notation failures keep their codes; only the gone implementations
are retired. Missing literal/numeral readers report their source import advice,
and a refused model extension keeps its original diagnostic and publication
behavior. New controls check these user-visible boundaries.

The audit also examined CB0's witness controls, mutation/shrinking and cost
records, and CB1's observation frames, scope descriptions and replay ownership.
Those mechanisms have separate tested responsibilities: semantic client
comparisons, failure classification, deterministic work accounting, discarded
attempt isolation, bounded DAG serialization and full-prefix reconstruction.
The cleanup removes duplicate registration and mode propagation around them;
it does not replace those guarantees with unverified shortcuts. Historical
source rewriting remains isolated, and the Hom/Iso template adapter remains
until CB4 replaces the actual template producer. Model numeral behavior remains;
the external cleanup review below replaces its nominal rule interpreter with
a direct operation application.

Expanded validation on frozen source: `npm test` passed 1,178 of 1,194 tests,
with the same 16 later-phase TODOs and zero failures. All 3,857 canonical checks
passed. All four production mutations were killed. The targeted retirement and
recipe suites passed 83/83 and 55/55 tests, respectively; both explicit notation
diagnostic controls passed. This was the frozen head for the first external
cleanup review.


## Cleanup external review, round 1

Claude Opus 5.5 at xhigh reviewed `ea1881bb` against the CB2 base `c908ffdc`.
All 59 compared binding and generation fixture results matched the base. The
review found three existing retained-path defects and four further cleanup
opportunities. Before applying fixes, they were grouped under two recurring
contracts rather than treated as isolated reproductions:

- Source decisions must have one representation and one consuming path.
  Theory printing still read the deleted producer's operand recipes; it now
  shares retained-recipe printing with named rules. Parallel notation label
  maps, duplicate universe labels and obsolete notation-inventory migration
  gates are removed. Theory, initial/free and named-rule entry share activation
  before parameters. The dead nominal substitution engine and its `renamable`
  metadata are removed. Model numerals call their operation directly, including
  the refused-operation case, so no general spelling-substitution interpreter
  remains for a single generated rule.
- Diagnostic ownership must survive phase changes. Unselected notation now
  uses the existing coded source errors; numeral terms are located when their
  term role is known, without changing interval endpoints. Declaration and
  directive catches share one failure record, and directive gaps retain its
  exact source span and dependency cause. Actual unmigrated syntax families
  still fail at their explicit gates.

Tests of the removed nominal engine were retired or moved to the live scope
traversal and source resolver. Existing semantic clients remain. Added controls
check unselected operators, negation, decimal and binary literals, the source
spans of missing readers and refused model extensions, and operand-view printing.
The first focused run passed 179 of 180 tests; its new numeral-span control
exposed the generated-header blame described above. All four diagnostic and
printing controls passed after correcting that boundary.

Final validation after round 1: `npm test` passed 1,177 of 1,193 tests, with
16 documented later-phase TODOs and zero failures; all 3,857 canonical checks
passed. All four production mutations were killed. An earlier full run had
only a stale coverage-index test name; the corrected index passed in isolation
and in the final full run. Source and tests were frozen throughout each run.


## Cleanup external review, round 2

Claude's review of `25c5f7ef` confirmed the first-round simplifications and
found two diagnostic boundary errors plus two lost scope controls. The same
source-ownership and source-decision roots apply. Imported rule bodies now
carry a caller blame site in the existing elaboration unit; application and
operator-section entry share that rule scope. Nested expansions keep the outer
site, while lazy operands retain their precise caller spans. This fixes lowered
nodes that no longer carry their authored origin, without a separate location
service or reconstruction of source environments.

Explicit parent namespace selection now determines missing-operation errors.
Decimal syntax keeps its missing-reader error inert until used as a term,
because the same numeric token can be an interval endpoint. That diagnostic
uses the existing failure representation and metadata filter: its wording
cannot change binding equality. Controls check both interval acceptance and
comparison, imported/nested rule errors, and precise caller-operand errors.
The retained resolver again has explicit controls for induction shadowing and
disjoint match branches, plus unpack, path and clause-coordinate scopes. Both
scope mutations reported by the reviewer fail the restored control.

The unused sequence-region getter/array branch and the remaining nominal
operator-section fallback are also removed. This round removes three net
application lines. The focused suites pass 169/169; the full run below includes
the final removal of unused sequence-region metadata.

Round-2 final validation: `npm test` passed 1,181 of 1,197 tests, with
16 existing later-phase TODOs and zero failures. All 3,857 canonical checks
passed, and all four production mutations were killed.

## CB3 external review, round 1 — diagnosis before fixes

Claude Opus 5.5 at xhigh reviewed `1e40d0a4` against #235 at `790162dd`.
It found two actionable issues and confirmed the CB3/later-package boundary.
Before changing code, both findings were compared with the earlier rounds:

- Evidence collection repeats the source-decision root (CB2 round 3): a shared
  alias boundary carries dimensions, constructor descriptors and lazy operands
  as well as terms. Its new evidence consumer independently classified inputs
  with two excluded tags. The shared evidence operation must use the existing
  core-term predicate before inference; callers must not grow separate lists.
- Proof-reference errors repeat the source-ownership root (CB2 round 1 and
  cleanup round 2): field substitution replaces the written occurrence with a
  projection expression. The existing substitution frame still records the
  occurrence's site and binding. Error reporting must consume that provenance,
  rather than the generated projection's label and offsets. A foreign site
  must never become offsets in the current module. General inherited error
  spans remain the explicit CB5 work; the newly admitted proof references
  must name their actual source occurrence now.

The intended fixes reuse `isTerm` and the existing expansion frames, without
new state, resolver modes or a diagnostic service. Controls cover each
non-term alias with intended and wrong computations, plus local/inherited
proof-field labels and precise same-module sites. The new diagnostic lookup
ignores foreign substitution sites. The surrounding imported statement catch
still has the pre-existing foreign-offset defect recorded by the reviewer;
the inherited-label control does not claim to repair that CB5 boundary.

Both fixes now use those existing contracts. The focused evidence,
proof-reference and diagnostic-catalogue suites pass 18/18. No new resolver,
state layer or compatibility mode was introduced.

Final round-1 fix validation: 1,201 tests pass out of 1,214, with 13 documented
later-phase TODOs and zero failures; all 3,857 canonical checks pass. All four
production mutations are killed. Source/tests remained frozen during validation.

## CB3 external review, round 2 — diagnosis before fixes

Claude reviewed `2e483917`. The evidence guard is clean, including models
passed through lazy notation operands. One actionable finding repeats the
source-ownership root: the first fix repaired `localReference` but missed
rule descriptions and freeze suggestions reading the same substituted nodes.
They slice the projection's offsets, producing the theory name in place of a
field or helper; applying the suggested edit breaks the proof. Renamed copies
also pair a child's binding label with the parent's written token.

The missing abstraction is one lookup of the existing written occurrence,
shared by diagnostic labels, simplification rule text and `using` suggestions.
When its source belongs to this unit, use that exact text and site together;
otherwise retain the binding label without reading foreign offsets. No new
frame data, state or resolver is needed. Before implementation, the consumers
were traced through `displayName`, E456, step descriptions and freeze edits;
local witness/target clauses cannot consume nonlocal substituted fields.
Controls will apply the suggestions and recheck field/helper/using proofs,
check E456 labels and test renamed inheritance against ordinary declarations.
General imported statement locations remain the separately reproduced CB5 gap.

The shared lookup now covers those consumers, and all 60 focused tests pass.
The remaining source-slice audit also reproduced `rw [fe]` displaying
"Checked rewrite using Parent" for a theory field, identically on this tree
and base `790162dd`. That existing description and generic generated-expression
views belong with CB5; no source edit is offered by that rewrite description.

Final round-2 fix validation: 1,203 tests pass out of 1,216, with 13 documented
later-phase TODOs and zero failures; all 3,857 canonical checks pass. All four
production mutations are killed. Source/tests remained frozen during validation.

## CB3 external review, round 3 — release boundary correction

Claude called the delta at `260c1a7d` clean and verified the shared lookup,
including compound references and imported binding labels. Its boundary notes
nevertheless expose a CB3 release defect: imported inherited simplification
links offer edits at the producer's offsets, and applying one can corrupt the
client document. The placement bug predates CB3, but the edit was newly exposed
by admitting theory simplification. We therefore treat it as actionable rather
than postponing it with CB5's non-editing views.

This is again source ownership, lost when link-site extraction retains a
keyword's offsets but drops its enclosing syntax's origin. The existing
publication filter already checks origin modules. Preserve that metadata at
the shared tactic/expression/calc-site boundary and in traced step links,
rather than adding bounds checks or a freeze-only exception. Validate imported
short clients and long clients where foreign offsets happen to fit, and retain
working local edits. No new ownership state is needed.

The reviewer also confirmed that the existing `rw` source slice affects E452
residual diagnostics as well as descriptions; both remain CB5 display work.

The shared link-site factories now carry origin/synthetic metadata, and traced
steps retain that same site. The existing publication predicate rejects foreign
tactic links. Focused tests pass 76/76, including local edit application and
short/long imported clients. Full validation passes 1,204 of 1,217 tests, with
13 later-phase TODOs and zero failures; all 3,857 canonical checks pass and all
four production mutations are killed. General generated-definition and match
annotations still need CB5 provenance; they offer no source edits.

## CB3 external review, round 4 — diagnosis before fixes

Claude reviewed `cc4d6efd`: imported actions are fixed and local inspection is
preserved, but a same-module inherited copy can offer an edit to its parent's
statement using a rule registered only before the child. Applying that edit
breaks the source; when only the child verifies, it is also the UI's sole edit.

The root is stronger than module ownership: a copied elaboration does not own
the written source context. Existing expansion frames identify that distinction.
The shared site extraction must treat source copies as synthetic observations;
ordinary generation lowering may still expose its authored source. Audit all
expansion producers, not just inheritance: notation already suppresses its
implementation recorder, lazy operands return to their own source scopes, and
substitution inserts synthetic expressions. Use the existing provenance rather
than add per-copy state, special freeze guards or a list of forbidden tactics.
Tests will register a rule between parent and child, apply every offered edit,
and cover a failed parent with a verified child, where UI deduplication cannot
hide the destructive suggestion.

The shared factory now marks source-copy expansions as synthetic observations;
authored syntax and generation lowering remain eligible for local source links.
All 77 focused tests pass. Full validation passes 1,205 of 1,218 tests, with
13 later-phase TODOs and zero failures; all 3,857 canonical checks pass and all
four production mutations are killed. Source/tests were frozen for these runs.

## CB3 external review, round 5 — clean

Claude reviewed `b8823f65` against `cc4d6efd` and found no actionable defects.
It audited all expansion-frame producers and swept plain, renamed, multilevel
and diamond inheritance with intervening rule registration. All five published
edits applied without new gaps; the previous head offered destructive child
edits. Local inspection parity covered 110 source files, with only duplicate
copy links removed in seven files. Imported notation operands keep their own
inspection and working edits. Both reverting the fix and treating ordinary
generation as a source copy fail the regression control.

The context-ownership rule therefore closes the repeated source-edit findings
without additional state or tactic-specific guards. Non-editing name annotations
outside the site factories and shared-binding view collisions remain explicit
CB5/CB6 work. CB3 review stops at round 5 of eight; no further round is needed
without a new finding.

## CB4 external review, round 1 — diagnosis before fixes

Claude reviewed `285f7223` against `3edc0d58` and found no semantic, identity,
availability, universe or rollback defects. Two low-severity findings repeat
the cleanup's source-decision root: representations used only by the removed
text producer remain after identities replace textual resolution.

The parent record's `fields` spelling list has no remaining consumer; the
direct builder uses `fieldIds` and `kinds`. Delete that list. Generated local
labels are still freshened across the entire Hom/Iso family, so unrelated
earlier generation changes later printed names. Choose a display label once
per stem, while allocating a fresh binding ID for every occurrence. Existing
core printing already disambiguates nested binders with equal display labels.
No new resolver, builder layer or compatibility path is needed.

The review checked emitted reference scope over 128 theory builds and 11
initial/free builds, including a mutation that reuses source input IDs. It
also checked fixed/dependent indices, collisions, named arguments, multiple
universes, parent inheritance, rollback and the strict G2 contract. Its notes
about anonymous labels and generated diagnostic locations belong to CB5's
recorded display work; generated spans are unchanged, while inferred bodies
no longer have the old synthetic `exact` statement's location suffix.

The first focused run rejected caching public parameter labels: a theory
parameter named `A` collided with the generated model parameter. Public
telescope labels are an API even though local references use IDs. Apply the
per-stem reuse only to the existing `local` role; parameter/universe allocation
keeps distinct public labels. The existing theory-resolution collision client
detected the mistake before commit, without requiring a new exception or mode.

Corrected validation: 133/133 focused tests; the full run passes 1,210 of
1,222 tests with 12 later-package TODOs and zero failures. All 3,857 canonical
checks pass and all four production mutations are killed. Source/tests were
frozen throughout the final gates.

## CB4 external review, round 2 — clean

Claude reviewed `f2dd9212` against `285f7223`. Both cleanup findings are fixed,
with no new actionable findings. Named public parameters remain unchanged;
internal equal-label binders retain distinct IDs and print without capturing
globals. A 24-file before/after comparison preserves verdicts, types and
output modulo the intended internal-label changes. The source head and full
validation remain unchanged. Stop at round 2; no speculative fixes follow.


## CB5 external review, round 1 — diagnosis before fixes

Claude reviewed `791f5e9e` against `1670411c`. Six actionable findings repeat
identity reconstruction and source ownership defects from earlier rounds.
The existing full suite, corpus, browser and mutation gates pass, but do not
cover these display and navigation cases. Before edits, the fixes are grouped
by the missing contracts:

- Formatting tokens must be fresh against every raw spelling in the retained
  graph, not only binder labels. Member and named-argument labels cannot be
  mistaken for an identity placeholder. Deferred references must use their
  slot ID's marker, including references with member paths. Display aliases
  belong to lexical scopes; disjoint scopes need not rename each other's
  binders. Reuse the existing bounded traversal, scope mapper and ID maps.
- Publication ownership and authored location are different facts. Interleave
  families by the existing publication owner, without a member-offset test.
  Keep the declaring module used for outputs/imports separate from a qualified
  definition site used for navigation and documentation. Checked and blocked
  generated symbols must consume the same site helper. Do not repurpose
  sourceModule: that would hide locally declared inherited symbols.
- A closing kernel check must carry its source site just as a closing proof
  check does. Synthesized exact statements must retain their value's origin.
  Locate at these boundaries, without changing unrelated import-failure
  messages through a blanket declaration-catch fallback. Share the existing
  substitution-frame lookup used by source text and written references.

Controls will cover real field/placeholder collisions, disjoint and overlapping
scopes, nested slot correspondence, local/imported derived-family ordering,
short and aligned long clients, blocked inherited symbols, and local/imported
closing-check diagnostics. No new resolver, registry or compatibility mode is
needed. The reviewer's scratch prototypes are evidence, not patches to copy.


The fixes now use those contracts. Formatting freshness scans the retained
syntax graph once; aliases use the existing lexical context and simultaneous
binders. Slot references and binders share markers by ID. Family placement no
longer compares offsets. Checked and blocked symbols share a qualified
`definitionSite`, leaving declaring-module classification intact. Helper
statements retain the value origin; inferred closing checks retain a fallback
site without changing the declaration catch. The substitution-frame lookup
has one implementation.

All 32 focused controls pass. Final validation passes 1,247 of 1,257 tests,
with ten CB6 TODOs and zero failures; all 3,857 canonical checks pass. All four
production mutations are killed. The browser suite passes, including inherited
generated definition navigation. The display sweep covers all 2,919 retained
declarations in 45 modules without failures. Source/tests stayed frozen through
these gates. Round 2 reviews this delta; CB5 remains draft until review is clean.


## CB5 external review, round 2 — diagnosis before fixes

Claude reviewed `ff7bc7a9` against `791f5e9e`. The six previous fixes hold;
alias annotations fall from 1,341 to 86 across the same 45-module sweep.
Three actionable findings remain, including one regression in scoped alias
allocation. Compare them with the earlier rounds before changing code:

- Operand grouping is a distinct syntax-preservation obligation. Parentheses
  around an entire binary expression do not delimit a left operand's binder
  body. Reuse the renderer's existing `atom` boundary for infix/path operands
  and calculation left sides, instead of adding a second precedence table or
  special cases for individual quantifiers. Round-trip controls must include
  forall, exists, grouped binders, lambdas and path lambdas, plus a checked
  client that distinguishes the changed proposition.
- Alias allocation repeats the incomplete-scope-description root: a traversal
  callback's current scope is not the full set of binders sharing that node's
  regions. Read every binder from the shared `scopesOf` schema before choosing
  a label. This may add a few aliases between disjoint regions of one node;
  it retains reuse across separate nodes without a second visibility model.
  Cover induction index/hypothesis overlap and clause coordinates, as well as
  the existing disjoint-scope and capture controls.
- Source ownership remains incomplete at a UI consumer. The new definition
  site fixed the source link, while deep-link highlighting still accepted bare
  symbol offsets. Make highlighting consume only qualified sites and share
  definition-site extraction with the link. Qualify local URL offsets, lint
  and gap sites at their source boundary. A foreign definition can be inspected
  without highlighting unrelated local text; its source link remains usable.

Remove the unused recordModule text parameter, and describe hidden-local
markers as hidden by another binder rather than specifically a public
parameter. These changes need no new registry, resolver or printer framework.


The broader grouping control also exposed an older spelling error before
validation: the frontend renderer emits path lambdas as `<i> body`, while the
current parser accepts `path i => body`. Correct that producer to the actual
grammar and cover a checked generated path proof, alongside the path-operand
round trip. This is the same source-syntax fidelity boundary, not a new mode.


The fixes now use those existing boundaries. All 36 focused controls pass,
including a checked client that distinguishes the original proposition from
the previously misprinted one. The browser regression confirms that a name-only
inherited deep link does not highlight a coincident local offset, while its
source link reaches the authored definition. Full validation passes 1,251 of
1,261 tests, with ten CB6 TODOs and zero failures; all 3,857 canonical checks
pass. All four production mutations are killed, and the display sweep renders
2,919 declarations in 45 modules without failure. Source/tests remained frozen
through validation. Round 3 reviews this delta; CB5 remains draft until clean.


## CB5 external review, round 3 — diagnosis before fixes

Claude reviewed `39a2a4f0` against `ff7bc7a9`. The grouping, overlapping-scope
and qualified-navigation fixes hold, including adversarial binding round trips
and the recorded validation. One cosmetic regression remains: `atom` wraps
expressions that the renderer already parenthesizes, and wraps a transparent
notation-argument wrapper even when its body is atomic. This adds visible noise
to generated declarations without changing their binding structure.

This finding is a local omission in the existing renderer's atom classification,
not a recurrence of identity reconstruction or source ownership. Extend that
classification to already-delimited forms and delegate transparent notation
arguments to their body. Keep the binder grouping controls and check the exact
nested-operand output. No precedence service, display mode or new registry is
needed. The suggested alias-number separator is a nonblocking style preference;
existing distinct, binding-faithful labels remain valid, so leave that policy alone.


The small renderer change passes all 27 binding-display/generated-view tests,
including the existing binder round trips and the exact nested-operand control.
The display sweep again renders 2,919 declarations in 45 modules without
failure. The last full suite, browser and mutation gates remain recorded at
`39a2a4f0`; this follow-up changes only display grouping. Request a focused
Claude delta verification, without reopening the already-clean CB5 audit.


## CB5 external review, round 4 — clean

Claude reviewed `57a1b9c9` against `39a2a4f0` and found no actionable issues.
The extra parentheses are gone and the required grouping remains. All 40
changed corpus-view lines differ only in parentheses; existing atom callers
also pass the reviewer's binding round trips. A fresh 45-module view dump has
no errors. The standalone negation fixture lacks its notation inventory, so
that probe was inconclusive; negation output in the corpus matches the earlier
base. The 10 binding-display tests pass independently.

Stop at round 4. Full-suite/browser/mutation validation remains the recorded
run at `39a2a4f0`; the rendering-only follow-up has 27 passing printer tests,
the complete display sweep and clean external verification. CB5 is ready;
CB6 contextual sessions and CB7 retirement continue in separate PRs.

## CB6 notation and cost audit — diagnosis before further fixes

The shadowed-notation query exposed the recurring visibility/availability
confusion. Its lexical source context names the correct ID, but the query's
value inventory was rebuilt through the caller's public notation labels.
Consume the private checked receipts already present in the environment;
the retained lexical context alone decides visibility. The distinguishing
test passes different source and caller notations under the same label.

The cost probe also exposes a recurrence of CB1's mutable-permission ownership
issue. Lazy caller descriptions embed recursion permissions, so their entire
environment description is rebuilt at every observed point. The nested-function
fixture now has 1,625 available points and roughly 1.30 million objects under
its binding descriptions. The larger sections fixture adds about 274 MB of
heap during collection. These counts include newly supported contexts and are
not comparable to CB1's mostly-unavailable pilot as marginal overhead figures.

Before optimizing, separate point-specific mutable permissions from shared
immutable environment descriptions, as CB1 already does for the immediate
scope. Cover nested and explicitly scoped lazy operands, and verify that a
permission change alters replay validation without mutating an earlier point.
Do not add another cache of live scopes or a second serialization framework.
The correction now follows that boundary: mutable caller permissions join the
per-point recursion description, while immutable operand/environment data are
shared. Direct, nested and explicitly scoped caller controls preserve earlier
descriptions and distinguish changed permissions. The same cost fixtures now
measure 63.58 MB and 206.17 MB heap growth, respectively. Collection remains
optional and expensive; the full measurements and qualifications are in the CB6
roadmap. No CB6 Claude review has run yet.

The remaining inductive-self gap was another missing introduction boundary,
not a missing final-module lookup. Record the exact reserved type/constructor
identities when they enter the provisional signature telescope. Queries then
use checked local variables and the existing uniform-parameter rules. Tests
distinguish later constructors, changed parameters, failed final admission and
initial/free generated instances; none publishes the unfinished signature.

The implementation at `9187cadf` passes all 1,299 tests with no TODOs, all 3,857
canonical checks, both browser suites and all four production mutation checks.
Source and tests remained frozen through these gates. External round 1 reviews
the complete CB6 delta against CB5; compare any findings with these ownership,
visibility and introduction-boundary diagnoses before applying fixes.

## CB6 external review, round 1 — diagnosis before fixes

Claude reviewed `5e469618` against CB5 `4c2b4f3a`. All 108 targeted tests
pass, but independent probes expose four regressions. The review compares
source collection on/off and the CB5 base; the full report and reproductions
are retained with the local review artifacts.

- Identity receipts acquired semantic visibility: `sourceBinding` registers
  its private alias as a second `localSources` entry. Evidence enumeration
  then counts a let twice and keeps using it after its public name is shadowed.
  Collection can turn a refused source into an accepted one, and `/prove`
  repeats the difference. This recurs the identity/availability root from CB2
  and CB6's earlier notation diagnosis. Correct the producer: only the actual
  introduced key is a semantic local. Keep private receipts for identity and
  shadowed-value inspection; add no consumer filters or deduplication service.
- Refinement derives identity keys from the optional scope collector. A copied
  lazy caller retains its binding records but has an observation-free query
  unit, so a dependent match crashes. This repeats the query ownership root.
  Both introduction and refinement must use the existing compilation registry,
  which already owns their table, without deleting caller binding records.
- Model numeral production marks its authored token as a copied notation body,
  suppressing its definition and view links. This repeats CB3/CB5's source
  ownership root. Preserve the numeral's authored origin at its producer;
  scope instances already have exact occurrence IDs. Do not relax copied-source
  link filtering or add a second link path.
- Inductive scope labels reuse definition-only self-reference metadata, so a
  name in its own parameter domain receives a misleading recursion diagnostic.
  Carry the declaration kind with its name in the existing unit metadata;
  observation labels and definition-only diagnostic policy then consume the
  appropriate part, without another registry or diagnostic classifier.

Verify the two shadowed-evidence sources and proof queries, automatic obligations,
canonical hlevel on/off results/fuel/work, lazy dependent matching with scratch
history, authored numeral links and provisional inductive contexts. Keep the
independent source controls, source-qualified link ownership and compiler limits.

The fixes now follow those existing boundaries. Shadowed let/obtain evidence,
automatic obligations and proof-query controls pass, including positive source
controls with the shadow removed. Canonical hlevel and obligation fixtures have
identical on/off outputs, diagnostics, links, fuel and kernel work. Lazy dependent
matching and scratch-history replay pass. All 367 canonical `notation_literals`
links equal CB5, and provisional inductive context labels remain intact. A new
link assertion initially read a nonexistent `kind` field; after correcting it
to the actual local-view identity, all 11 notation tests pass. Full gates and
external delta verification remain pending.

The first full run of these fixes passes 1,302/1,310 tests and all 3,857 corpus
checks, but reveals three follow-ups before external verification. Six failures
come from a pilot harness using a scope registry distinct from its checker's
registry; it must use the shared production registry, and translator construction
must reject contradictory identity owners. A resource-injection hook still reads
the old declaration-name shape and must follow the metadata change.

The remaining failure is real: recursion permissions contain entries for both
an introduced key and its observational alias. After nested refinement, the
alias's older entry is no longer callable, but query key remapping collapses both
keys to one ID and lets the stale entry overwrite the valid one. This is the
same receipt-versus-permission root, not a reason to restore search visibility.
Apply the source recursive-call consumer's existing alias/value validity check
before collapsing keys. Preserve the valid source permission and reject stale
ones; add no new recursion eligibility rule or spelling fallback.

The follow-up implements that contract at the existing key-remapping boundary.
All 37 declaration/compilation/replay tests pass, including the eight failures;
source-call permissions and negative recursion controls are unchanged. No
observer-derived local visibility was restored. Final gates rerun before round 2.

## CB6 external review, round 2 — diagnosis before fixes

Claude verified all four round-1 corrections and the registry/permission
follow-up at `8ec414c9`; all 133 targeted tests pass. It found one low-severity
inspection regression: shadowed variable-valued lets still refine in branches,
but shadowed compound values and their types do not. `branch` used the visible
`localSources` inventory to decide which stored definitions need refinement.

This is the same identity/availability conflation in the other direction.
A private receipt does not grant search visibility, but it must retain the
refinement behavior of the source introduction it records. Record that fact
alongside the binding in the existing `sourceBindings` receipt, where the
presence of source-local metadata is known. Branch refinement consumes this
fact for shadowed receipts as well as current locals. Do not infer it from a
binding role or label: opened model members have local-role identities but
were never semantic locals, and must retain their existing checking behavior.
No second visibility map, query-only renderer fix or role-based fallback is
needed. Verify visible/shadowed rows for compound lets and dependent proofs
through match/induction, and preserve model-opening on/off behavior.

The fix stores the introduction fact on each existing receipt and consumes it
at the shared branch transition. All 76 focused command, notation, replay and
scope-point tests pass. New controls compare visible and shadowed compound lets,
dependent proofs and obtain components in both match and induction branches;
opened-member behavior and collection on/off kernel work remain identical.
The first test fixture lacked its pair's required expected type; adding that
explicit type corrected the fixture without changing the implementation.

## Independent audit during CB6 round 3 — diagnosis before fixes

At frozen 280b4592, `/prove { let h := p(tt); let h := tt; hlevel; }` succeeds in a context `A : U0, p : Unit -> IsProp(U0,A)` with goal `IsSet(U0,A and A)`, where the equivalent authored block fails. Separate scratch entries `let h := p(tt)` then `let h := tt` likewise leave the old h available to `/prove { hlevel; }`. The no-h query fails and the unshadowed h query succeeds. Probes are cb6-visibility-audit.log and cb6-visibility-opening-audit.log. This is an additional finding, not a failure of the narrow round-2 receipt refinement fix.

Shared root across rounds: identity is distinct from lexical visibility. Round 1 removed observation aliases from localSources, but actual retained/scratch introductions have unique private keys; replacing the visible spelling does not overwrite that key. localSources therefore still lists the old semantic local. Proof search consumes that inventory, while `/locals` derives visibility from the lexical context and correctly calls the same row hidden. This is a source/query behavior mismatch, not kernel unsoundness.

Trace all introduction forms before changes: ordinary and retained locals, scratch lets, proof-block binders, obtain, patterns, dimensions and model openings. Maintain one semantic-local inventory at introduction/alias transitions, keyed for execution but shadowed by source label. Preserve binding receipts and their refinement facts independently; binding-aware introductions already have registered IDs even without an observation collector. Do not add an hlevel-only blacklist, a query-only scope rewrite, another registry or a second resolver. Compare source controls, retained declarations and scratch history, retaining both positive and negative results. The pending Claude round-3 report must remain pinned to unchanged `280b4592`; fold the isolated fix into the reviewed branch only after that review finishes, then request focused verification of this shared-boundary correction.

The reviewed worktree remains unchanged while an isolated worktree holds the
follow-up. Scope introduction reads existing retained identities without an
observer and removes shadowed semantic locals by their source label; public
alias introduction does the same for model openings. Receipts stay available
for refinement. Single-alias introduction delegates to the multi-alias method,
removing duplicated transition logic. All 18 command tests and 71 other focused
checks pass. The first fixture matrix exhausted the unchanged kernel-session
limit by retaining every control until test completion; immediate disposal of
each completed control corrects the harness. The independent source controls
show the intended positive and negative verdicts for let, obtain, intro and
model opening. A saved alias remains usable after the original label shadows.

The full run at `ab68362d` passes 1,315 of 1,317 tests and all 3,857 corpus
checks. Both failures are older binding-syntax pilot fixtures that use an
independent adapter table with a production checker. This repeats the round-1
declaration-pilot ownership problem: making receipt metadata independent of
observation exposes inconsistent fixture ownership. Production entry points
already share the registry. Before changing the fixtures, the adapter-call-site
audit confirms these are the two remaining independent-table cases. Reuse the
compilation's table and imported value identities in that shared test helper;
do not permit cross-registry fallback in the implementation.

## CB6 external review, round 4 — diagnosis before fixes

Claude finds the two adapter-fixture failures at `ab68362d` and a new notation
regression. The fixture correction `bcbf6849` is now on the PR branch; its full
run passes all 1,317 tests and all 3,857 canonical checks. The compiler code is
unchanged from the reviewed commit. The earlier full log remains a failed run.

The product finding repeats identity versus lexical visibility across a new
boundary: a notation body has its own source names but inherits the caller's
proof context. Comparing its operand labels to caller-local labels deletes
unrelated evidence. An independent extension of the review's probe, giving the
rule's inner lambda an explicit result type, reproduces the same regression for
ordinary binders inside the rule. An operand-only exception would miss that
case. Dimension binders also shadow and cannot be excluded just because they
lack source-local metadata.

The shared abstraction must distinguish lexical local definitions from the
definitions inherited as implicit proof evidence when entering a foreign rule
body. Preserve those inherited core terms independently of the rule's names;
start its lexical-local inventory empty. Nested rules inherit the evidence,
and lazy operands retain their original caller scope. Keep evidence untyped
until the existing search boundary so entering a lazy rule adds no inference,
fuel charge or eager operand evaluation. Use one definition enumeration for
both tactic search and generated obligations. Refine inherited definitions at
the same branch/face transitions as the other proof context, and include them
in isolated copying and inert replay descriptions. This needs one list of core
terms in the existing Scope, not another resolver, identity registry, label
blacklist, or new namespace framework.

The correction follows that boundary with one inherited-definition list on
Scope and one enumeration shared by both proof-search consumers. Rule entry
captures definitions without inference; refinement, faces, isolated copying and
replay descriptions preserve them. The 20-test notation suite passes, including
eight new source/query controls for operands, ordinary rule binders, model
openings, nested rules, lazy operands, missing evidence and caller shadowing.
Both elaborated instances of the inner lambda support queries and scratch
history. Native checks also validate inherited terms after refinement and faces.

Fixture debugging did not justify compiler changes: a direct-call opening was
invalid syntax, the lambda has two valid elaborated instances, and retaining the
whole quotient-library fixture caused an aggregate test-process heap failure.
A minimal quotient declaration and immediate program/session disposal keep the
complete notation suite within the existing limits. The unchanged heavy library
test also passes alone. Full gates and focused external round 5 remain pending.


## CB6 external review, round 5 — diagnosis before fixes

Claude finds no product issues in `3b9a0845`, passes 189 targeted tests and
runs nine independent probes against both earlier revisions. It verifies
source/query and collection parity, every reproduced collision, caller-shadowing
refusals, inner-body scratch history, operator sections and branch refinement.
A bounded 120-application comparison takes about 2.1 seconds at both revisions.
The shared list/enumeration/entry transition is judged minimal.

Its sole low-severity finding is the failed inspector browser log: the shared
`inspected()` predicate dereferences static markup while navigation is replacing
the document. An unchanged rerun had already passed, but that log was not named
in the original review brief. Preserve both logs. This is an asynchronous test
boundary, not another identity/visibility problem. Make the shared wait predicate
tolerate absent elements, as the neighboring workbench predicate already does;
then run that browser suite alone. Add no delay, retry policy or navigation-code
change. Full compiler gates remain valid on the unchanged product code. Focused
round 6 should verify this test-only correction and the exact terminal evidence,
without reopening the product audit.


Round 6 is clean on `fbd68711`, closing the inspector gate finding. Product code
remains `3b9a0845`. The user then requests an inspector-context REPL entry point;
that additional CB6 behavior remains pending before marking #239 ready.

## Inspector entry request — diagnosis before implementation

The inspector currently exposes a checked judgement without its replay scope.
Source-line buttons cannot establish which elaborated occurrence produced that
judgement, and a binder's introduction context can differ from a later use.
Connect the existing reference observation to an exact scope point at production,
including binder introductions, and transport its ID with the local inspection.
Use the existing replay callback, attempt ownership, worker index and console.
Do not reconstruct scope identity from label equality or nearest source ranges.
Keep these inspection points out of generic line pickers to avoid duplicate
choices there. Queries at an inspector entry may open its one exact instance.

Collection remains optional: the inspector button can request a check with scopes
on the unchanged source, preserve the inspected occurrence, and open its newly
recorded point. An edit, changed selection or compiler replacement must prevent a
late request from opening the old context. Embedded inspectors can reuse the same
console and on-demand collection rather than a separate query path. Verify the
reported Tree induction hypothesis, refined instances, source/query agreement,
no-collection entry and stale navigation. Extra observation points must preserve
source behavior and stay within existing resource limits.

The first implementation made every reference observation a new replay point.
Testing found two symptoms of the same design problem: optional reference
records shifted semantic scope IDs, and redundant snapshots exhausted the default
heap on the existing large notation fixture. Reference display events should
consume semantic entry points, not define them. The final wiring looks up the
actual Scope object in the active elaboration stack; binder introductions alone
add a semantic entry after binding. The stack is unwound synchronously and no
live scope enters a persisted description. Existing reference-on/off identity,
historical-notation, and large notation tests now pass without changing their
assertions or resource limits. Introduction/use and imported `ih` probes pass.

The combined notation suite still exposed excessive retention with the added
binder entries: each lexical frame copied receipts for all imported core values.
Share those immutable binding receipts, while rebuilding lazy operand and mutable
permission descriptions. A cache hit charges the same construction visits as a
cold receipt; the existing per-environment graph budget is unchanged. This fixes
the retained representation rather than adding a collection cutoff, raising a
limit, or weakening the large-fixture test. Replayed descriptions must still
match exactly. Binder entry follows model-evidence registration, so it denotes
the completed introduction transition.

The existing inspector browser gate caught a completion-path regression: returning
the check result for on-demand entry skipped the trailing status refresh when a
check did not render a kernel inspection. Move that refresh into the existing
`finally`, alongside the checking indicator. Every completed check now updates
controls regardless of its return path. Preserve the failing browser log; rerun
the gate on the corrected UI rather than adding a special generated-view fix.

## CB6 external review, round 7 — diagnosis before fixes

Claude finds one gate failure on `d48fa919`: the new inspector-unavailable message
was not registered. Use the existing diagnostic catalogue tool; this requires no
new abstraction. Its scope/cache/lifecycle audit otherwise passes, and it judges
the implementation proportionate. Five library probes link 11,321 of 11,322 local
views to available points; every linked entry appears in its module's index.

Two observations deserve completion before the final round. Splitting binding
snapshots preserved the aggregate visit limit but made the text cap per receipt.
Preserve both aggregate limits when sharing descriptions, counting cached text
alongside cached visits. This is representation accounting, not a reason to raise
limits or add a separate budget service. The unlinked quotient view is an
automatically checked coherence clause in its own observation attempt. Its entry
must be recorded at that semantic clause boundary, as binder entries are recorded
at introduction; optional reference events still only consume existing points.
Do not weaken exact Scope matching or choose a nearby point. Verify generated
clause queries, observation parity and warm/cold text exhaustion before round 8.


Round 8 is clean on `cb1cdc2c`. Claude independently verifies text cost against
7,108 distinct receipts, cold/warm refusal, generated clause goals and exact
locals, successful recovery attempt ownership, and reference-collection parity.
The coherence entry may parent inner proof points; its breadcrumb correctly
represents that enclosing goal. No new registry or budget service is needed.
Final gates on the same clean revision pass 1,332 tests, all 3,857 corpus checks,
both browser suites and all four production mutation kills. CB6 review stops
clean at eight rounds. CB7 retirement/release follows; after CB7, the user's
requested separate cleanup audits the entire CB0–CB7 stack.

## CB7 external review, round 1 — diagnosis before fixes

Claude verifies the production retirement, preserved semantic controls, twelve
mutation kills and release gates at `0c27548a`. Its three findings repeat two
existing roots. Removing the ordinary-module pilot left a module-wide adapter
option that bypasses retained-declaration admission. Delete that unused option
and its fallbacks: each retained declaration supplies its adapter at admission.
No replacement entry abstraction or test framework is needed.

The measurement tool also owns objects whose lifetime extends past the compiler's
disposal. The exact sampling-path probe shows serialization retains the scope map
through the first GC; yielding one event-loop turn did not fix it. An additional
turn/GC or omitting serialization releases it. Correct the interpretation rather
than adding GC machinery: the reported disposal sample includes measurement-owned
graphs and is not release proof. Check-time and pre-serialization retained-memory
measurements remain valid. Finally, one algebra peak-RSS sample exceeds the
proposed allowance (338.2 versus 334.9 MiB), while retained heap is unchanged.
Record this exception explicitly; do not report all allowances as satisfied or
rerun until a favorable sample appears. These evidence corrections need no
compiler resource-limit change.

Round 2 is clean at `32bda0ee`. Claude reproduces refusal of the removed bypass,
checks all 18 queue callers against the 137 passing focused tests, and verifies
the committed reports byte-for-byte and numerically. No additional code change
is needed. The final wording distinguishes retained heap growth from absolute
heap readings. CB7 is complete; the separate full-stack cleanup follows.
